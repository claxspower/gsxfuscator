-- obfuscate.lua -- layer 12 assembly: the whole pipeline behind one call.
--
--   Obfuscate.run(source, opts) -> result
--
-- Used by the CLI (v2/obfuscator.lua), the auto-fix runner and the browser
-- driver. The default preset is `strong`: every layer, self-modifying
-- bytecode, anti-debug and the integrity runtime.
--
-- Pipeline order is fixed by the architecture: M1 parse, M2 scope/rename,
-- M5 constants, M3 flatten, M4 opaque, M6 strings, M7 compiler,
-- M8 randomize, M10 block store, M9 pack, M8 emit, M11/M12 prologues.
local Parser = require("src.parser")
local Ast = require("src.ast")
local Scope = require("src.scope")
local Consts = require("src.consts")
local Flatten = require("src.flatten")
local Opaque = require("src.opaque")
local Strings = require("src.strings")
local Compiler = require("src.compiler")
local VMGen = require("src.vmgen")
local Selfmod = require("src.selfmod")
local Bytecode = require("src.bytecode")
local Entropy = require("src.entropy")

local Obfuscate = {}

Obfuscate.PRESETS = {
  strong = {
    decoys = 896, selfmod = true, antidebug = true, integrity = true,
    flatten = true, opaque = true, schemes = 6,
    flattenMinIfs = 0, flattenHard = true, flattenLoops = false,
    opaqueLoops = false,
  },
  normal = {
    decoys = 448, selfmod = false, antidebug = true, integrity = true,
    flatten = true, opaque = true, schemes = 6,
    flattenMinIfs = 1, flattenHard = true, flattenLoops = false,
    opaqueLoops = false,
  },
  fast = {
    decoys = 160, selfmod = false, antidebug = false, integrity = true,
    flatten = false, opaque = false, schemes = 2,
  },
}

Obfuscate.DEFAULT_PRESET = "strong"

local function mix(seed, tag)
  return (seed + tag * 2654435761) % 4294967296
end

-- Strings.run takes a list of scheme names; the presets speak in counts so a
-- single number can pick the strength of the string layer.
local SCHEME_NAMES = { "xor", "b64", "huff", "feistel", "lookup", "chain" }

local function schemeList(value)
  if type(value) == "table" then return value end
  local count = math.floor(tonumber(value) or #SCHEME_NAMES)
  local list = {}
  for i = 1, math.min(count, #SCHEME_NAMES) do list[i] = SCHEME_NAMES[i] end
  return list
end


local function parseErrors(errors)
  local list = {}
  for i = 1, #(errors or {}) do
    local e = errors[i]
    list[#list + 1] = {
      line = e.line or 0,
      col = e.col or 0,
      msg = tostring(e.msg or e),
    }
  end
  return list
end

local function fail(stage, errors, seed, preset)
  return {
    ok = false,
    stage = stage,
    errors = parseErrors(errors),
    seed = seed,
    preset = preset,
    code = nil,
    stats = nil,
  }
end

-- opts:
--   preset    "strong" (default) | "normal" | "fast"
--   seed      integer 0..2^32-1; omitted means a fresh one per run
--   selfmod / antidebug / integrity / flatten / opaque / decoys
--             explicit overrides, mainly for the auto-fix ladder
function Obfuscate.run(source, opts)
  opts = opts or {}
  local presetName = opts.preset or Obfuscate.DEFAULT_PRESET
  local preset = Obfuscate.PRESETS[presetName]
  if not preset then
    error("obfuscate: unknown preset '" .. tostring(presetName) .. "'", 0)
  end
  local seed = opts.seed
  if seed == nil then seed = Entropy.seed() end
  seed = math.floor(tonumber(seed) or 0) % 4294967296
  if seed < 0 then seed = seed + 4294967296 end

  if type(source) ~= "string" or source == "" then
    return fail("input", { { line = 0, col = 0, msg = "empty source" } },
      seed, presetName)
  end

  local ast, parseErrs = Parser.parse(source, opts.filename or "input.lua")
  if not ast or #parseErrs > 0 then return fail("parse", parseErrs, seed, presetName) end
  ast = Ast.normalize(ast)
  if not ast then
    return fail("parse", { { line = 0, col = 0, msg = "empty AST" } }, seed,
      presetName)
  end

  local scope = Scope.analyze(ast, { seed = mix(seed, 2) })
  if #scope.errors > 0 then return fail("scope", scope.errors, seed, presetName) end
  Scope.apply(scope)

  local useFlatten = opts.flatten
  if useFlatten == nil then useFlatten = preset.flatten end
  local useOpaque = opts.opaque
  if useOpaque == nil then useOpaque = preset.opaque end
  local decoys = opts.decoys
  if decoys == nil then decoys = preset.decoys end
  local schemes = opts.schemes
  if schemes == nil then schemes = preset.schemes end

  -- Every alias key costs a whole generated handler, so the fixed table
  -- dominates the artifact for small scripts: a 3 KB script used to ship the
  -- same 1,500-function runtime a 300 KB script gets. Scale the redundancy with
  -- source size, and explicit caller overrides win. Every level keeps alias
  -- layouts, operand masks and the per-prototype keystream fully randomized;
  -- the ladder below is the post-hardening one (more aliases and decoys per
  -- size band than the previous table).
  local encodings = opts.encodings
  if encodings == nil then
    if #source <= 4096 then
      encodings = 5
      decoys = math.min(decoys, 176)
    elseif #source <= 16384 then
      encodings = 7
      decoys = math.min(decoys, 224)
    elseif #source <= 65536 then
      encodings = 9
      decoys = math.min(decoys, 288)
    elseif #source <= 262144 then
      encodings = 13
      decoys = math.min(decoys, 512)
    else
      encodings = 18
      decoys = math.min(decoys, 640)
    end
  end

  -- Opt-in size/latency budget. This reduces redundant VM aliases and decoy
  -- handlers, not the intrinsic bytecode format or integrity/anti-debug layers.
  -- Compact is the default to avoid multi-megabyte handler/decoy bloat.
  local vmSize = opts.vmSize or "compact"
  if vmSize ~= "standard" and vmSize ~= "compact" then
    return fail("input", {{ msg = "vmSize must be standard or compact" }},
      seed, presetName)
  end
  if vmSize == "compact" then
    encodings = math.min(encodings, 2)
    decoys = math.min(decoys, 24)
  end

  Consts.run(ast, { seed = mix(seed, 5) })
  if useFlatten then
    local hard = preset.flattenHard
    Flatten.run(ast, {
      seed = mix(seed, 3),
      minIfs = preset.flattenMinIfs or 1,
      shapes = hard or nil,
      split = hard or nil,
      decoys = hard or nil,
      stateOffset = hard or nil,
      flattenLoops = preset.flattenLoops ~= false,
    })
  end
  if useOpaque then
    Opaque.run(ast, { seed = mix(seed, 4), prob = 0.6,
      loopConditions = preset.opaqueLoops ~= false })
  end
  Strings.run(ast, { seed = mix(seed, 6), schemes = schemeList(schemes) })

  local compiled = Compiler.compile(ast, {})
  if #compiled.errors > 0 then
    return fail("compile", compiled.errors, seed, presetName)
  end

  local plan = VMGen.randomize(compiled, {
    seed = seed, decoys = decoys, encodings = encodings,
    pruneHandlers = (vmSize == "compact" and opts.pruneHandlers ~= false),
    adaptiveAliases = (vmSize == "compact" and opts.adaptiveAliases ~= false) })
  local useSelfmod = opts.selfmod
  if useSelfmod == nil then useSelfmod = preset.selfmod end
  if useSelfmod then Selfmod.apply(plan, { seed = seed }) end
  local payload = Bytecode.pack(plan, { seed = seed })
  -- [VM9-AUDIT] Reject broken VM9 serialization before SEAL4 wrapping.
  -- Verification uses the actual packed bytes, not only pre-pack AST metadata.
  local audit, auditErr = Bytecode.auditPacked(plan, payload)
  if not audit then
    return fail("bytecode-integrity", { { msg = auditErr } }, seed, presetName)
  end

  local useAntidebug = opts.antidebug
  if useAntidebug == nil then useAntidebug = preset.antidebug end
  local useIntegrity = opts.integrity
  if useIntegrity == nil then useIntegrity = preset.integrity end

  local emitOpts = {
    payload = payload,
    antidebug = useAntidebug and true or nil,
    integrity = useIntegrity and true or nil,
    executor = opts.executor and true or nil,
    gethui = opts.gethui and true or nil,
    antiwebhook = opts.antiwebhook and true or nil,
    -- Compact output omits nonessential decoy environment reads. They are
    -- additional intercepted strings in an instrumented host, not security.
    -- Standard VM retains the legacy decoy mode for regression compatibility.
    envChaff = (vmSize == "standard"),
    compactNames = (vmSize == "compact"),
    -- Host API fingerprinting differs across Roblox/Luau versions and may
    -- trigger false positives; opt-in explicitly only for diagnostic builds.
    strictHostChecks = opts.strictHostChecks == true,
  }
  local code, stats = VMGen.emit(plan, emitOpts)
  stats.vmAudit = audit

  return {
    ok = true,
    stage = "done",
    code = code,
    stats = stats,
    vmLayerVerified = true,
    vmSize = vmSize,
    seed = seed,
    preset = presetName,
    errors = {},
    integrity = useIntegrity and true or false,
    selfmod = useSelfmod and true or false,
    antidebug = useAntidebug and true or false,
    executor = opts.executor and true or false,
    gethui = opts.gethui and true or false,
    antiwebhook = opts.antiwebhook and true or false,
    settings = {
      flatten = useFlatten and true or false,
      opaque = useOpaque and true or false,
      decoys = decoys,
      schemes = schemes,
      vmSize = vmSize,
      strictHostChecks = opts.strictHostChecks == true,
    },
  }
end

return Obfuscate
