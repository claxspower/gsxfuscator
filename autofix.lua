-- Build and retry a verified artifact for the local CLI.
local Obfuscate = require("src.obfuscate")
local Autofix = {}
for k, v in pairs(require("src.verifier")) do Autofix[k] = v end
local aborted = Autofix.aborted
local OUTPUT_LIMIT_ERROR = Autofix.outputLimitError

Autofix.GOLDEN = 2654435761 -- 0x9E3779B1, below 2^32 so 5.1 is exact

-- Decreasing risk. `minimal` drops every optional layer except encryption and
-- the runtime integrity check, which is what finally ships.
Autofix.LADDER = {
  { label = "strong", preset = "strong" },
  { label = "normal", preset = "normal" },
  { label = "fast", preset = "fast" },
  {
    label = "minimal", preset = "fast",
    integrity = false, decoys = 32, schemes = 1,
  },
}

-- Parse and scope failures do not depend on the preset, so escalating cannot
-- help. Compile failures can come from flatten/opaque, so they retry.
local FATAL = { input = true, parse = true, scope = true }

-- ------------------------------------------------------------------- ladder
local function strategyArgs(strategy, seed, opts)
  local args = { preset = strategy.preset, seed = seed }
  local keys = { "selfmod", "antidebug", "integrity", "flatten", "opaque",
    "decoys", "schemes" }
  for i = 1, #keys do args[keys[i]] = strategy[keys[i]] end
  -- Orthogonal protections survive every ladder rung: a repaired build must
  -- not silently lose gethui/anti-webhook or the executor gate.
  if opts then
    args.executor = opts.executor
    args.gethui = opts.gethui
    args.antiwebhook = opts.antiwebhook
    args.noSeal = opts.noSeal
    args.vmSize = opts.vmSize
    args.sealCompression = opts.sealCompression
    args.sealBlockSize = opts.sealBlockSize
  end
  return args
end

local function seedAt(base, index)
  if base == nil then return nil end
  return (base + (index - 1) * Autofix.GOLDEN) % 4294967296
end

local function ladderFor(opts)
  if opts.ladder then return opts.ladder end
  local start = opts.preset or Obfuscate.DEFAULT_PRESET
  local from = 1
  for i = 1, #Autofix.LADDER do
    if Autofix.LADDER[i].preset == start then
      from = i
      break
    end
  end
  local list = {}
  for i = from, #Autofix.LADDER do list[#list + 1] = Autofix.LADDER[i] end
  return list
end

local function settingsOf(result)
  local s = result.settings or {}
  s.preset = result.preset
  s.selfmod = result.selfmod
  s.antidebug = result.antidebug
  s.integrity = result.integrity
  return s
end

-- opts:
--   preset       start of the ladder (default strong)
--   seed         base seed; each attempt derives its own
--   maxSteps / seconds / compareReturns  forwarded to the sandbox
--   engine       function(source, opts) -> Obfuscate result (tests inject one)
--   verify       false disables the reference run entirely
function Autofix.run(source, opts)
  opts = opts or {}
  local started = os.clock()
  local reference
  if opts.verify ~= false then
    reference = Autofix.sandboxRun(source, opts)
  end
  local verifiable = reference ~= nil and reference.ok and
    not aborted(reference) and not reference.outputLimited
  local unverifiedNote
  if reference == nil then
    unverifiedNote = "verification disabled"
  elseif reference.stage == "load" then
    unverifiedNote = "source chunk does not load on this host"
  elseif not reference.ok and not aborted(reference) then
    unverifiedNote = "source raised a runtime error; verification inconclusive"
  elseif reference.outputLimited then
    unverifiedNote = OUTPUT_LIMIT_ERROR
  else
    unverifiedNote = "source did not finish within the sandbox budget"
  end
  local strategies = ladderFor(opts)
  local engine = opts.engine or Obfuscate.run
  local attempts = {}

  for i = 1, #strategies do
    local strategy = strategies[i]
    local args = strategyArgs(strategy, seedAt(opts.seed, i), opts)
    local t0 = os.clock()
    local result = engine(source, args)
    local ms = math.floor((os.clock() - t0) * 1000 + 0.5)
    local record = {
      index = i,
      label = strategy.label,
      preset = strategy.preset,
      seed = args.seed,
      stage = result.stage,
      ok = result.ok,
      ms = ms,
    }

    if not result.ok then
      record.reason = result.stage
      record.errors = result.errors
      attempts[#attempts + 1] = record
      if FATAL[result.stage] then
        return {
          ok = false, stage = result.stage, attempts = attempts,
          errors = result.errors, reference = reference,
          failedPreset = strategy.preset, seed = args.seed,
          ms = math.floor((os.clock() - started) * 1000 + 0.5),
        }
      end
    else
      local run = Autofix.sandboxRun(result.code, {
        maxSteps = opts.maxSteps,
        stepChunk = opts.stepChunk,
        seconds = opts.seconds,
      })
      record.run = run
      if not run.ok and Autofix.isIntegrityError(run.error) then
        local integrityError = run.error
        record.match, record.reason = false, integrityError
        attempts[#attempts + 1] = record
        return { ok = false, stage = "integrity", attempts = attempts,
          reference = reference, run = run, errors = { { msg = integrityError } },
          seed = args.seed, preset = strategy.preset }
      end
      -- A budget abort is not evidence the output is wrong, and a lower preset
      -- cannot make the same chunk cheaper. Keep the build, mark it unverified.
      local matched, reason, budgetLimited
      if verifiable then
        if aborted(run) then
          matched, reason, budgetLimited = false, "sandbox limit", true
        else
          matched, reason = Autofix.compare(reference, run, opts)
        end
      else
        matched, reason = run.stage ~= "load", run.stage == "load" and "load" or nil
      end
      record.match = matched
      record.reason = reason
      if matched or budgetLimited then
        attempts[#attempts + 1] = record
        local out = {
          ok = true,
          stage = (verifiable and not budgetLimited) and "done" or "unverified",
          code = result.code,
          deliveryMode = result.deliveryMode,
          stats = result.stats,
          seed = result.seed,
          preset = result.preset,
          attempts = attempts,
          reference = reference,
          run = run,
          verified = verifiable and not budgetLimited,
          note = run.outputLimited and OUTPUT_LIMIT_ERROR or budgetLimited and
            "sandbox budget exceeded on the obfuscated chunk" or
            (not verifiable and unverifiedNote or nil),
          ms = math.floor((os.clock() - started) * 1000 + 0.5),
        }
        local extra = settingsOf(result)
        out.selfmod = extra.selfmod
        out.antidebug = extra.antidebug
        out.integrity = extra.integrity
        out.settings = extra
        return out
      end
      attempts[#attempts + 1] = record
    end
  end

  return {
    ok = false,
    stage = "exhausted",
    attempts = attempts,
    reference = reference,
    errors = {},
    ms = math.floor((os.clock() - started) * 1000 + 0.5),
  }
end

return Autofix
