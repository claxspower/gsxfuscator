-- cli.lua -- command line front end for the layer 12 pipeline.
--
--   lua v2/obfuscator.lua input.lua
--   lua v2/obfuscator.lua input.lua out.lua --preset strong --seed 123
--   lua v2/obfuscator.lua input.lua --auto-fix
--
-- The wrapper (v2/obfuscator.lua) only sets package.path and calls Cli.main,
-- so this module is directly testable. `sink` is injectable:
--   { out = function(text), err = function(text) }
local Obfuscate = require("src.obfuscate")
local Autofix = require("src.autofix")
local Artifact = require("src.artifact")
local Release = require("src.release")

local Cli = {}

Cli.EXIT_OK = 0
Cli.EXIT_USAGE = 1
Cli.EXIT_FAILED = 2
Cli.EXIT_VERIFY = 3

Cli.USAGE = table.concat({
  "usage: lua v2/obfuscator.lua <input.lua> [output.lua] [options]",
  "",
  "  --preset NAME     strong (default) | normal | fast",
  "  --seed N          0..4294967295; omitted means a fresh seed",
  "  --run             verify the output against the source once",
  "  --no-seal         emit direct VM (opt-in; no outer runtime load/loadstring)",
  "  --seal            sealed wrapper (default; dynamic load at runtime)",
  "  Fast Load is always enabled for sealed delivery",
  "  --coroutine-wrap  opt-in; changes coroutine semantics (not dump-proof)",
  "  --version         print the generator version and format identifiers",
  "  --vm-size MODE    compact (default) | standard (larger runtime)",
  "  --seal-compression MODE  auto (default) | raw (skip LZSS) | lzss",
  "  --seal-block-size N     raw bytes per seal block (1..8388607)",
  "  --fragment-size N      outer transport fragment length (128..16384)",
  "  --watermark ID         embedded provenance label (ASCII, max 128)",
  "  --strict-verify   fail instead of warning if verification is inconclusive",
  "  --auto-fix        verify and retry with safer presets on failure",
  "  --stats           print the full layer statistics",
  "  --max-steps N     sandbox instruction budget (default " .. Autofix.DEFAULTS.maxSteps .. ")",
  "  --seconds N       sandbox CPU time budget (default " .. Autofix.DEFAULTS.seconds .. ")",
  "  -o PATH           output path; used before the positional output",
  "  -h, --help        show this help",
  "",
  "exit codes: 0 ok, 1 usage/io, 2 obfuscation failed, 3 verification failed",
}, "\n")

local function validPreset(name)
  return Obfuscate.PRESETS[name] ~= nil
end

local function defaultOutput(input)
  local base = input:gsub("%.lua$", "")
  return base .. ".obf.lua"
end

local function parseSeed(text)
  if type(text) ~= "string" or not text:match("^%d+$") then return nil end
  local n = tonumber(text)
  if not n or n < 0 or n > 4294967295 then return nil end
  return math.floor(n)
end

function Cli.parse(argv)
  local opts = {
    preset = Obfuscate.DEFAULT_PRESET,
    run = false,
    autofix = false,
    stats = false,
    noSeal = false,
    strictVerify = false,
  }
  local positional = {}
  local i = 1
  while i <= #argv do
    local a = argv[i]
    local key, value = a:match("^%-%-([%w%-]+)=(.*)$")
    if a == "-h" or a == "--help" then
      opts.help = true
    elseif a == "--version" then
      opts.version = true
    elseif a == "--run" then
      opts.run = true
    elseif a == "--auto-fix" or a == "--autofix" then
      opts.autofix = true
    elseif a == "--stats" then
      opts.stats = true
    elseif a == "--strict-verify" then
      opts.strictVerify = true
    elseif a == "--no-seal" or a == "--direct-vm" then
      opts.noSeal = true
    elseif a == "--seal" then
      opts.noSeal = false
    elseif a == "--fast-load" then
      opts.fastLoad = true
    elseif a == "--no-fast-load" then
      return nil, "Fast Load is always enabled (remove --no-fast-load)"
    elseif a == "--coroutine-wrap" then
      opts.coroutineWrapper = true
    elseif key then
      if key == "preset" then opts.preset = value
      elseif key == "seed" then opts.seed = value
      elseif key == "out" then opts.output = value
      elseif key == "max-steps" then opts.maxSteps = value
      elseif key == "seconds" then opts.seconds = value
      elseif key == "vm-size" then opts.vmSize = value
      elseif key == "seal-compression" then opts.sealCompression = value
      elseif key == "seal-block-size" then opts.sealBlockSize = value
      elseif key == "fragment-size" then opts.fragmentSize = value
      elseif key == "watermark" then opts.watermark = value
      else return nil, "unknown option --" .. key end
    elseif a == "--preset" or a == "--seed" or a == "--out" or
      a == "--max-steps" or a == "--seconds" or
      a == "--seal-compression" or a == "--seal-block-size" or
      a == "--vm-size" or a == "--fragment-size" or a == "--watermark" then
      i = i + 1
      if i > #argv then return nil, "missing value for " .. a end
      local v = argv[i]
      if a == "--preset" then opts.preset = v
      elseif a == "--seed" then opts.seed = v
      elseif a == "--out" then opts.output = v
      elseif a == "--max-steps" then opts.maxSteps = v
      elseif a == "--vm-size" then opts.vmSize = v
      elseif a == "--seal-compression" then opts.sealCompression = v
      elseif a == "--seal-block-size" then opts.sealBlockSize = v
      elseif a == "--fragment-size" then opts.fragmentSize = v
      elseif a == "--watermark" then opts.watermark = v
      else opts.seconds = v end
    elseif a == "-o" then
      i = i + 1
      if i > #argv then return nil, "missing value for -o" end
      opts.output = argv[i]
    elseif a:sub(1, 1) == "-" and a ~= "-" then
      return nil, "unknown option " .. a
    else
      positional[#positional + 1] = a
    end
    i = i + 1
  end

  if opts.help or opts.version then return opts end
  if not validPreset(opts.preset) then
    return nil, "unknown preset '" .. tostring(opts.preset) .. "'"
  end
  if opts.seed ~= nil then
    opts.seedNumber = parseSeed(opts.seed)
    if opts.seedNumber == nil then
      return nil, "seed must be an integer in 0..4294967295"
    end
  end
  if opts.maxSteps ~= nil then
    opts.maxSteps = parseSeed(opts.maxSteps)
    if opts.maxSteps == nil then return nil, "invalid --max-steps" end
  end
  if opts.seconds ~= nil then
    local n = tonumber(opts.seconds)
    if not n or n < 0 then return nil, "invalid --seconds" end
    opts.seconds = n
  end
  if opts.vmSize and opts.vmSize ~= "standard" and opts.vmSize ~= "compact" then
    return nil, "--vm-size must be standard or compact"
  end
  if opts.sealCompression and opts.sealCompression ~= "auto" and
      opts.sealCompression ~= "raw" and opts.sealCompression ~= "lzss" then
    return nil, "--seal-compression must be auto, raw or lzss"
  end
  if opts.sealBlockSize ~= nil then
    local n = parseSeed(opts.sealBlockSize)
    if not n or n < 1 or n >= 8388608 then
      return nil, "--seal-block-size must be 1..8388607"
    end
    opts.sealBlockSize = n
  end
  if opts.fragmentSize ~= nil then
    local n=tonumber(opts.fragmentSize)
    if not n or n~=math.floor(n) or n<128 or n>16384 then
      return nil,"--fragment-size must be 128..16384"
    end
    opts.fragmentSize=n
  end
  if opts.watermark~=nil and (#opts.watermark>128 or opts.watermark:find("[^%w%._%-]")) then
    return nil,"--watermark must use ASCII letters, digits, dot, underscore or hyphen"
  end
  if opts.strictVerify then opts.run = true end
  if #positional == 0 then return nil, "missing input file" end
  if #positional > 2 then return nil, "too many arguments" end
  opts.input = positional[1]
  opts.output = opts.output or positional[2] or defaultOutput(opts.input)
  return opts
end

local function human(bytes)
  if bytes >= 1048576 then
    return string.format("%.1f MB", bytes / 1048576)
  end
  if bytes >= 1024 then
    return string.format("%.1f KB", bytes / 1024)
  end
  return tostring(bytes) .. " B"
end

local function readFile(path)
  local f, err = io.open(path, "rb")
  if not f then return nil, err end
  local data = f:read("*a")
  f:close()
  return data
end

-- Write alongside the target and rename only after a successful close.
-- On filesystems where rename cannot replace an existing destination (notably
-- some Windows configurations), report failure instead of deleting old output.
local writeCounter = 0
local function writeFile(path, data)
  writeCounter = writeCounter + 1
  local temp = path .. ".gsx-tmp-" .. tostring(writeCounter) .. "-" ..
    tostring(math.floor(os.clock() * 1000000))
  local f, err = io.open(temp, "wb")
  if not f then return nil, err end
  local ok, writeErr = f:write(data)
  local closed, closeErr = f:close()
  if not ok or not closed then
    os.remove(temp)
    return nil, writeErr or closeErr
  end
  local renamed, renameErr = os.rename(temp, path)
  if not renamed then
    os.remove(temp)
    return nil, renameErr
  end
  return true
end

local buildArtifact = Artifact.build

local function formatErrors(errors)
  local lines = {}
  for i = 1, #(errors or {}) do
    local e = errors[i]
    lines[#lines + 1] = string.format("%d:%d: %s", e.line or 0, e.col or 0,
      e.msg or "unknown error")
  end
  return lines
end

local function describe(result)
  local stats = result.stats or {}
  local parts = {
    result.preset,
    "seed " .. tostring(result.seed),
    result.deliveryMode or "sealed",
    human(stats.bytes or 0),
    "proto " .. tostring(stats.protos or 0),
    "ops " .. tostring(stats.opcodes or 0) .. "+" .. tostring(stats.decoys or 0),
  }
  if stats.integrity then
    parts[#parts + 1] = "int " .. tostring(stats.integrityPeriod)
  end
  if stats.selfmod then
    parts[#parts + 1] = "sm " .. tostring(stats.selfmodProtos) .. "x" ..
      tostring(stats.selfmodBlocks)
  end
  if stats.antidebug then
    parts[#parts + 1] = "ad " .. tostring(stats.antidebugProbes)
  end
  return table.concat(parts, "  ")
end

local function attemptLine(attempt)
  local base = string.format("attempt %d/%s", attempt.index, attempt.label)
  if not attempt.ok then
    return base .. ": " .. tostring(attempt.reason or attempt.stage)
  end
  if attempt.match then return base .. ": ok" end
  return base .. ": " .. tostring(attempt.reason or "mismatch")
end

local function sourceRatio(inputBytes, outputBytes)
  if inputBytes <= 0 then return "0x" end
  return string.format("%.1fx", outputBytes / inputBytes)
end

function Cli.main(argv, sink)
  sink = sink or {
    out = function(text) io.write(text) end,
    err = function(text) io.stderr:write(text) end,
  }
  local opts, parseErr = Cli.parse(argv)
  if not opts then
    sink.err("obfuscator: " .. parseErr .. "\n\n" .. Cli.USAGE .. "\n")
    return Cli.EXIT_USAGE
  end
  if opts.help then
    sink.out(Cli.USAGE .. "\n")
    return Cli.EXIT_OK
  end
  if opts.version then
    sink.out("GsXFuscator " .. Release.displayVersion .. " (" .. Release.version .. ") " ..
      Release.vmFormat .. "/" .. Release.sealFormat .. "\n")
    return Cli.EXIT_OK
  end

  local source, readErr = readFile(opts.input)
  if not source then
    sink.err("obfuscator: cannot read " .. opts.input .. ": " ..
      tostring(readErr) .. "\n")
    return Cli.EXIT_USAGE
  end

  -- Never silently replace the input with its obfuscated form. Direct name
  -- equality covers the most common accident; symbolic links and alternative
  -- paths still require separate care from the caller.
  if opts.output == opts.input then
    sink.err("obfuscator: input and output paths must differ\n")
    return Cli.EXIT_USAGE
  end
  local report = opts.output == "-" and sink.err or sink.out
  local result
  if opts.autofix then
    result = Autofix.run(source, {
      engine = buildArtifact,
      preset = opts.preset,
      seed = opts.seedNumber,
      noSeal = opts.noSeal,
      coroutineWrapper = opts.coroutineWrapper,
      sealCompression = opts.sealCompression,
      vmSize = opts.vmSize,
      sealBlockSize = opts.sealBlockSize,
      fragmentSize = opts.fragmentSize,
      fastLoad = true,
      watermark = opts.watermark,
      maxSteps = opts.maxSteps,
      seconds = opts.seconds,
    })
    for i = 1, #result.attempts do
      report(attemptLine(result.attempts[i]) .. "\n")
    end
    if not result.ok then
      local msg = result.stage == "exhausted"
        and "no preset produced a matching output"
        or ("failed at " .. tostring(result.stage))
      sink.err("obfuscator: auto-fix: " .. msg .. "\n")
      local lines = formatErrors(result.errors)
      for i = 1, #lines do sink.err("  " .. lines[i] .. "\n") end
      return (result.stage == "exhausted" or result.stage == "integrity")
        and Cli.EXIT_VERIFY or Cli.EXIT_FAILED
    end
    if not result.verified then
      if opts.strictVerify then
        sink.err("obfuscator: verification inconclusive: " ..
          tostring(result.note) .. "\n")
        return Cli.EXIT_VERIFY
      end
      sink.err("obfuscator: warning: " .. tostring(result.note) ..
        "; output not verified\n")
    end
  else
    local t0 = os.clock()
    result = buildArtifact(source, {
      preset = opts.preset,
      seed = opts.seedNumber,
      noSeal = opts.noSeal,
      coroutineWrapper = opts.coroutineWrapper,
      sealCompression = opts.sealCompression,
      vmSize = opts.vmSize,
      sealBlockSize = opts.sealBlockSize,
      fragmentSize = opts.fragmentSize,
      fastLoad = true,
      watermark = opts.watermark,
    })
    result.ms = math.floor((os.clock() - t0) * 1000 + 0.5)
    if not result.ok then
      sink.err("obfuscator: " .. tostring(result.stage) .. " error\n")
      local lines = formatErrors(result.errors)
      for i = 1, #lines do sink.err("  " .. lines[i] .. "\n") end
      return Cli.EXIT_FAILED
    end
    if opts.run then
      local check = Autofix.verify(source, result.code, {
        maxSteps = opts.maxSteps,
        seconds = opts.seconds,
      })
      if Autofix.isIntegrityError(check.reason) then
        sink.err(check.reason .. "\n")
        return Cli.EXIT_VERIFY
      elseif check.candidate.stage == "load" then
        sink.err("obfuscator: verification failed: output does not load\n")
        return Cli.EXIT_VERIFY
      elseif not check.verified then
        if opts.strictVerify then
          sink.err("obfuscator: verification inconclusive: " ..
            tostring(check.note) .. "\n")
          return Cli.EXIT_VERIFY
        end
        sink.err("obfuscator: warning: " .. tostring(check.note) ..
          "; output not verified\n")
      elseif check.ok then
        report("verified: output matches source\n")
      else
        sink.err("obfuscator: verification failed: " ..
          tostring(check.reason) .. "\n")
        return Cli.EXIT_VERIFY
      end
    end
  end

  local stats = result.stats or {}
  local outputBytes = #result.code
  if opts.output == "-" then
    sink.out(result.code)
  else
    local wrote, writeErr = writeFile(opts.output, result.code)
    if not wrote then
      sink.err("obfuscator: cannot write " .. opts.output .. ": " ..
        tostring(writeErr) .. "\n")
      return Cli.EXIT_USAGE
    end
  end

  report(string.format("%s -> %s\n", opts.input, opts.output))
  report(string.format("%s  %s (%s)  %d ms\n", describe(result),
    human(outputBytes), sourceRatio(#source, outputBytes), result.ms or 0))
  if opts.stats then
    local rows = {
      { "payload", stats.payloadBytes },
      { "plain", stats.plainBytes },
      { "instructions", stats.instructions },
      { "selfmodBytes", stats.selfmodBytes },
      { "antidebugMask", stats.antidebugMask },
      { "integrityPeriod", stats.integrityPeriod },
      { "integrityCanaryLen", stats.integrityCanaryLen },
      { "integrityProbe", stats.integrityProbe },
    }
    for i = 1, #rows do
      if rows[i][2] ~= nil then
        report(string.format("  %-20s %s\n", rows[i][1],
          tostring(rows[i][2])))
      end
    end
  end
  return Cli.EXIT_OK
end

return Cli
