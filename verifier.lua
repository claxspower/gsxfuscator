-- Execution comparison shared by the browser worker and trusted CLI.
local unpackFn = table.unpack or unpack
local OUTPUT_LIMIT = 256 * 1024
local OUTPUT_LIMIT_ERROR = "autofix: captured output exceeds 256 KiB"

local Verifier = {}

Verifier.DEFAULTS = {
  maxSteps = 400000000,
  stepChunk = 1000000,
  seconds = 10,
  randomSeed = 1,
  time = 1700000000,
}

local function pack(...)
  return { n = select("#", ...), ... }
end

local function blocked(name)
  return function()
    error("autofix: " .. name .. " is disabled in the sandbox", 0)
  end
end

-- Embedded hosts (fengari-web) have no `io` library at all, so a missing
-- library copies to an empty table instead of raising.
local function copyTable(src)
  local out = {}
  if type(src) ~= "table" then return out end
  for k, v in pairs(src) do out[k] = v end
  return out
end

-- ------------------------------------------------------------- sandbox env
local function makeEnv(capture, opts, attach)
  local env = copyTable(_G)
  env._G = env
  env.arg = { [0] = "sandbox" }
  -- The verification harness is not a security boundary. Still, do not
  -- expose unnecessary filesystem/module-loader primitives to source chunks.
  env.require = blocked("require")
  env.package = nil
  env.dofile = blocked("dofile")
  env.loadfile = blocked("loadfile")
  env.module = blocked("module")
  env.collectgarbage = blocked("collectgarbage")
  env.ffi, env.jit = nil, nil
  -- Prevent ordinary library-table mutations from leaking across the two
  -- verification runs. These are shallow copies, not a full VM isolation.
  env.string = copyTable(string)
  env.table = copyTable(table)
  env.math = copyTable(math)
  env.utf8 = copyTable(utf8)
  env.bit32 = copyTable(bit32)

  local function verifiedLoad(src, chunkname, mode, requestedEnv)
    if type(src) ~= "string" then return nil, "verifier: only text chunks allowed" end
    if requestedEnv ~= nil and requestedEnv ~= env then
      return nil, "verifier: foreign load environment denied"
    end
    if type(mode) == "string" and mode:find("b", 1, true) then
      return nil, "verifier: bytecode loading denied"
    end
    local fn, err
    if type(setfenv) == "function" then
      fn, err = (loadstring or load)(src, chunkname)
      if fn then setfenv(fn, env) end
    else
      fn, err = load(src, chunkname, "t", env)
    end
    return fn, err
  end
  env.load, env.loadstring = verifiedLoad, verifiedLoad
  if type(getfenv) == "function" then
    env.getfenv = function() return env end
  end
  if type(setfenv) == "function" then
    env.setfenv = function(fn, requestedEnv)
      if requestedEnv ~= env then error("verifier: foreign setfenv denied", 0) end
      return setfenv(fn, env)
    end
  end

  local function checkSize(bytes)
    if capture.limited or bytes > OUTPUT_LIMIT - capture.bytes then
      capture.limited = true
      error(OUTPUT_LIMIT_ERROR, 0)
    end
  end

  local function emit(s)
    checkSize(#s)
    if #s > 0 then
      capture.bytes = capture.bytes + #s
      capture.parts[#capture.parts + 1] = s
    end
  end

  env.print = function(...)
    local t = {}
    local count = select("#", ...)
    local bytes = math.max(1, count) -- tabs between arguments and a newline
    checkSize(bytes)
    for i = 1, count do
      local value = tostring(select(i, ...))
      bytes = bytes + #value
      checkSize(bytes)
      t[i] = value
    end
    emit(table.concat(t, "\t") .. "\n")
  end

  local ioCopy = copyTable(io)
  ioCopy.write = function(...)
    for i = 1, select("#", ...) do emit(tostring(select(i, ...))) end
  end
  ioCopy.read = blocked("io.read")
  ioCopy.open = blocked("io.open")
  ioCopy.lines = blocked("io.lines")
  ioCopy.popen = blocked("io.popen")
  ioCopy.tmpfile = blocked("io.tmpfile")
  env.io = ioCopy

  local fixedTime = opts.time
  if fixedTime == nil then fixedTime = Verifier.DEFAULTS.time end
  local realDate = os.date
  local osCopy = copyTable(os)
  osCopy.time = function() return fixedTime end
  osCopy.date = function(fmt, t)
    if t == nil then t = fixedTime end
    return realDate(fmt, t)
  end
  local ticks = 0
  osCopy.clock = function()
    ticks = ticks + 1
    return (ticks - 1) * 0.001
  end
  osCopy.exit = blocked("os.exit")
  osCopy.execute = blocked("os.execute")
  osCopy.remove = blocked("os.remove")
  osCopy.rename = blocked("os.rename")
  osCopy.tmpname = blocked("os.tmpname")
  env.os = osCopy

  local seed = opts.randomSeed
  if seed == nil then seed = Verifier.DEFAULTS.randomSeed end
  if env.math and env.math.randomseed then
    pcall(env.math.randomseed, seed)
  end

  -- Fengari's floor returns the float subtype where PUC 5.3+ returns an
  -- integer, so `tostring(math.floor(3.0))` would be "3.0" there. The VM
  -- normalises decoded operands through floor, which would turn every integer
  -- register into a float and make a correct program print differently only
  -- inside this harness. Narrow the result back to an integer when possible.
  if env.math and env.math.floor then
    local mathCopy = copyTable(env.math)
    local realFloor, tointeger = mathCopy.floor, mathCopy.tointeger
    if tointeger then
      mathCopy.floor = function(x)
        local r = realFloor(x)
        local i = tointeger(r)
        if i ~= nil then return i end
        return r
      end
    end
    env.math = mathCopy
  end

  if coroutine then
    local coCopy = copyTable(coroutine)
    local realCreate, realResume = coroutine.create, coroutine.resume
    coCopy.create = function(f)
      local co = realCreate(f)
      attach(co)
      return co
    end
    coCopy.wrap = function(f)
      local co = coCopy.create(f)
      return function(...)
        local values = pack(realResume(co, ...))
        if not values[1] then error(values[2], 2) end
        return unpackFn(values, 2, values.n)
      end
    end
    env.coroutine = coCopy
  end

  -- The step/time guard is a real debug hook, and M11 treats any installed
  -- hook as a debugger by design. Verification needs the clean-host baseline,
  -- so the chunk sees a debug library whose gethook reports none while the
  -- harness hook keeps firing. Everything else in debug stays real.
  local dbg = rawget(_G, "debug")
  if dbg then
    -- A full debug table exposes registry/upvalue and hook manipulation.
    -- Expose only read-only stack helpers needed for debugger probes.
    env.debug = {
      gethook = function() return nil end,
      getinfo = dbg.getinfo,
      traceback = dbg.traceback,
    }
  end

  -- Executor-gate baseline: a gated chunk must still run under verification, so
  -- the harness presents the getgenv marker a real executor exposes. A plain
  -- website runner has no such marker and the gate no-ops there instead.
  env.getgenv = function() return env end

  return env
end

-- -------------------------------------------------------------- sandbox run
function Verifier.sandboxRun(chunk, opts)
  opts = opts or {}
  local capture = { parts = {}, bytes = 0, limited = false }
  -- Both counters stay in the float domain: Fengari's lua_Integer is 32-bit, so
  -- a large budget past 2^31 would wrap negative and disable the step guard.
  local maxSteps = opts.maxSteps
  if maxSteps == nil then maxSteps = Verifier.DEFAULTS.maxSteps end
  maxSteps = maxSteps + 0.0
  local stepChunk = opts.stepChunk
  if stepChunk == nil then stepChunk = Verifier.DEFAULTS.stepChunk end
  local seconds = opts.seconds
  if seconds == nil then seconds = Verifier.DEFAULTS.seconds end
  seconds = seconds + 0.0

  local debugLib = rawget(_G, "debug")
  local steps, started = 0.0, os.clock()
  local function tick()
    steps = steps + stepChunk + 0.0
    if steps > maxSteps then error("autofix: step limit", 0) end
    if seconds > 0 and (os.clock() - started) > seconds then
      error("autofix: time limit", 0)
    end
  end
  local hookOn = maxSteps > 0 and debugLib ~= nil and debugLib.sethook ~= nil

  local function attach(thread)
    if not hookOn then return end
    if thread then
      pcall(debugLib.sethook, thread, tick, "", stepChunk)
    else
      pcall(debugLib.sethook, tick, "", stepChunk)
    end
  end

  local env = makeEnv(capture, opts, attach)
  local loader = loadstring or load
  local chunkName = opts.chunkname or "=sandbox"
  local fn, loadErr
  if setfenv then
    fn, loadErr = loader(chunk, chunkName)
    if fn then setfenv(fn, env) end
  else
    fn, loadErr = load(chunk, chunkName, "t", env)
  end
  if not fn then
    return {
      ok = false, stage = "load", output = "", error = tostring(loadErr),
      steps = 0, elapsed = 0,
    }
  end

  attach(nil)
  local call = pack(pcall(fn))
  if hookOn then pcall(debugLib.sethook) end
  local elapsed = math.floor((os.clock() - started) * 1000 + 0.5)

  local ok = call[1] == true and not capture.limited
  local rets
  if ok then
    rets = pack(unpackFn(call, 2, call.n))
  else
    rets = pack()
  end
  return {
    ok = ok,
    stage = ok and "run" or "error",
    output = table.concat(capture.parts),
    outputLimited = capture.limited,
    error = capture.limited and OUTPUT_LIMIT_ERROR or (not ok) and tostring(call[2]) or nil,
    rets = rets,
    steps = steps,
    elapsed = elapsed,
  }
end

-- ------------------------------------------------------------- comparison
local function sketch(v, depth, seen)
  local t = type(v)
  if t == "nil" or t == "boolean" then return tostring(v) end
  if t == "number" then
    if v ~= v then return "nan" end
    if v == math.huge then return "inf" end
    if v == -math.huge then return "-inf" end
    return string.format("%.17g", v)
  end
  if t == "string" then return string.format("%q", v) end
  if t ~= "table" then return "<" .. t .. ">" end
  if depth <= 0 then return "{...}" end
  if seen[v] then return "<cycle>" end
  seen[v] = true
  local items = {}
  local count = 0
  for k, val in pairs(v) do
    items[#items + 1] = sketch(k, depth - 1, seen) .. "=" ..
      sketch(val, depth - 1, seen)
    count = count + 1
    if count >= 128 then
      items[#items + 1] = "..."
      break
    end
  end
  seen[v] = nil
  table.sort(items)
  return "{" .. table.concat(items, ",") .. "}"
end

local function sameReturns(a, b)
  local an = a and a.n or 0
  local bn = b and b.n or 0
  if an ~= bn then return false end
  for i = 1, an do
    if sketch(a[i], 2, {}) ~= sketch(b[i], 2, {}) then return false end
  end
  return true
end

-- Both chunks must agree on whether they finished, on everything they printed
-- and (when both finished) on their return values. Error messages are not
-- compared: renames and line numbers legitimately change them.
function Verifier.compare(reference, candidate, opts)
  opts = opts or {}
  if not reference then return true, nil end
  if reference.stage == "load" then return false, "reference does not load" end
  if candidate.stage == "load" then return false, "output does not load" end
  if reference.outputLimited or candidate.outputLimited then return false, "output limit" end
  if reference.ok ~= candidate.ok then
    return false, candidate.ok and "unexpected success" or "runtime error"
  end
  -- Two matching crashes do not establish semantic equivalence. Historically
  -- both chunks raising (even unrelated errors) could be marked verified.
  if not reference.ok then
    return false, "both executions failed; equivalence not established"
  end
  if reference.output ~= candidate.output then return false, "output mismatch" end
  if opts.compareReturns ~= false and candidate.ok and
    not sameReturns(reference.rets, candidate.rets) then
    return false, "return mismatch"
  end
  return true, nil
end

-- A chunk that was stopped by the sandbox budget, rather than by its own code,
-- did not finish. Both sides hitting the budget says nothing about agreement.
Verifier.integrityError = require("src.release").integrityError
function Verifier.isIntegrityError(message)
  -- Older artifacts used the shorter message.
  return message == Verifier.integrityError or message == "GsXFuscator: integrity check failed"
end

local function aborted(run)
  if run and run.outputLimited then return true end
  if run == nil or run.ok or type(run.error) ~= "string" then return false end
  return run.error:find("autofix: step limit", 1, true) ~= nil or
    run.error:find("autofix: time limit", 1, true) ~= nil
end

Verifier.aborted = aborted
Verifier.outputLimitError = OUTPUT_LIMIT_ERROR

function Verifier.verify(source, code, opts)
  opts = opts or {}
  local reference = Verifier.sandboxRun(source, opts)
  local candidate = Verifier.sandboxRun(code, opts)
  local refAborted = aborted(reference)
  local outputLimited = reference.outputLimited or candidate.outputLimited
  local matched, reason
  if not candidate.ok and Verifier.isIntegrityError(candidate.error) then
    matched, reason = false, candidate.error
  elseif outputLimited then
    matched, reason = false, "output limit"
  elseif refAborted then
    matched, reason = candidate.stage ~= "load", nil
  elseif aborted(candidate) then
    matched, reason = false, "sandbox limit"
  else
    matched, reason = Verifier.compare(reference, candidate, opts)
  end
  return {
    ok = matched,
    reason = reason,
    verified = reference.ok and candidate.ok and not refAborted and
      not outputLimited and not aborted(candidate),
    reference = reference,
    candidate = candidate,
    note = reference.stage == "load" and "source chunk does not load"
      or (not reference.ok and not refAborted) and
        "source raised a runtime error; verification is inconclusive"
      or outputLimited and OUTPUT_LIMIT_ERROR
      or refAborted and "source did not finish within the sandbox budget"
      or nil,
  }
end

return Verifier
