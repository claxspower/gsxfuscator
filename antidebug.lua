-- antidebug.lua -- layer 11: silent anti-debug deviation.
--
-- Pipeline position:
--   vmgen.emit(plan, { antidebug = cfg })
--
-- Detecting a debugger or an instrumentation layer must never stop the chunk:
-- a hard failure (error, os.exit, infinite loop) is easy to spot and to patch
-- out. Instead this layer removes the plaintext constants from under the
-- runtime: when a probe fires, every value-only string constant has its
-- letters rotated in place before execution starts (case preserved, z/Z wraps
-- to a/A). Instruction words, numbers, booleans, nil, global names and field
-- names are untouched, so control flow keeps advancing and nothing structural
-- can break; a hooked session simply computes on wrong data and silently
-- diverges. The entry call is additionally wrapped in a swallow-all pcall so
-- even a program error caused by the deviated constants cannot escape.
--
-- Probes (all pcall-guarded, read-only, never raise):
--   hook      active debug hook (debug.gethook/sethook instrumentation)
--   what      a fresh Lua function reports `what == "Lua"` and `linedefined >= 0`
--   func      debug.getinfo(fn, "f").func is the very same function object
--   dump      string.dump(fn) is stable and non-empty across two calls
--   addr      two fresh tables print distinct addresses (no pointer redaction)
--   trace     debug.traceback still returns a stack, not just the marker
--   setupv    debug.setupvalue really moves a closure's upvalue
--   loadc     the chunk loader is still the C loader, not a Lua replay shim
--   gproxy    _G carries no function-valued __index/__newindex proxy
--
-- The last five target environment loggers and dump harnesses, which forward
-- globals, redact addresses, hide tracebacks, block upvalue pulls or replay
-- compiled chunks while leaving the ordinary library calls intact.
--
-- A pre-existing host hook is diagnostic, never a standalone deviation: a
-- legitimate profiler or debugger must not corrupt otherwise valid code.
-- The load-time count-hook self-test is active but best-effort, restores the
-- hook baseline and adds a strong signal only when a claimed installed count-hook never fires if a hook that
-- the host claims is installed never fires. Unavailable APIs are inconclusive.
-- Probe weights and ordering remain derived from the build seed.
local Antidebug = {}

local floor = math.floor
local concat = table.concat

Antidebug.PROBES = {
  "hook", "what", "func", "dump", "byte", "concat", "pcall", "select",
  "type", "upv", "reg", "char", "tonum", "nextp", "raw", "sm", "envid",
  "mathl", "raweq", "tablel", "format", "find",
  -- Deeper behavioural probes: an instrumentation layer that fakes the debug
  -- library still has to keep the rest of the runtime honest.
  "xpcall", "pat", "co", "src",
  -- Second behavioural pack: length/case mapping, vararg unpacking, metamethod
  -- dispatch and the garbage collector. Each is a surface a proxy/emulation
  -- harness routinely stubs while leaving the debug library untouched.
  "len", "unpack", "meta", "gc",
  -- Third pack: range substrings, format width/hex and the min/max/floor
  -- triple. A literal spy that rewrites decoded strings at the library
  -- boundary has to preserve all three exactly, and most shims do not.
  "subx", "fmtx", "minx",
  -- Fourth pack: environment-proxy and fake-library fingerprints. These are
  -- the shapes an environment logger (global read/write tracing) leaves that
  -- the library-behaviour checks cannot see: sanitized table addresses,
  -- stubbed debug.traceback/setupvalue, a Lua-level replacement for the C
  -- loader, and a metatable on _G whose __index/__newindex is a function.
  "addr", "trace", "setupv", "loadc", "gproxy",
  -- Fifth pack: comparator sort, positional insert/remove, negative-index
  -- byte reads, debug line info and __len/rawlen dispatch. A library spy that
  -- mirrors the common call shapes still trips on at least one of these, and a
  -- dumped/replayed chunk loses its line info and reports -1.
  "sortx", "insertx", "bytex", "line", "metalen",
  -- Luau anti-environment probes: behavior invariants, not brittle fingerprints
  -- such as C function names, version-specific Path2D geometry or debug lines.
  "packx", "freezex", "bufferx", "infox",
}
Antidebug.HOOK_WEIGHT = 2
Antidebug.THRESHOLD = 2
Antidebug.TRIP = 0

-- Executor hosts legitimately install their own debug hooks and may wrap
-- string.dump/load for their sandbox. Those probes must not deviate a normal
-- executor session, or the protected program silently computes on garbage. In
-- an executor host they carry zero weight; only the library-integrity probes
-- (string.byte/concat, pcall, select) can trip, and those are never altered by
-- a healthy executor.
Antidebug.AMBIGUOUS = {
  hook = true, what = true, func = true, dump = true, type = true,
  upv = true, reg = true,
  -- Executors commonly wrap xpcall for error reporting and coroutine entry
  -- points for thread bookkeeping, and some strip debug info from injected
  -- chunks. Those are legitimate host behaviours, so they carry zero weight
  -- on an executor; on a plain host the same swaps are instrumentation.
  xpcall = true, co = true, src = true,
  -- Environment loggers and dump harnesses routinely replace traceback (to
  -- hide their own frames), stub setupvalue/upvaluejoin (to block upvalue
  -- pulls), swap the loader for a Lua wrapper (to intercept compiled chunks)
  -- and put a proxy around _G. Executors do some of the same things for their
  -- own sandbox, so these are demoted on an executor host.
  trace = true, setupv = true, loadc = true, gproxy = true,
  -- Executors and some Launchers strip debug line info from injected chunks;
  -- that is a host policy, not instrumentation, so the line probe is demoted.
  line = true, infox = true,
}

-- Every known executor API surface. Detection must not depend on a single
-- function: mobile and serverside executors drop some of these (some hide
-- getgenv, some only expose request/http_request). A false negative here
-- demotes nothing, so the executor's own debug hooks and dump wrappers would
-- trip the ambiguous probes and silently deviate a healthy session -- the
-- "works on some executors, not others" failure. Any one hit is enough.
Antidebug.EXECUTOR_KEYS = {
  "getgenv", "gethui", "identifyexecutor", "hookfunction", "request",
  "http_request", "syn", "getrawmetatable", "setreadonly", "cloneref",
  "getconnections", "firetouchinterest", "fireclickdetector", "queue_on_teleport",
  "getscriptbytecode", "decompile", "saveinstance", "checkcaller",
}

-- Second demotion class: pure library-behaviour probes. Healthy executors keep
-- these functions untouched, but a few sandboxes wrap one of them lazily, so a
-- single hit there weighs 1 instead of 2: two independent library swaps still
-- trip, a lone sandbox wrapper never deviates the session on its own.
Antidebug.SOFT = {
  char = true, tonum = true, nextp = true, raw = true, sm = true, envid = true,
  mathl = true, raweq = true, tablel = true, format = true, find = true,
  -- A string spy that logs decrypted literals wraps gsub/gmatch; one such
  -- wrapper alone should not deviate a healthy session, but two soft hits do.
  pat = true,
  -- Sandboxes lazily wrap one of these (a length spy, a vararg shim). They are
  -- library behaviour, not debug instrumentation, so they weight 1 on a host
  -- that already looks like an executor.
  len = true, unpack = true, meta = true, gc = true,
  subx = true, fmtx = true, minx = true,
  -- Comparator sort and positional insert/remove. A table spy that only
  -- mirrors append/remove-end keeps these wrong; they are library behaviour,
  -- so an executor sandbox that wraps one weighs 1, not 2.
  sortx = true, insertx = true, bytex = true,
  -- Sanitized table addresses are a library-behaviour difference, not debug
  -- instrumentation: an executor that hides pointers should not deviate.
  addr = true, packx = true, freezex = true, bufferx = true,
}

-- Always-weak class: signals that hardened environments legitimately produce
-- (a sandbox replaces the C loader with a Lua wrapper, a launcher forwards it).
-- They add to the score but never trip alone on any host; they only push an
-- already suspicious host over the threshold.
Antidebug.WEAK = {
  loadc = true,
  -- __len dispatch and rawlen presence differ across hosts that otherwise run
  -- the program correctly, so this only ever corroborates another hit.
  metalen = true,
}

-- Optional namespaces may be proxies whose __index rejects individual keys.
-- A denied read is absence, not evidence of inconsistent API behaviour.
local function optionalRead(t, key)
  if type(t) ~= "table" then return nil end
  local ok, value = pcall(function() return t[key] end)
  if ok then return value end
end

function Antidebug.isExecutorHost(env)
  if type(env) ~= "table" then return false end
  local keys = Antidebug.EXECUTOR_KEYS
  for i = 1, #keys do
    local value = optionalRead(env, keys[i])
    if type(value) == "function" or
       (keys[i] == "syn" and type(value) == "table") then return true end
  end
  return false
end

local probeFn = function() return 1 end

local function makeRng(seed)
  local state = floor(tonumber(seed) or 0) % 4294967296
  if state < 0 then state = state + 4294967296 end
  return function(n)
    state = (state * 1664525 + 1013904223) % 4294967296
    -- The LCG's low bit alternates every step, so draw from the high half.
    return floor(state / 65536) % n + 1
  end
end

-- --------------------------------------------------------------------- plan
function Antidebug.plan(opts)
  opts = opts or {}
  local seed = floor(tonumber(opts.seed) or 0) % 4294967296
  if seed < 0 then seed = seed + 4294967296 end
  local rng = makeRng(seed + 0xA11D)
  local mask = 1
  local weak = 0
  for bit = 1, #Antidebug.PROBES - 1 do
    if rng(2) == 1 then
      mask = mask + 2 ^ bit
      weak = weak + 1
    end
  end
  if weak == 0 then mask = mask + 2 end
  -- Cover at least two independently tested Luau language invariants per
  -- build, while keeping the exact pair seed-dependent. They are still
  -- capability-gated at runtime and do nothing on a host lacking those APIs.
  local luauNames = { packx = true, freezex = true, bufferx = true, infox = true }
  local selected = 0
  for i = 1, #Antidebug.PROBES do
    if luauNames[Antidebug.PROBES[i]] then
      local bit = 2 ^ (i - 1)
      if mask % (bit * 2) >= bit then selected = selected + 1 end
    end
  end
  while selected < 2 do
    local i = #Antidebug.PROBES - rng(4) + 1
    local bit = 2 ^ (i - 1)
    if mask % (bit * 2) < bit then mask = mask + bit selected = selected + 1 end
  end
  local weights = { hook = Antidebug.HOOK_WEIGHT }
  for i = 2, #Antidebug.PROBES do
    -- The library-integrity probes are the only ones that can fire on a
    -- host without a debug library, so each of them trips alone.
    weights[Antidebug.PROBES[i]] = i >= 5 and 2 or rng(2)
  end
  -- Loader replacement is a shape hardened hosts legitimately produce, so it
  -- is always compiled with a weight of one and never trips alone.
  weights.loadc = 1
  -- Fill uncovered families without discarding any seed-selected probes.
  local families = {
    { byte = true, concat = true, pcall = true, select = true },
    { char = true, mathl = true, tablel = true },
    { tonum = true, nextp = true, raw = true, sm = true, raweq = true },
    { len = true, unpack = true, meta = true, gc = true },
    -- Environment-proxy fingerprints: the shapes a logger leaves when it
    -- forwards globals, hides addresses or replays compiled chunks.
    { addr = true, trace = true, setupv = true, gproxy = true },
    { packx = true, freezex = true, bufferx = true, infox = true },
  }
  for i = 1, #families do
    local bits, covered = {}, false
    for j = 1, #Antidebug.PROBES do
      if families[i][Antidebug.PROBES[j]] then
        local bit = 2 ^ (j - 1)
        bits[#bits + 1] = bit
        if mask % (bit * 2) >= bit then covered = true end
      end
    end
    if not covered then mask = mask + bits[rng(#bits)] end
  end
  local probes = {}
  for i = 1, #Antidebug.PROBES do
    local bit = 2 ^ (i - 1)
    if mask % (bit * 2) >= bit then probes[#probes + 1] = Antidebug.PROBES[i] end
  end
  for i = #probes, 2, -1 do
    local j = rng(i)
    probes[i], probes[j] = probes[j], probes[i]
  end
  return {
    seed = seed, mask = mask, probes = probes, weights = weights,
    threshold = Antidebug.THRESHOLD,
    -- Per-build rotation offset for the silent deviation. Without it every
    -- build of every script rotated a given string by the same amount, so a
    -- harness could learn the mapping once and invert it offline.
    salt = rng(192),
  }
end

-- Reference implementation of the emitted probes. `opts.env` must provide the
-- `debug` and `string` tables the runtime will see; it defaults to the host.
function Antidebug.probe(cfg, opts)
  opts = opts or {}
  local host = opts.env or _G
  local function namespace(t)
    if type(t) ~= "table" then return nil end
    return setmetatable({}, { __index = function(_, key)
      return optionalRead(t, key)
    end })
  end
  -- Read-only views protect capability discovery without changing host tables
  -- or wrapping the functions whose behaviour is being checked.
  local libraries = { debug = true, string = true, table = true,
    math = true, coroutine = true }
  local env = setmetatable({}, { __index = function(_, key)
    local value = optionalRead(host, key)
    if libraries[key] then return namespace(value) end
    return value
  end })
  local dbg = env.debug
  local str = env.string
  local exHost = Antidebug.isExecutorHost(host)
  local threshold = cfg.threshold
  local out = { score = 0, hits = {}, probe = probeFn, threshold = threshold }
  local function weigh(name)
    local w = cfg.weights[name] or 0
    if exHost and Antidebug.AMBIGUOUS[name] then return 0 end
    if Antidebug.WEAK[name] and w > 1 then return 1 end
    if exHost and Antidebug.SOFT[name] and w > 1 then return 1 end
    return w
  end
  local function enabled(name)
    for i = 1, #cfg.probes do
      if cfg.probes[i] == name then return true end
    end
    return false
  end
  if enabled("hook") and dbg and type(dbg.gethook) == "function" then
    -- A real, pre-existing profiler/debugger hook is a legitimate host state.
    -- Record it for diagnostics, but never turn it into a tamper score by
    -- itself; the generated hook self-test also skips that host state.
    local ok, hook = pcall(dbg.gethook)
    if ok and hook ~= nil then
      out.hits.hook = true
    end
  end
  if enabled("what") and dbg and type(dbg.getinfo) == "function" then
    local ok, valid = pcall(function()
      local info = dbg.getinfo(probeFn, "S")
      return type(info) == "table" and info.what == "Lua" and
        type(info.linedefined) == "number" and info.linedefined >= 0
    end)
    if ok and not valid then
      out.hits.what = true
      out.score = out.score + weigh("what")
    end
  end
  if enabled("func") and dbg and type(dbg.getinfo) == "function" then
    local ok, valid = pcall(function()
      local info = dbg.getinfo(probeFn, "f")
      return type(info) == "table" and info.func == probeFn
    end)
    if ok and not valid then
      out.hits.func = true
      out.score = out.score + weigh("func")
    end
  end
  if enabled("byte") and str and type(str.byte) == "function" then
    local ok, v = pcall(str.byte, "A")
    if not ok or v ~= 65 then
      out.hits.byte = true
      out.score = out.score + weigh("byte")
    end
  end
  -- Behavioural library checks. Each one is skipped when the host simply does
  -- not expose the library, so a minimal environment never trips on absence.
  if enabled("char") and str and type(str.char) == "function" and
     type(str.sub) == "function" and type(str.rep) == "function" then
    local ok, v = pcall(function()
      return str.char(65, 66) == "AB" and str.sub("abc", 2, 2) == "b" and
        str.rep("xy", 2) == "xyxy"
    end)
    if ok and v ~= true then
      out.hits.char = true
      out.score = out.score + weigh("char")
    end
  end
  if enabled("tonum") and type(env.tonumber) == "function" and
     type(env.tostring) == "function" then
    local ok, v = pcall(function()
      return env.tonumber("0x10") == 16 and env.tostring(42) == "42"
    end)
    if ok and v ~= true then
      out.hits.tonum = true
      out.score = out.score + weigh("tonum")
    end
  end
  if enabled("nextp") and type(env.next) == "function" and
     type(env.pairs) == "function" and type(env.ipairs) == "function" then
    local ok, v = pcall(function()
      local t = { 10, 20, x = 5 }
      local s = 0
      for i, x in env.ipairs(t) do s = s + i * x end
      local c = 0
      for _ in env.pairs(t) do c = c + 1 end
      return s == 50 and c == 3 and env.next({ z = 1 }) == "z"
    end)
    if ok and v ~= true then
      out.hits.nextp = true
      out.score = out.score + weigh("nextp")
    end
  end
  if enabled("raw") and type(env.rawget) == "function" and
     type(env.rawset) == "function" and type(env.setmetatable) == "function" then
    local ok, v = pcall(function()
      local t = env.setmetatable({}, { __index = function() return 9 end })
      env.rawset(t, "y", 4)
      return env.rawget(t, "x") == nil and t.x == 9 and t.y == 4
    end)
    if ok and v ~= true then
      out.hits.raw = true
      out.score = out.score + weigh("raw")
    end
  end
  if enabled("sm") and type(env.setmetatable) == "function" and
     type(env.getmetatable) == "function" then
    local ok, v = pcall(function()
      local t = env.setmetatable({}, { __metatable = "K" })
      return env.getmetatable(t) == "K"
    end)
    if ok and v ~= true then
      out.hits.sm = true
      out.score = out.score + weigh("sm")
    end
  end
  -- Only a self-mirror makes claims about the active environment's libraries.
  -- A distinct _G can legitimately be an empty/shared sandbox data table.
  if enabled("envid") and env._G == host then
    local g = env._G
    local ok, v = pcall(function()
      return type(g.string) == "table" and type(g.string.byte) == "function" and
        type(g.pcall) == "function" and type(g.type) == "function"
    end)
    if ok and v ~= true then
      out.hits.envid = true
      out.score = out.score + weigh("envid")
    end
  end
  if enabled("concat") and env.table and type(env.table.concat) ==
     "function" then
    local ok, v = pcall(env.table.concat, { "a", "b" })
    if not ok or v ~= "ab" then
      out.hits.concat = true
      out.score = out.score + weigh("concat")
    end
  end
  if enabled("pcall") and type(env.pcall) == "function" and
     type(env.error) == "function" then
    local CP, ER = env.pcall, env.error
    local ok, v = pcall(function()
      local s, a, b, c = CP(function() return nil, false, 7 end)
      if s ~= true or a ~= nil or b ~= false or c ~= 7 then return false end
      local f, msg = CP(function() return ER("zq") end)
      if f ~= false or type(msg) ~= "string" then return false end
      local SF = str and str.find
      if type(SF) == "function" and SF(msg, "zq", 1, true) == nil then
        return false
      end
      local marker = {}
      local e, obj = CP(function() return ER(marker) end)
      return e == false and obj == marker
    end)
    if not ok or v ~= true then
      out.hits.pcall = true
      out.score = out.score + weigh("pcall")
    end
  end
  if enabled("select") and type(env.select) == "function" then
    local SL = env.select
    local ok, v = pcall(function()
      if SL("#", 1, nil, 3) ~= 3 or SL("#") ~= 0 then return false end
      local a, b, c, d = SL(2, 1, nil, false, "tail")
      local x, y, z, w = SL(-3, 1, nil, false, "tail")
      return a == nil and b == false and c == "tail" and d == nil and
        x == nil and y == false and z == "tail" and w == nil and
        SL(-1, 1, nil, false, "tail") == "tail"
    end)
    if not ok or v ~= true then
      out.hits.select = true
      out.score = out.score + weigh("select")
    end
  end
  -- The host's own `type` is the cheapest tamper oracle: every Lua sandbox and
  -- every injector leaves it in place, so a wrapped/monkeypatched `type` (one
  -- that reports "table" for numbers, or raises on a primitive) is a reliable
  -- sign the global environment is being watched. Skipped when the host has no
  -- callable `type` at all, so a minimal env never trips on absence.
  if enabled("type") and type(env.type) == "function" then
    local ok, v = pcall(function()
      return env.type(1) == "number" and env.type("x") == "string" and
        env.type({}) == "table" and env.type(nil) == "nil" and
        env.type(true) == "boolean"
    end)
    if ok and v ~= true then
      out.hits.type = true
      out.score = out.score + weigh("type")
    end
  end
  -- Debug-library integrity, deeper than a hook check: `getupvalue` must still
  -- report the captured table, and the registry's _LOADED table must still hold
  -- the very `string` table the environment runs on. A devirt harness that
  -- swaps libraries or lies through the debug library changes one of them.
  if enabled("upv") and dbg and type(dbg.getupvalue) == "function" then
    local box = { 0x51AD + (cfg.seed % 251) }
    local f = function() return box[1] end
    local ok, _, val = pcall(dbg.getupvalue, f, 1)
    if ok and val ~= box then
      out.hits.upv = true
      out.score = out.score + weigh("upv")
    end
  end
  if enabled("reg") and dbg and type(dbg.getregistry) == "function" then
    local ok, bad = pcall(function()
      local reg = dbg.getregistry()
      if type(reg) ~= "table" then return true end
      local loaded = reg["_LOADED"]
      return type(loaded) == "table" and type(loaded["string"]) ~= "table"
    end)
    if ok and bad then
      out.hits.reg = true
      out.score = out.score + weigh("reg")
    end
  end
  if enabled("dump") and str and type(str.dump) == "function" then
    local ok1, a = pcall(str.dump, probeFn)
    local ok2, b = pcall(str.dump, probeFn)
    if ok1 and ok2 and (type(a) ~= "string" or #a == 0 or a ~= b) then
      out.hits.dump = true
      out.score = out.score + weigh("dump")
    end
  end
  -- Arithmetic library behaviour: a patched math table (rounded results, a
  -- replaced floor) silently changes program output, so it must trip.
  if enabled("mathl") and type(env.math) == "table" and
     type(env.math.floor) == "function" and type(env.math.abs) == "function" and
     type(env.math.max) == "function" then
    local ok, v = pcall(function()
      return env.math.floor(3.7) == 3 and env.math.floor(-0.5) == -1 and
        env.math.abs(-4) == 4 and env.math.max(1, 2) == 2
    end)
    if ok and v ~= true then
      out.hits.mathl = true
      out.score = out.score + weigh("mathl")
    end
  end
  -- Identity semantics: raw equality must still be raw (no __eq trampoline).
  if enabled("raweq") and type(env.rawequal) == "function" then
    local ok, v = pcall(function()
      local t = {}
      return env.rawequal(t, t) == true and env.rawequal({}, {}) == false and
        env.rawequal(t, {}) == false
    end)
    if ok and v ~= true then
      out.hits.raweq = true
      out.score = out.score + weigh("raweq")
    end
  end
  -- Table library behaviour: insert/remove/sort must stay positional.
  if enabled("tablel") and type(env.table) == "table" and
     type(env.table.insert) == "function" and
     type(env.table.remove) == "function" and
     type(env.table.sort) == "function" then
    local ok, v = pcall(function()
      local t = { 3, 1, 2 }
      env.table.sort(t)
      env.table.insert(t, 4)
      local r = env.table.remove(t)
      return t[1] == 1 and t[2] == 2 and t[3] == 3 and #t == 3 and r == 4
    end)
    if ok and v ~= true then
      out.hits.tablel = true
      out.score = out.score + weigh("tablel")
    end
  end
  -- Format-library behaviour: a patched format silently rewrites every string
  -- a program builds from data, so it must trip.
  if enabled("format") and str and type(str.format) == "function" then
    local ok, v = pcall(function()
      return str.format("%d|%s", 7, "q") == "7|q" and
        str.format("%.2f", 1.5) == "1.50"
    end)
    if ok and v ~= true then
      out.hits.format = true
      out.score = out.score + weigh("format")
    end
  end
  -- Pattern-library behaviour: find must honour the plain flag and positions.
  if enabled("find") and str and type(str.find) == "function" then
    local ok, v = pcall(function()
      return str.find("abc", "b", 1, true) == 2 and
        str.find("a.c", ".", 1, true) == 2 and
        str.find("abc", "z", 1, true) == nil
    end)
    if ok and v ~= true then
      out.hits.find = true
      out.score = out.score + weigh("find")
    end
  end
  -- xpcall integrity: the protected call must still return a function's values
  -- and hand the handler the exact error object. A wrapper that rewrites error
  -- objects (common in devirt harnesses that want a clean stack report) fails
  -- the identity check without touching the debug library.
  if enabled("xpcall") and type(env.xpcall) == "function" and
     type(env.error) == "function" then
    local XP, ER = env.xpcall, env.error
    local ok, v = pcall(function()
      local s1, a, b = XP(function() return 3, 4 end, function(e) return e end)
      if s1 ~= true or a ~= 3 or b ~= 4 then return false end
      local marker = {}
      local s2, obj = XP(function() ER(marker) end, function(e) return e end)
      return s2 == false and obj == marker
    end)
    if ok and v ~= true then
      out.hits.xpcall = true
      out.score = out.score + weigh("xpcall")
    end
  end
  -- Pattern-library behaviour with a replacement callback. A string spy that
  -- intercepts gsub/gmatch to log decrypted text changes the callback's
  -- arguments or call count, which this round-trip exposes.
  if enabled("pat") and str and type(str.gsub) == "function" and
     type(str.gmatch) == "function" then
    local ok, v = pcall(function()
      local n = 0
      local s = str.gsub("ab12cd", "%d", function(d) n = n + 1 return "<" .. d .. ">" end)
      local c = 0
      for _ in str.gmatch("a1b2", "%d") do c = c + 1 end
      return s == "ab<1><2>cd" and n == 2 and c == 2
    end)
    if ok and v ~= true then
      out.hits.pat = true
      out.score = out.score + weigh("pat")
    end
  end
  -- Coroutine round-trip. Instruction tracers and thread-hopping dumpers wrap
  -- resume/wrap/yield; the yielded values, the intermediate status and the
  -- final return all have to stay exact.
  if enabled("co") and type(env.coroutine) == "table" then
    local CO = env.coroutine
    if type(CO.create) == "function" and type(CO.resume) == "function" and
       type(CO.yield) == "function" and type(CO.status) == "function" and
       type(CO.wrap) == "function" then
      local ok, v = pcall(function()
        local th = CO.create(function(a)
          local b = CO.yield(a + 1)
          return b * 2
        end)
        local r1, x1 = CO.resume(th, 4)
        local s1 = CO.status(th)
        local r2, x2 = CO.resume(th, 6)
        local s2 = CO.status(th)
        local w = CO.wrap(function() CO.yield(7) return 8 end)
        local p = w()
        local q = w()
        return r1 == true and x1 == 5 and s1 == "suspended" and
          r2 == true and x2 == 12 and s2 == "dead" and p == 7 and q == 8
      end)
      if ok and v ~= true then
        out.hits.co = true
        out.score = out.score + weigh("co")
      end
    end
  end
  -- Debug-info shape: both functions live in this chunk, so their reported
  -- source must match, the source and short source must be non-empty strings
  -- and the line range must be real. A chunk recompiled by a dump-replay tool
  -- is stripped (source "=?", linedefined -1) and trips here even when every
  -- debug entry point still answers.
  if enabled("src") and dbg and type(dbg.getinfo) == "function" then
    local f2 = function() return 2 end
    local ok, bad = pcall(function()
      local a = dbg.getinfo(probeFn, "S")
      local b = dbg.getinfo(f2, "S")
      return type(a) ~= "table" or type(b) ~= "table" or
        type(a.source) ~= "string" or #a.source == 0 or
        type(b.source) ~= "string" or a.source ~= b.source or
        type(a.linedefined) ~= "number" or a.linedefined < 0 or
        type(a.short_src) ~= "string"
    end)
    if ok and bad then
      out.hits.src = true
      out.score = out.score + weigh("src")
    end
  end
  -- Length and case mapping: a literal spy that rewrites decoded strings at
  -- the library boundary still has to answer lengths and case exactly.
  if enabled("len") and str and type(str.len) == "function" and
     type(str.upper) == "function" and type(str.lower) == "function" then
    local ok, v = pcall(function()
      return str.len("abc") == 3 and str.upper("aB") == "AB" and
        str.lower("aB") == "ab"
    end)
    if ok and v ~= true then
      out.hits.len = true
      out.score = out.score + weigh("len")
    end
  end
  -- Vararg unpacking: table.unpack (5.2+) or the 5.1 global. A shim that
  -- intercepts a call's argument list breaks the range form here.
  if enabled("unpack") then
    local UP = env.table and env.table.unpack
    if type(UP) ~= "function" then UP = env.unpack end
    if type(UP) == "function" then
      local ok, v = pcall(function()
        local a, b, c = UP({ 1, 2, 3 })
        if a ~= 1 or b ~= 2 or c ~= 3 then return false end
        local d, e = UP({ 1, 2, 3 }, 2, 3)
        return d == 2 and e == 3
      end)
      if ok and v ~= true then
        out.hits.unpack = true
        out.score = out.score + weigh("unpack")
      end
    end
  end
  -- Metamethod dispatch round-trip: __index, __newindex and __call have to
  -- fire exactly once with the documented arguments. A hookmetamethod layer
  -- that hides itself still changes one of these results or call counts.
  if enabled("meta") and type(env.setmetatable) == "function" and
     type(env.rawset) == "function" then
    local ok, v = pcall(function()
      local t = env.setmetatable({}, {
        __index = { m = "?", k = "?" },
        __newindex = function(s, k, x) env.rawset(s, "n" .. k, x) end,
        __call = function(_, x) return x * 2 end,
      })
      if t.m ~= "?" or t(3) ~= 6 then return false end
      t.k = 1
      return t.nk == 1 and t.k == "?"
    end)
    if ok and v ~= true then
      out.hits.meta = true
      out.score = out.score + weigh("meta")
    end
  end
  -- Collector presence: a stubbed collectgarbage returns a non-number or a
  -- frozen zero. Only the counting modes are read; no collection is forced.
  if enabled("gc") and type(env.collectgarbage) == "function" then
    local ok, v = pcall(function()
      local c = env.collectgarbage("count")
      return type(c) == "number" and c > 0
    end)
    if ok and v ~= true then
      out.hits.gc = true
      out.score = out.score + weigh("gc")
    end
  end
  -- Range substrings: negative indices and clamping are exact semantics a
  -- literal-rewriting spy has to preserve; most shims get one of them wrong.
  if enabled("subx") and str and type(str.sub) == "function" then
    local ok, v = pcall(function()
      return str.sub("abcdef", -3) == "def" and str.sub("abc", 5) == "" and
        str.sub("abc", 2, 99) == "bc" and str.sub("abc", -2, -2) == "b"
    end)
    if ok and v ~= true then
      out.hits.subx = true
      out.score = out.score + weigh("subx")
    end
  end
  -- Format width, precision and hex. A proxy that intercepts formatted output
  -- rewrites one of these even when its simple "%d" path still works.
  if enabled("fmtx") and str and type(str.format) == "function" then
    local ok, v = pcall(function()
      return str.format("%05.2f", 1.5) == "01.50" and
        str.format("%x", 255) == "ff"
    end)
    if ok and v ~= true then
      out.hits.fmtx = true
      out.score = out.score + weigh("fmtx")
    end
  end
  -- The remaining math triples: min/max selection and a fractional floor.
  if enabled("minx") and type(env.math) == "table" and
     type(env.math.min) == "function" and type(env.math.max) == "function" and
     type(env.math.floor) == "function" then
    local ok, v = pcall(function()
      return env.math.min(4, 2, 7) == 2 and env.math.max(4, 2, 7) == 7 and
        env.math.floor(1048576 / 7) == 149796
    end)
    if ok and v ~= true then
      out.hits.minx = true
      out.score = out.score + weigh("minx")
    end
  end
  -- Environment-proxy fingerprints. An environment logger has to route every
  -- global read through its own table, so it leaves at least one of these
  -- shapes: a sanitized tostring that hides pointers, a traceback that no
  -- longer carries a stack, a stubbed setupvalue (dumping tools block upvalue
  -- pulls), a Lua-level replacement for the C loader (chunk replay), or a
  -- function-valued __index/__newindex on _G.
  if enabled("addr") and type(env.tostring) == "function" then
    local ok, v = pcall(function()
      local a = env.tostring({})
      local b = env.tostring({})
      return type(a) == "string" and a ~= b
    end)
    if ok and v ~= true then
      out.hits.addr = true
      out.score = out.score + weigh("addr")
    end
  end
  if enabled("trace") and dbg and type(dbg.traceback) == "function" then
    local ok, s = pcall(dbg.traceback, "T", 1)
    if ok and (type(s) ~= "string" or #s <= 1) then
      out.hits.trace = true
      out.score = out.score + weigh("trace")
    end
  end
  if enabled("setupv") and dbg and type(dbg.setupvalue) == "function" then
    local boxA, boxB = {}, {}
    local f = function() return boxA end
    local ok, v = pcall(function()
      dbg.setupvalue(f, 1, boxB)
      local moved = f() == boxB
      dbg.setupvalue(f, 1, boxA)
      return moved and f() == boxA
    end)
    if ok and v ~= true then
      out.hits.setupv = true
      out.score = out.score + weigh("setupv")
    end
  end
  if enabled("loadc") and dbg and type(dbg.getinfo) == "function" and
     type(env.load) == "function" then
    local ok, bad = pcall(function()
      local info = dbg.getinfo(env.load, "S")
      return type(info) == "table" and info.what ~= "C"
    end)
    if ok and bad then
      out.hits.loadc = true
      out.score = out.score + weigh("loadc")
    end
  end
  if enabled("gproxy") and type(env.getmetatable) == "function" and
     type(env._G) == "table" then
    local ok, bad = pcall(function()
      local mt = env.getmetatable(env._G)
      if type(mt) ~= "table" then return false end
      return type(mt.__index) == "function" or
        type(mt.__newindex) == "function"
    end)
    if ok and bad then
      out.hits.gproxy = true
      out.score = out.score + weigh("gproxy")
    end
  end
  -- Comparator sort: argument order and the resulting order are fixed
  -- semantics a table spy that only mirrors the no-comparator path gets wrong.
  if enabled("sortx") and type(env.table) == "table" and
     type(env.table.sort) == "function" then
    local ok, v = pcall(function()
      local t = { 3, 1, 2 }
      env.table.sort(t, function(a, b) return a > b end)
      return t[1] == 3 and t[2] == 2 and t[3] == 1
    end)
    if ok and v ~= true then
      out.hits.sortx = true
      out.score = out.score + weigh("sortx")
    end
  end
  -- Positional insert/remove: front insertion and front removal shift the
  -- whole table exactly once. An append-only shim fails both.
  if enabled("insertx") and type(env.table) == "table" and
     type(env.table.insert) == "function" and
     type(env.table.remove) == "function" then
    local ok, v = pcall(function()
      local t = { 1, 2, 3 }
      env.table.insert(t, 1, 9)
      local r = env.table.remove(t, 1)
      return t[1] == 1 and t[2] == 2 and t[3] == 3 and r == 9
    end)
    if ok and v ~= true then
      out.hits.insertx = true
      out.score = out.score + weigh("insertx")
    end
  end
  -- Negative and out-of-range byte reads. A literal spy that only forwards
  -- positive indices returns a value (or raises) here.
  if enabled("bytex") and str and type(str.byte) == "function" then
    local ok, v = pcall(function()
      local a, b = str.byte("abc", -2, -1)
      return a == 98 and b == 99 and str.byte("abc", 0) == nil and
        str.byte("abc", 4) == nil
    end)
    if ok and v ~= true then
      out.hits.bytex = true
      out.score = out.score + weigh("bytex")
    end
  end
  -- Debug line info: a chunk compiled with stripped debug info reports -1
  -- here even though every debug entry point still answers. Dump-replay
  -- harnesses rebuild the chunk without line info.
  if enabled("line") and dbg and type(dbg.getinfo) == "function" then
    local ok, v = pcall(function()
      local info = dbg.getinfo(1, "l")
      return type(info) == "table" and type(info.currentline) == "number" and
        info.currentline >= 0
    end)
    if ok and v ~= true then
      out.hits.line = true
      out.score = out.score + weigh("line")
    end
  end
  -- __len dispatch plus rawlen: #t honours the metamethod while rawlen stays
  -- raw. A metamethod-hiding layer breaks one side of the pair.
  if enabled("metalen") and type(env.rawlen) == "function" and
     type(env.setmetatable) == "function" then
    local ok, v = pcall(function()
      local t = env.setmetatable({}, { __len = function() return 99 end })
      return #t == 99 and env.rawlen(t) == 0
    end)
    if ok and v ~= true then
      out.hits.metalen = true
      out.score = out.score + weigh("metalen")
    end
  end
  -- Luau/Roblox environment emulation checks (from the reference harness).
  -- Never infer tampering from an unavailable API. On executor hosts a single
  -- discrepancy in these optional semantics carries only one point.
  if enabled("packx") and env.table and type(env.table.pack) == "function" then
    local ok, v = pcall(function()
      local t = env.table.pack("a", nil, "z")
      return type(t) == "table" and t.n == 3 and t[1] == "a" and
        t[2] == nil and t[3] == "z"
    end)
    if ok and v ~= true then
      out.hits.packx = true
      out.score = out.score + weigh("packx")
    end
  end
  if enabled("freezex") and env.table and
     type(env.table.freeze) == "function" and
     type(env.table.isfrozen) == "function" then
    local ok, v = pcall(function()
      local t = env.table.freeze({ marker = 1 })
      if type(t) ~= "table" or not env.table.isfrozen(t) then return false end
      local written = pcall(function() t.marker = 2 end)
      return not written and t.marker == 1
    end)
    if ok and v ~= true then
      out.hits.freezex = true
      out.score = out.score + weigh("freezex")
    end
  end
  local buf = env.buffer
  if enabled("bufferx") and type(buf) == "table" and
     type(buf.create) == "function" and
     type(buf.writeu16) == "function" and
     type(buf.readu16) == "function" and
     type(buf.len) == "function" then
    local ok, v = pcall(function()
      local b = buf.create(4)
      buf.writeu16(b, 1, 48879)
      return buf.len(b) == 4 and buf.readu16(b, 1) == 48879
    end)
    if ok and v ~= true then
      out.hits.bufferx = true
      out.score = out.score + weigh("bufferx")
    end
  end
  if enabled("infox") and dbg and type(dbg.info) == "function" then
    local ok, v = pcall(function()
      local f = function(x) return x end
      return rawequal(dbg.info(f, "f"), f)
    end)
    if ok and v ~= true then
      out.hits.infox = true
      out.score = out.score + weigh("infox")
    end
  end
  out.trip = out.score >= threshold and 1 or 0
  return out
end
-- ------------------------------------------------------------------- codegen
-- Field names are shipped as byte codes and rebuilt at load, so the probe
-- sites carry no grep-able `gethook` / `linedefined` marker.
local function codes(text)
  local out = {}
  for i = 1, #text do out[i] = string.byte(text, i) end
  return table.concat(out, ",")
end

-- Hardcoded-globals handles used by the emitted probes: `type`/`pcall` come
-- from the locals vmgen captured at load, so a global swap cannot redirect the
-- probes themselves. Fallbacks keep the module usable standalone.
local function tyOf(names) return names.G4 or "type" end
local function pcOf(names) return names.G3 or "pcall" end
local function keyOf(names, text) return names.DM .. "(" .. codes(text) .. ")" end

local function hookLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  -- An existing hook is neither payload tamper nor an anti-debug failure.
  -- Observe it without adding to the deviation counter (matching probe()).
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB ..
    "[" .. names.AGH .. "])==\"function\" then " .. PC .. "(" .. names.ADB ..
    "[" .. names.AGH .. "]) end"
end

local function whatLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB ..
    "[" .. names.AGI .. "])==\"function\" then local ok,r=" .. PC .. "(" .. names.ADB ..
    "[" .. names.AGI .. "]," .. names.ADX .. ",\"S\") if ok and (" .. TY ..
    "(r)~=\"table\" or " ..
    "r[" .. names.AGW .. "]~=\"Lua\" or " .. TY .. "(r[" .. names.AGL ..
    "])~=\"number\" or r[" .. names.AGL .. "]<0) then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end"
end

local function funcLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB ..
    "[" .. names.AGI .. "])==\"function\" then local ok,r=" .. PC .. "(" .. names.ADB ..
    "[" .. names.AGI .. "]," .. names.ADX .. ",\"f\") if ok and (" .. TY ..
    "(r)~=\"table\" or " ..
    "r[" .. names.AGF .. "]~=" .. names.ADX .. ") then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end"
end

local function byteLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "if " .. names.ADS .. " and " .. TY .. "(" .. names.ADS ..
    ".byte)==\"function\" then local ok,v=" .. PC .. "(" .. names.ADS ..
    ".byte,\"A\") if not ok or v~=65 then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end"
end

local function concatLine(names, weight)
  local TBL, CN = keyOf(names, "table"), keyOf(names, "concat")
  local TY, PC = tyOf(names), pcOf(names)
  return "local TB=" .. names.E .. "[" .. TBL .. "] if " .. TY ..
    "(TB)==\"table\" and " .. TY .. "(TB[" .. CN ..
    "])==\"function\" then local ok,v=" .. PC .. "(TB[" .. CN ..
    "],{\"a\",\"b\"}) if not ok or v~=\"ab\" then " .. names.ADT ..
    "=" .. names.ADT .. "+" .. weight .. " end end"
end

local function pcallLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "do local CP=" .. names.E .. "[" .. keyOf(names, "pcall") ..
    "] local ER=" .. names.E .. "[" .. keyOf(names, "error") .. "] if " ..
    TY .. "(CP)==\"function\" and " .. TY .. "(ER)==\"function\" then " ..
    "local ok,v=" .. PC .. "(function() local s,a,b,c=CP(function() " ..
    "return nil,false,7 end) if s~=true or a~=nil or b~=false or c~=7 then " ..
    "return false end local f,m=CP(function() return ER(\"zq\") end) " ..
    "if f~=false or " .. TY .. "(m)~=\"string\" then return false end " ..
    "local SF=" .. names.ADS .. " and " .. names.ADS .. "[" ..
    keyOf(names, "find") .. "] if " .. TY .. "(SF)==\"function\" and " ..
    "SF(m,\"zq\",1,true)==nil then return false end local marker={} " ..
    "local e,obj=CP(function() return ER(marker) end) return e==false " ..
    "and obj==marker end) if not ok or v~=true then " .. names.ADT .. "=" ..
    names.ADT .. "+" .. weight .. " end end end"
end

local function selectLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "do local SL=" .. names.E .. "[" .. keyOf(names, "select") .. "] if " ..
    TY .. "(SL)==\"function\" then local ok,v=" .. PC .. "(function() " ..
    "if SL(\"#\",1,nil,3)~=3 or SL(\"#\")~=0 then return false end " ..
    "local a,b,c,d=SL(2,1,nil,false,\"tail\") " ..
    "local x,y,z,w=SL(-3,1,nil,false,\"tail\") " ..
    "return a==nil and b==false and c==\"tail\" and d==nil and " ..
    "x==nil and y==false and z==\"tail\" and w==nil and " ..
    "SL(-1,1,nil,false,\"tail\")==\"tail\" end) if not ok or v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end end"
end

-- Hardcoded-globals probes: the emitted code reaches `type`/`pcall` through
-- the locals captured at load, so these checks keep working even when the
-- globals themselves were swapped before the probe runs.
local function charLine(names, weight)
  local S, TY, PC, k = names.ADS, tyOf(names), pcOf(names), keyOf(names, "char")
  return "if " .. S .. " and " .. TY .. "(" .. S .. "[" .. k ..
    "])==\"function\" and " .. TY .. "(" .. S .. "[" .. keyOf(names, "sub") ..
    "])==\"function\" and " .. TY .. "(" .. S .. "[" .. keyOf(names, "rep") ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() return " ..
    S .. "[" .. k .. "](65,66)==\"AB\" and " .. S .. "[" ..
    keyOf(names, "sub") .. "](\"abc\",2,2)==\"b\" and " .. S .. "[" ..
    keyOf(names, "rep") .. "](\"xy\",2)==\"xyxy\" end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end"
end

local function tonumLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local nk, sk = keyOf(names, "tonumber"), keyOf(names, "tostring")
  return "if " .. TY .. "(" .. E .. "[" .. nk .. "])==\"function\" and " ..
    TY .. "(" .. E .. "[" .. sk .. "])==\"function\" then local ok,v=" .. PC ..
    "(function() return " .. E .. "[" .. nk .. "](\"0x10\")==16 and " ..
    E .. "[" .. sk .. "](42)==\"42\" end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end"
end

local function nextpLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local pk, ik, nk = keyOf(names, "pairs"), keyOf(names, "ipairs"),
    keyOf(names, "next")
  return "if " .. TY .. "(" .. E .. "[" .. pk .. "])==\"function\" and " ..
    TY .. "(" .. E .. "[" .. ik .. "])==\"function\" and " ..
    TY .. "(" .. E .. "[" .. nk .. "])==\"function\" then local ok,v=" .. PC ..
    "(function() local t={10,20,x=5} local s=0 for i,x in " .. E .. "[" .. ik ..
    "](t) do s=s+i*x end local c=0 for _ in " .. E .. "[" .. pk ..
    "](t) do c=c+1 end return s==50 and c==3 and " .. E .. "[" .. nk ..
    "]({z=1})==\"z\" end) if ok and v~=true then " .. names.ADT .. "=" ..
    names.ADT .. "+" .. weight .. " end end"
end

local function rawLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local rg, rs, sm = keyOf(names, "rawget"), keyOf(names, "rawset"),
    keyOf(names, "setmetatable")
  return "if " .. TY .. "(" .. E .. "[" .. rg .. "])==\"function\" and " ..
    TY .. "(" .. E .. "[" .. rs .. "])==\"function\" and " ..
    TY .. "(" .. E .. "[" .. sm .. "])==\"function\" then local ok,v=" .. PC ..
    "(function() local t=" .. E .. "[" .. sm .. "]({},{__index=function() " ..
    "return 9 end}) " .. E .. "[" .. rs .. "](t,\"y\",4) return " ..
    E .. "[" .. rg .. "](t,\"x\")==nil and t.x==9 and t.y==4 end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

local function smLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local sm, gm = keyOf(names, "setmetatable"), keyOf(names, "getmetatable")
  return "if " .. TY .. "(" .. E .. "[" .. sm .. "])==\"function\" and " ..
    TY .. "(" .. E .. "[" .. gm .. "])==\"function\" then local ok,v=" .. PC ..
    "(function() local t=" .. E .. "[" .. sm .. "]({},{__metatable=\"K\"}) " ..
    "return " .. E .. "[" .. gm .. "](t)==\"K\" end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end"
end

-- A distinct _G is not necessarily the active environment or its mirror.
local function envidLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local GG = keyOf(names, "_G")
  local sk, pk, tk, bk = keyOf(names, "string"), keyOf(names, "pcall"),
    keyOf(names, "type"), keyOf(names, "byte")
  return "if " .. E .. "[" .. GG .. "]==" .. E .. " then local ok,v=" ..
    PC .. "(function() local g=" .. E .. "[" .. GG .. "] return " .. TY ..
    "(g[" .. sk .. "])==\"table\" and " .. TY .. "(g[" .. sk .. "][" .. bk ..
    "])==\"function\" and " .. TY .. "(g[" .. pk .. "])==\"function\" and " ..
    TY .. "(g[" .. tk .. "])==\"function\" end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

local function mathLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local mk, fk, ak, xk = keyOf(names, "math"), keyOf(names, "floor"),
    keyOf(names, "abs"), keyOf(names, "max")
  return "do local MT=" .. E .. "[" .. mk .. "] if " .. TY ..
    "(MT)==\"table\" and " .. TY .. "(MT[" .. fk .. "])==\"function\" and " .. TY .. "(MT[" .. ak ..
    "])==\"function\" and " .. TY .. "(MT[" .. xk .. "])==\"function\" " ..
    "then local ok,v=" .. PC .. "(function() return MT[" .. fk ..
    "](3.7)==3 and MT[" .. fk .. "](-0.5)==-1 and MT[" .. ak ..
    "](-4)==4 and MT[" .. xk .. "](1,2)==2 end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end end"
end

local function raweqLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local rk = keyOf(names, "rawequal")
  return "do local RQ=" .. E .. "[" .. rk .. "] if " .. TY .. "(RQ)==\"function\" " ..
    "then local ok,v=" .. PC .. "(function() local t={} return RQ(t,t)==true " ..
    "and RQ({},{})==false and RQ(t,{})==false end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end end"
end

local function tableLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local tk, ik = keyOf(names, "table"), keyOf(names, "insert")
  local rk, sk = keyOf(names, "remove"), keyOf(names, "sort")
  return "do local TB=" .. E .. "[" .. tk .. "] if " .. TY ..
    "(TB)==\"table\" and " .. TY .. "(TB[" .. ik .. "])==\"function\" and " .. TY .. "(TB[" .. rk ..
    "])==\"function\" and " .. TY .. "(TB[" .. sk .. "])==\"function\" " ..
    "then local ok,v=" .. PC .. "(function() local t={3,1,2} TB[" .. sk ..
    "](t) TB[" .. ik .. "](t,4) local r=TB[" .. rk .. "](t) return t[1]==1 " ..
    "and t[2]==2 and t[3]==3 and #t==3 and r==4 end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end end"
end

-- Format and pattern-matching integrity: a patched `string.format` rewrites
-- every value a program prints, and a patched `find` would mis-handle the
-- plain flag the runtime itself relies on.
local function formatLine(names, weight)
  local S, TY, PC, k = names.ADS, tyOf(names), pcOf(names), keyOf(names, "format")
  return "if " .. S .. " and " .. TY .. "(" .. S .. "[" .. k ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() return " ..
    S .. "[" .. k .. "](\"%d|%s\",7,\"q\")==\"7|q\" and " ..
    S .. "[" .. k .. "](\"%.2f\",1.5)==\"1.50\" end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

local function findLine(names, weight)
  local S, TY, PC, k = names.ADS, tyOf(names), pcOf(names), keyOf(names, "find")
  return "if " .. S .. " and " .. TY .. "(" .. S .. "[" .. k ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() return " ..
    S .. "[" .. k .. "](\"abc\",\"b\",1,true)==2 and " ..
    S .. "[" .. k .. "](\"a.c\",\".\",1,true)==2 and " ..
    S .. "[" .. k .. "](\"abc\",\"z\",1,true)==nil end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

-- xpcall integrity: success values pass through and the handler receives the
-- exact error object. Wrapped error reporting changes one of those.
local function xpcallLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local xk, ek = keyOf(names, "xpcall"), keyOf(names, "error")
  return "do local XP=" .. E .. "[" .. xk .. "] local ER=" .. E .. "[" .. ek ..
    "] if " .. TY .. "(XP)==\"function\" and " .. TY .. "(ER)==\"function\" then " ..
    "local ok,v=" .. PC .. "(function() local s1,a,b=XP(function() return 3,4 end," ..
    "function(e) return e end) if s1~=true or a~=3 or b~=4 then return false end " ..
    "local mk={} local s2,o=XP(function() ER(mk) end,function(e) return e end) " ..
    "return s2==false and o==mk end) if ok and v~=true then " .. names.ADT ..
    "=" .. names.ADT .. "+" .. weight .. " end end end"
end

-- Pattern callbacks: captures and replacement call count must stay exact.
local function patLine(names, weight)
  local S, TY, PC = names.ADS, tyOf(names), pcOf(names)
  local gk, mk = keyOf(names, "gsub"), keyOf(names, "gmatch")
  return "if " .. S .. " and " .. TY .. "(" .. S .. "[" .. gk ..
    "])==\"function\" and " .. TY .. "(" .. S .. "[" .. mk ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() local n=0 " ..
    "local s=" .. S .. "[" .. gk .. "](\"ab12cd\",\"%d\",function(d) n=n+1 " ..
    "return \"<\"..d..\">\" end) local c=0 for _ in " .. S .. "[" .. mk ..
    "](\"a1b2\",\"%d\") do c=c+1 end " ..
    "return s==\"ab<1><2>cd\" and n==2 and c==2 end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

-- Coroutine round-trip: yielded values, thread status and the wrapped entry
-- point have to behave exactly like the host's own coroutine library.
local function coLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local ck = keyOf(names, "coroutine")
  local cr, cu, cy = keyOf(names, "create"), keyOf(names, "resume"),
    keyOf(names, "yield")
  local cs, cw = keyOf(names, "status"), keyOf(names, "wrap")
  return "do local CO=" .. E .. "[" .. ck .. "] if " .. TY .. "(CO)==\"table\" " ..
    "and " .. TY .. "(CO[" .. cr .. "])==\"function\" and " .. TY .. "(CO[" ..
    cu .. "])==\"function\" and " .. TY .. "(CO[" .. cy .. "])==\"function\" " ..
    "and " .. TY .. "(CO[" .. cs .. "])==\"function\" and " .. TY .. "(CO[" ..
    cw .. "])==\"function\" then local ok,v=" .. PC .. "(function() " ..
    "local th=CO[" .. cr .. "](function(a) local b=CO[" .. cy ..
    "](a+1) return b*2 end) " ..
    "local r1,x1=CO[" .. cu .. "](th,4) local s1=CO[" .. cs .. "](th) " ..
    "local r2,x2=CO[" .. cu .. "](th,6) local s2=CO[" .. cs .. "](th) " ..
    "local w=CO[" .. cw .. "](function() CO[" .. cy .. "](7) return 8 end) " ..
    "local p=w() local q=w() return r1==true and x1==5 and s1==\"suspended\" " ..
    "and r2==true and x2==12 and s2==\"dead\" and p==7 and q==8 end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end end"
end

-- Debug-info shape: same source for two functions in this chunk, non-empty
-- source/short source and a real line range. A stripped recompiled chunk has
-- "=?" and -1 here even if every debug call still succeeds.
local function srcLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  local SK, SS = keyOf(names, "source"), keyOf(names, "short_src")
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB .. "[" ..
    names.AGI .. "])==\"function\" then local f2=function() return 2 end " ..
    "local o1,a=" .. PC .. "(" .. names.ADB .. "[" .. names.AGI .. "]," ..
    names.ADX .. ",\"S\") local o2,b=" .. PC .. "(" .. names.ADB .. "[" ..
    names.AGI .. "],f2,\"S\") if o1 and o2 then local bad=" .. TY ..
    "(a)~=\"table\" or " .. TY .. "(b)~=\"table\" if not bad then bad=" ..
    TY .. "(a[" .. SK .. "])~=\"string\" or #a[" .. SK .. "]==0 or " .. TY ..
    "(b[" .. SK .. "])~=\"string\" or a[" .. SK .. "]~=b[" .. SK .. "] or " ..
    TY .. "(a[" .. names.AGL .. "])~=\"number\" or a[" .. names.AGL ..
    "]<0 or " .. TY .. "(a[" .. SS ..
    "])~=\"string\" end if bad then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end end"
end

-- Length and case mapping. A proxy that rewrites decoded literals on the way
-- out of the string library changes one of these answers.
local function lenLine(names, weight)
  local S, TY, PC = names.ADS, tyOf(names), pcOf(names)
  local lk, uk, wk = keyOf(names, "len"), keyOf(names, "upper"),
    keyOf(names, "lower")
  return "if " .. S .. " and " .. TY .. "(" .. S .. "[" .. lk ..
    "])==\"function\" and " .. TY .. "(" .. S .. "[" .. uk ..
    "])==\"function\" and " .. TY .. "(" .. S .. "[" .. wk ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() return " ..
    S .. "[" .. lk .. "](\"abc\")==3 and " .. S .. "[" .. uk ..
    "](\"aB\")==\"AB\" and " .. S .. "[" .. wk .. "](\"aB\")==\"ab\" end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

-- Vararg unpacking, range form included. `table.unpack` is preferred (5.2+,
-- Luau) and the 5.1 global is the fallback; a host with neither skips.
local function unpackLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local tk, uk = keyOf(names, "table"), keyOf(names, "unpack")
  return "do local TB=" .. E .. "[" .. tk .. "] local UP " .. PC ..
    "(function() UP=TB[" .. uk .. "] end) if " .. TY ..
    "(UP)~=\"function\" then UP=" .. E .. "[" .. uk .. "] end if " ..
    TY .. "(UP)==\"function\" then " ..
    "local ok,v=" .. PC .. "(function() local a,b,c=UP({1,2,3}) " ..
    "if a~=1 or b~=2 or c~=3 then return false end " ..
    "local d,e=UP({1,2,3},2,3) return d==2 and e==3 end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end end"
end

-- Metamethod dispatch round-trip. The keys are char-coded like the rest.
local function metaLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local sm, rg = keyOf(names, "setmetatable"), keyOf(names, "rawset")
  local ik, nk, ck = keyOf(names, "__index"), keyOf(names, "__newindex"),
    keyOf(names, "__call")
  return "if " .. TY .. "(" .. E .. "[" .. sm .. "])==\"function\" and " .. TY ..
    "(" .. E .. "[" .. rg .. "])==\"function\" then local ok,v=" .. PC ..
    "(function() local t=" .. E .. "[" .. sm .. "]({},{[" .. ik .. "]={m=\"?\",k=\"?\"},[" ..
    nk .. "]=function(s,k,x) " .. E .. "[" .. rg .. "](s,\"n\"..k,x) end,[" ..
    ck .. "]=function(_,x) return x*2 end}) " ..
    "if t.m~=\"?\" or t(3)~=6 then return false end t.k=1 " ..
    "return t.nk==1 and t.k==\"?\" end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

-- Collector presence. Only the counting mode is read, so a host that locks the
-- collector still answers; a stub that returns a frozen zero does not.
local function gcLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local gk = keyOf(names, "collectgarbage")
  return "if " .. TY .. "(" .. E .. "[" .. gk .. "])==\"function\" then " ..
    "local ok,v=" .. PC .. "(function() local c=" .. E .. "[" .. gk ..
    "](\"count\") return " .. TY .. "(c)==\"number\" and c>0 end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

-- Range substrings: negative indices, clamping and the single-index negative
-- form. A string spy that only mirrors the positive-argument path fails here.
local function subxLine(names, weight)
  local S, TY, PC, k = names.ADS, tyOf(names), pcOf(names), keyOf(names, "sub")
  return "if " .. S .. " and " .. TY .. "(" .. S .. "[" .. k ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() return " ..
    S .. "[" .. k .. "](\"abcdef\",-3)==\"def\" and " ..
    S .. "[" .. k .. "](\"abc\",5)==\"\" and " ..
    S .. "[" .. k .. "](\"abc\",2,99)==\"bc\" and " ..
    S .. "[" .. k .. "](\"abc\",-2,-2)==\"b\" end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

-- Format width, precision and hex.
local function fmtxLine(names, weight)
  local S, TY, PC, k = names.ADS, tyOf(names), pcOf(names), keyOf(names, "format")
  return "if " .. S .. " and " .. TY .. "(" .. S .. "[" .. k ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() return " ..
    S .. "[" .. k .. "](\"%05.2f\",1.5)==\"01.50\" and " ..
    S .. "[" .. k .. "](\"%x\",255)==\"ff\" end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

-- min/max selection and a fractional floor.
local function minxLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local mk, nk, xk, fk = keyOf(names, "math"), keyOf(names, "min"),
    keyOf(names, "max"), keyOf(names, "floor")
  return "do local MT=" .. E .. "[" .. mk .. "] if " .. TY ..
    "(MT)==\"table\" and " .. TY .. "(MT[" .. nk .. "])==\"function\" and " ..
    TY .. "(MT[" .. xk .. "])==\"function\" and " .. TY .. "(MT[" .. fk ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() return MT[" ..
    nk .. "](4,2,7)==2 and MT[" .. xk .. "](4,2,7)==7 and MT[" .. fk ..
    "](1048576/7)==149796 end) if ok and v~=true then " .. names.ADT ..
    "=" .. names.ADT .. "+" .. weight .. " end end end"
end

-- Global `type` tamper check. The name is decoded from byte codes like the
-- other probe keys, so the site has no grep-able "type" marker.
-- Environment-proxy probes. Names are always read from the load-time
-- capability snapshot (ADB) or from byte-coded keys, so no probe site carries
-- a grep-able `traceback`, `setupvalue`, `getmetatable` or `_G` marker.
local function addrLine(names, weight, er)
  local TY, PC = tyOf(names), pcOf(names)
  local TK = er(keyOf(names, "tostring"))
  return "if " .. TY .. "(" .. TK ..
    ")==\"function\" then local ok,v=" .. PC .. "(function() local F=" .. TK ..
    " local a=F({}) local b=F({}) return " .. TY ..
    "(a)==\"string\" and a~=b end) if ok and v~=true then " .. names.ADT ..
    "=" .. names.ADT .. "+" .. weight .. " end end"
end

local function traceLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB .. "[" ..
    names.ADTR .. "])==\"function\" then local ok,s=" .. PC .. "(" ..
    names.ADB .. "[" .. names.ADTR .. "],\"T\",1) if ok and (" .. TY ..
    "(s)~=\"string\" or #s<=1) then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end"
end

local function setupvLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB .. "[" ..
    names.ADSU .. "])==\"function\" and " .. TY .. "(" .. names.ADB .. "[" ..
    names.ADU .. "])==\"function\" then local ok,v=" .. PC ..
    "(function() local p={} local q={} local f=function() return p end " ..
    names.ADB .. "[" .. names.ADSU .. "](f,1,q) local m=(f()==q) " ..
    names.ADB .. "[" .. names.ADSU .. "](f,1,p) return m and (f()==p) end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

local function loadcLine(names, weight, er)
  local TY, PC = tyOf(names), pcOf(names)
  local LK = er(keyOf(names, "load"))
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB .. "[" ..
    names.AGI .. "])==\"function\" and " .. TY .. "(" .. LK ..
    ")==\"function\" then local ok,bad=" .. PC .. "(function() local r=" ..
    names.ADB .. "[" .. names.AGI .. "](" .. LK ..
    ",\"S\") return " .. TY .. "(r)==\"table\" and r[" .. names.AGW ..
    "]~=\"C\" end) if ok and bad then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end"
end

local function gproxyLine(names, weight, er)
  local TY, PC = tyOf(names), pcOf(names)
  local GM, GK = er(keyOf(names, "getmetatable")), er(keyOf(names, "_G"))
  return "if " .. TY .. "(" .. GM .. ")==\"function\" then local G=" ..
    GK .. " if " .. TY .. "(G)==\"table\" then local ok,bad=" ..
    PC .. "(function() local mt=" .. GM .. "(G) if " .. TY ..
    "(mt)~=\"table\" then return false end local ix=mt[" ..
    keyOf(names, "__index") .. "] local nx=mt[" ..
    keyOf(names, "__newindex") .. "] return " .. TY .. "(ix)==\"function\" or " ..
    TY .. "(nx)==\"function\" end) if ok and bad then " .. names.ADT ..
    "=" .. names.ADT .. "+" .. weight .. " end end end"
end

local function sortxLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local tk, sk = keyOf(names, "table"), keyOf(names, "sort")
  return "do local TB=" .. E .. "[" .. tk .. "] if " .. TY ..
    "(TB)==\"table\" and " .. TY .. "(TB[" .. sk ..
    "])==\"function\" then local ok,v=" .. PC ..
    "(function() local t={3,1,2} TB[" .. sk ..
    "](t,function(a,b) return a>b end) return t[1]==3 and t[2]==2 and " ..
    "t[3]==1 end) if ok and v~=true then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end end"
end

local function insertxLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local tk, ik, rk = keyOf(names, "table"), keyOf(names, "insert"),
    keyOf(names, "remove")
  return "do local TB=" .. E .. "[" .. tk .. "] if " .. TY ..
    "(TB)==\"table\" and " .. TY .. "(TB[" .. ik .. "])==\"function\" and " ..
    TY .. "(TB[" .. rk .. "])==\"function\" then local ok,v=" .. PC ..
    "(function() local t={1,2,3} TB[" .. ik .. "](t,1,9) local r=TB[" .. rk ..
    "](t,1) return t[1]==1 and t[2]==2 and t[3]==3 and r==9 end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end end"
end

local function bytexLine(names, weight)
  local S, TY, PC, k = names.ADS, tyOf(names), pcOf(names), keyOf(names, "byte")
  return "if " .. S .. " and " .. TY .. "(" .. S .. "[" .. k ..
    "])==\"function\" then local ok,v=" .. PC .. "(function() local a,b=" ..
    S .. "[" .. k .. "](\"abc\",-2,-1) return a==98 and b==99 and " ..
    S .. "[" .. k .. "](\"abc\",0)==nil and " .. S .. "[" .. k ..
    "](\"abc\",4)==nil end) if ok and v~=true then " .. names.ADT .. "=" ..
    names.ADT .. "+" .. weight .. " end end"
end

local function lineLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  local CL = keyOf(names, "currentline")
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB .. "[" ..
    names.AGI .. "])==\"function\" then local ok,v=" .. PC ..
    "(function() local i=" .. names.ADB .. "[" .. names.AGI ..
    "](1,\"l\") return " .. TY .. "(i)==\"table\" and " .. TY .. "(i[" .. CL ..
    "])==\"number\" and i[" .. CL .. "]>=0 end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end"
end

local function metalenLine(names, weight)
  local E, TY, PC = names.E, tyOf(names), pcOf(names)
  local rk, sm, lk = keyOf(names, "rawlen"), keyOf(names, "setmetatable"),
    keyOf(names, "__len")
  return "do local RL=" .. E .. "[" .. rk .. "] local SM=" .. E .. "[" .. sm ..
    "] if " .. TY .. "(RL)==\"function\" and " .. TY .. "(SM)==\"function\" " ..
    "then local ok,v=" .. PC .. "(function() local t=SM({},{[" .. lk ..
    "]=function() return 99 end}) return #t==99 and RL(t)==0 end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end end"
end

-- Selectively test Luau language invariants without modifying the host.
-- Keys are reconstructed at runtime, and optional/proxied libraries are read
-- through the protected capability helper when present.
local function luauRead(names, root, key)
  local k = keyOf(names, key)
  if names.ADY then return names.ADY .. "(" .. root .. "," .. k .. ")" end
  return "(" .. root .. " and " .. root .. "[" .. k .. "])"
end
local function packxLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  local t = luauRead(names, names.E, "table")
  local p = luauRead(names, "TT", "pack")
  return "do local TT=" .. t .. " local PK=" .. p ..
    " if " .. TY .. "(PK)==\"function\" then local ok,v=" .. PC ..
    "(function() local a=PK(\"a\",nil,\"z\") return " .. TY ..
    "(a)==\"table\" and a.n==3 and a[1]==\"a\" and a[2]==nil and a[3]==\"z\" end)" ..
    " if ok and v~=true then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end end"
end
local function freezexLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  local t = luauRead(names, names.E, "table")
  local f = luauRead(names, "TT", "freeze")
  local i = luauRead(names, "TT", "isfrozen")
  return "do local TT=" .. t .. " local F=" .. f .. " local I=" .. i ..
    " if " .. TY .. "(F)==\"function\" and " .. TY .. "(I)==\"function\" then " ..
    "local ok,v=" .. PC .. "(function() local a=F({marker=1}) if " .. TY ..
    "(a)~=\"table\" or not I(a) then return false end " ..
    "local wrote=" .. PC .. "(function() a.marker=2 end) " ..
    "return not wrote and a.marker==1 end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end end"
end
local function bufferxLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  local t = luauRead(names, names.E, "buffer")
  local c = luauRead(names, "BB", "create")
  local w = luauRead(names, "BB", "writeu16")
  local r = luauRead(names, "BB", "readu16")
  local l = luauRead(names, "BB", "len")
  return "do local BB=" .. t .. " local C=" .. c .. " local W=" .. w ..
    " local R=" .. r .. " local L=" .. l ..
    " if " .. TY .. "(C)==\"function\" and " .. TY .. "(W)==\"function\" and " ..
    TY .. "(R)==\"function\" and " .. TY .. "(L)==\"function\" then " ..
    "local ok,v=" .. PC .. "(function() local a=C(4) W(a,1,48879) " ..
    "return L(a)==4 and R(a,1)==48879 end) " ..
    "if ok and v~=true then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end end"
end
local function infoxLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  local d = luauRead(names, names.E, "debug")
  local info = luauRead(names, "DD", "info")
  return "do local DD=" .. d .. " local IF=" .. info ..
    " if " .. TY .. "(IF)==\"function\" then local ok,v=" .. PC ..
    "(function() local f=function(x) return x end " ..
    "return IF(f,\"f\")==f end) if ok and v~=true then " ..
    names.ADT .. "=" .. names.ADT .. "+" .. weight .. " end end end"
end

local function typeLine(names, weight)  local TY, PC = tyOf(names), pcOf(names)  return "local GK=" .. names.E .. "[" .. names.DM .. "(" .. codes("type") ..
    ")] if GK~=nil then local ok,v=" .. PC .. "(function() return GK(1)==\"number\" " ..
    "and GK(\"x\")==\"string\" and GK({})==\"table\" and GK(nil)==\"nil\" " ..
    "and GK(true)==\"boolean\" end) if ok and v~=true then " .. names.ADT ..
    "=" .. names.ADT .. "+" .. weight .. " end end"
end

local function dumpLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "if " .. names.ADS .. " and " .. TY .. "(" .. names.ADS ..
    "[" .. names.AGD .. "])==\"function\" then local ok,a=" .. PC .. "(" .. names.ADS ..
    "[" .. names.AGD .. "]," ..
    names.ADX .. ") local ok2,b=" .. PC .. "(" .. names.ADS .. "[" .. names.AGD .. "]," ..
    names.ADX .. ") if ok and ok2 and (" .. TY .. "(a)~=\"string\" or #a==0 or " ..
    "a~=b) then " .. names.ADT .. "=" .. names.ADT .. "+" .. weight ..
    " end end"
end

-- Deeper debug-library checks. `getupvalue` must still report the captured
-- table, and the registry must still expose a string library under _LOADED; a
-- lying debug API or a wiped registry breaks one of those.
local function upvLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB .. "[" .. names.ADU ..
    "])==\"function\" then local bx={1} local f=function() return bx[1] end " ..
    "local ok,nm,v=" .. PC .. "(" .. names.ADB .. "[" .. names.ADU .. "],f,1) " ..
    "if ok and v~=bx then " .. names.ADT .. "=" .. names.ADT .. "+" ..
    weight .. " end end"
end

local function regLine(names, weight)
  local TY, PC = tyOf(names), pcOf(names)
  return "if " .. names.ADB .. " and " .. TY .. "(" .. names.ADB .. "[" .. names.AGR ..
    "])==\"function\" then local ok,r=" .. PC .. "(" .. names.ADB .. "[" .. names.AGR ..
    "]) local bad=(ok and " .. TY .. "(r)~=\"table\") if ok and not bad then local L=r[" ..
    names.ADLD .. "] if " .. TY .. "(L)==\"table\" then bad=(" .. TY .. "(L[" .. names.ADR ..
    "])~=\"table\") end end if bad then " .. names.ADT .. "=" .. names.ADT ..
    "+" .. weight .. " end end"
end

-- Emits the probe block. `names` carries ADT/ADB/ADX/ADS from vmgen.
function Antidebug.prologue(names, cfg)
  local keys = {
    { names.ADG, "debug" }, { names.ADR, "string" },
    { names.AGH, "gethook" }, { names.AGI, "getinfo" },
    { names.AGW, "what" }, { names.AGL, "linedefined" },
    { names.AGF, "func" }, { names.AGD, "dump" },
    { names.ADU, "getupvalue" }, { names.AGR, "getregistry" },
    { names.AGS, "sethook" },
    { names.ADTR, "traceback" }, { names.ADSU, "setupvalue" },
    { names.ADLD, "_LOADED" },
  }
  local lines = {
    "local " .. names.ADT .. "=0",
    "local " .. names.ADX .. "=function() return 1 end",
  }
  if names.ADH then lines[#lines + 1] = "local " .. names.ADH .. "=0" end
  if names.ADN then lines[#lines + 1] = "local " .. names.ADN .. "=0" end
  if names.ADZ then lines[#lines + 1] = "local " .. names.ADZ .. "=0" end
  for i = 1, #keys do
    if keys[i][1] then
      lines[#lines + 1] = "local " .. keys[i][1] .. "=" .. names.DM .. "(" ..
        codes(keys[i][2]) .. ")"
    end
  end
  local function dkey(text) return names.DM .. "(" .. codes(text) .. ")" end
  -- Optional libraries may be proxies whose __index rejects keys, and a denied
  -- read must mean "not available", never "the chunk raises". The capability
  -- snapshot below reads every entry the probes touch through one protected
  -- helper and stores only the values that answered, so the shipped probe code
  -- never indexes the host table directly. Without the extra names (direct
  -- callers and tests) the plain capture is kept.
  local safe = names.ADY and names.ADB0 and names.ADS0
  if safe then
    local TY, PC = tyOf(names), pcOf(names)
    lines[#lines + 1] = "local " .. names.ADY .. "=function(t,k) if " .. TY ..
      "(t)~=\"table\" then return nil end local o,v=" .. PC ..
      "(function() return t[k] end) if o then return v end end"
    lines[#lines + 1] = "local " .. names.ADB0 .. "=" .. names.ADY ..
      "(" .. names.E .. "," .. names.ADG .. ")"
    local fields = {}
    for _, k in ipairs({ names.AGH, names.AGI, names.ADU, names.AGR,
        names.AGS, names.ADTR, names.ADSU }) do
      if k then
        fields[#fields + 1] = names.ADB .. "[" .. k .. "]=" .. names.ADY ..
          "(" .. names.ADB0 .. "," .. k .. ")"
      end
    end
    lines[#lines + 1] = "local " .. names.ADB .. "={} if " .. names.ADB0 ..
      " then " .. table.concat(fields, " ") .. " end"
    lines[#lines + 1] = "local " .. names.ADS0 .. "=" .. names.ADY ..
      "(" .. names.E .. "," .. names.ADR .. ")"
    local sfields = {}
    local strKeys = { "dump", "byte", "char", "sub", "rep", "find",
      "format", "gsub", "gmatch", "len", "upper", "lower" }
    for i = 1, #strKeys do
      local e = dkey(strKeys[i])
      sfields[#sfields + 1] = names.ADS .. "[" .. e .. "]=" .. names.ADY ..
        "(" .. names.ADS0 .. "," .. e .. ")"
    end
    lines[#lines + 1] = "local " .. names.ADS .. "={} if " .. names.ADS0 ..
      " then " .. table.concat(sfields, " ") .. " end"
  else
    lines[#lines + 1] = "local " .. names.ADB .. "=" .. names.E ..
      "[" .. names.ADG .. "]"
    lines[#lines + 1] = "local " .. names.ADS .. "=" .. names.E ..
      "[" .. names.ADR .. "]"
  end
  -- Executor hosts run their own debug hooks and may wrap dump/load, so the
  -- ambiguous probes are demoted to weight 1 there and the threshold rises by
  -- one. A normal executor session therefore never deviates; a host that
  -- tampers with the core libraries still trips on its own. `syn` is a table on
  -- several executors, so it counts either way; a denied read counts as absent.
  local exKeys = Antidebug.EXECUTOR_KEYS
  local TYEX = tyOf(names)
  local exParts = {}
  for i = 1, #exKeys do
    local read = safe and (names.ADY .. "(" .. names.E .. "," ..
      dkey(exKeys[i]) .. ")") or (names.E .. "[" .. dkey(exKeys[i]) .. "]")
    if exKeys[i] == "syn" then
      exParts[i] = "(" .. TYEX .. "(" .. read .. ")==\"table\" or " ..
        TYEX .. "(" .. read .. ")==\"function\")"
    else
      exParts[i] = TYEX .. "(" .. read .. ")==\"function\""
    end
  end
  -- Stored as 0/1, never as a boolean: the integrity tick and the capability
  -- snapshot both test it against 0, and Lua treats 0 as truthy, so a boolean
  -- here silently disabled the runtime anti-debug pass.
  lines[#lines + 1] = "local " .. names.ADE .. "=(" ..
    table.concat(exParts, " or ") .. ") and 1 or 0"
  local function amb(w) return "(" .. names.ADE .. "==1 and 0 or " .. w .. ")" end
  local function soft(w) return "(" .. names.ADE .. "==1 and 1 or " .. w .. ")" end
  -- Always-weak probes: executor demotes to zero, every other host caps at one.
  local function weak(w)
    local v = tonumber(w) or 0
    if v > 1 then v = 1 end
    return "(" .. names.ADE .. "==1 and 0 or " .. v .. ")"
  end
  local function raw(w) return tostring(w) end
  -- Global reads for the environment-proxy probes go through the same
  -- protected read helper the snapshot uses when it is available: a proxy that
  -- denies one entry yields nil (the probe is skipped) instead of raising
  -- inside the probe block.
  local function er(expr) return names.E .. "[" .. expr .. "]" end
  if safe then
    er = function(expr) return names.ADY .. "(" .. names.E .. "," .. expr .. ")" end
  end
  local body = {}
  for i = 1, #cfg.probes do
    local p = cfg.probes[i]
    if p == "hook" then
      body[#body + 1] = hookLine(names, amb(Antidebug.HOOK_WEIGHT))
    elseif p == "what" then body[#body + 1] = whatLine(names, amb(cfg.weights.what))
    elseif p == "func" then body[#body + 1] = funcLine(names, amb(cfg.weights.func))
    elseif p == "dump" then body[#body + 1] = dumpLine(names, amb(cfg.weights.dump))
    elseif p == "byte" then body[#body + 1] = byteLine(names, raw(cfg.weights.byte))
    elseif p == "concat" then
      body[#body + 1] = concatLine(names, raw(cfg.weights.concat))
    elseif p == "pcall" then
      body[#body + 1] = pcallLine(names, raw(cfg.weights.pcall))
    elseif p == "select" then
      body[#body + 1] = selectLine(names, raw(cfg.weights.select))
    elseif p == "type" then
      body[#body + 1] = typeLine(names, amb(cfg.weights.type))
    elseif p == "upv" then
      body[#body + 1] = upvLine(names, amb(cfg.weights.upv))
    elseif p == "reg" then
      body[#body + 1] = regLine(names, amb(cfg.weights.reg))
    elseif p == "char" then
      body[#body + 1] = charLine(names, soft(cfg.weights.char))
    elseif p == "tonum" then
      body[#body + 1] = tonumLine(names, soft(cfg.weights.tonum))
    elseif p == "nextp" then
      body[#body + 1] = nextpLine(names, soft(cfg.weights.nextp))
    elseif p == "raw" then
      body[#body + 1] = rawLine(names, soft(cfg.weights.raw))
    elseif p == "sm" then
      body[#body + 1] = smLine(names, soft(cfg.weights.sm))
    elseif p == "envid" then
      body[#body + 1] = envidLine(names, soft(cfg.weights.envid))
    elseif p == "mathl" then
      body[#body + 1] = mathLine(names, soft(cfg.weights.mathl))
    elseif p == "raweq" then
      body[#body + 1] = raweqLine(names, soft(cfg.weights.raweq))
    elseif p == "tablel" then
      body[#body + 1] = tableLine(names, soft(cfg.weights.tablel))
    elseif p == "format" then
      body[#body + 1] = formatLine(names, soft(cfg.weights.format))
    elseif p == "find" then
      body[#body + 1] = findLine(names, soft(cfg.weights.find))
    elseif p == "xpcall" then
      body[#body + 1] = xpcallLine(names, amb(cfg.weights.xpcall))
    elseif p == "pat" then
      body[#body + 1] = patLine(names, soft(cfg.weights.pat))
    elseif p == "co" then
      body[#body + 1] = coLine(names, amb(cfg.weights.co))
    elseif p == "src" then
      body[#body + 1] = srcLine(names, amb(cfg.weights.src))
    elseif p == "len" then
      body[#body + 1] = lenLine(names, soft(cfg.weights.len))
    elseif p == "unpack" then
      body[#body + 1] = unpackLine(names, soft(cfg.weights.unpack))
    elseif p == "meta" then
      body[#body + 1] = metaLine(names, soft(cfg.weights.meta))
    elseif p == "gc" then
      body[#body + 1] = gcLine(names, soft(cfg.weights.gc))
    elseif p == "subx" then
      body[#body + 1] = subxLine(names, soft(cfg.weights.subx))
    elseif p == "fmtx" then
      body[#body + 1] = fmtxLine(names, soft(cfg.weights.fmtx))
    elseif p == "minx" then
      body[#body + 1] = minxLine(names, soft(cfg.weights.minx))
    elseif p == "addr" then
      body[#body + 1] = addrLine(names, soft(cfg.weights.addr), er)
    elseif p == "trace" and names.ADTR then
      body[#body + 1] = traceLine(names, amb(cfg.weights.trace))
    elseif p == "setupv" and names.ADSU and names.ADU then
      body[#body + 1] = setupvLine(names, amb(cfg.weights.setupv))
    elseif p == "loadc" then
      body[#body + 1] = loadcLine(names, weak(cfg.weights.loadc), er)
    elseif p == "gproxy" then
      body[#body + 1] = gproxyLine(names, amb(cfg.weights.gproxy), er)
    elseif p == "sortx" then
      body[#body + 1] = sortxLine(names, soft(cfg.weights.sortx))
    elseif p == "insertx" then
      body[#body + 1] = insertxLine(names, soft(cfg.weights.insertx))
    elseif p == "bytex" then
      body[#body + 1] = bytexLine(names, soft(cfg.weights.bytex))
    elseif p == "line" then
      body[#body + 1] = lineLine(names, amb(cfg.weights.line))
    elseif p == "metalen" then
      body[#body + 1] = metalenLine(names, weak(cfg.weights.metalen))
    elseif p == "packx" then
      body[#body + 1] = packxLine(names, soft(cfg.weights.packx))
    elseif p == "freezex" then
      body[#body + 1] = freezexLine(names, soft(cfg.weights.freezex))
    elseif p == "bufferx" then
      body[#body + 1] = bufferxLine(names, soft(cfg.weights.bufferx))
    elseif p == "infox" then
      body[#body + 1] = infoxLine(names, amb(cfg.weights.infox))
    end
  end
  -- Dynamic probe-shape chain. Unlike the old static additive check, the
  -- expected value now depends on a runtime clock slot. Each probe advances
  -- a noncommutative polynomial recurrence; deleting even one probe changes
  -- the chain. This is tamper evidence, NOT a secret or authentication key.
  -- Compute two coefficients at build time so runtime verification is O(1)
  -- after the startup probes. Every probe is still run exactly once.
  local shape = nil
  if names.ADN then
    local modulus, multiplier = 1000003, 65599
    local base = (cfg.seed or 0) % 251
    local v0, v1 = 0, 0
    local slot = names.ADN .. "_slot"
    -- Clock may not exist in Luau or an isolated Lua sandbox. An unavailable
    -- clock is not evidence of tampering; use a deterministic runtime slot,
    -- avoiding a compatibility regression or an always-failing loader.
    local PC = pcOf(names)
    local TY = tyOf(names)
    local clock = "local " .. slot .. "=0 do local ok,cv=" .. PC ..
      "(function() local o=" .. names.E .. "[" .. names.DM .. "(" ..
      codes("os") .. ")] if " .. TY .. "(o)==\"table\" and " ..
      TY .. "(o.clock)==\"function\" then return o.clock() end end) " ..
      "if ok and " .. TY .. "(cv)==\"number\" and cv==cv and " ..
      "cv~=math.huge and cv~=-math.huge and cv>=0 and cv<10000000 then " ..
      slot .. "=math.floor(cv*1000)%97 end end"
    lines[#lines+1] = clock
    for i = 1, #cfg.probes do
      local token = ((i * 97 + base) % 401) + 7
      local weight = ((i * 29 + base) % 11) + 1
      v0 = (v0 * multiplier + token) % modulus
      v1 = (v1 * multiplier + weight) % modulus
      body[i] = names.ADN .. "=(" .. names.ADN .. "*" .. multiplier ..
        "+" .. token .. "+" .. slot .. "*" .. weight .. ")%" ..
        modulus .. " " .. body[i]
    end
    shape = "if " .. names.ADN .. "~=(" .. v0 .. "+" .. slot ..
      "*" .. v1 .. ")%" .. modulus .. " then " .. names.ADT ..
      "=" .. names.ADT .. "+" .. cfg.threshold .. " end"
  end
  for i = 1, #body do lines[#lines + 1] = body[i] end
  if shape then lines[#lines + 1] = shape end
  -- Best-effort, one-shot count-hook self-test.  This is intentionally a
  -- compatibility-gated check, not a test that every host supports count hooks: a profiler, Luau
  -- host, sandbox or custom debug shim may legitimately reject count hooks.
  -- Never replace an existing hook (including profilers); only install the
  -- temporary hook if gethook confirms this thread has no active hook.
  -- Always restore the nil baseline before scoring any result.  The hook is
  -- expected to fire; fired > 0 means the test worked, NOT an attack.
  -- A verified but never-triggered hook adds 2, reaching the usual threshold.
  if names.ADB and names.ADT then
    local DB = names.ADB
    local PT = pcOf(names)
    local TY = tyOf(names)
    local hookSelfTest =
      "do local D=" .. DB .. " if " .. TY .. "(D)==\"table\" then " ..
      "local st,gh=D.sethook,D.gethook " ..
      "if " .. TY .. "(st)==\"function\" and " ..
      TY .. "(gh)==\"function\" then " ..
      "local ok0,h0=" .. PT .. "(gh) if ok0 and h0==nil then " ..
      "local fired=0 local cb=function() fired=fired+1 end " ..
      "local okSet,setResult=" .. PT .. "(st,cb,\"\",1) " ..
      "if okSet and setResult~=false then " ..
      "local okSeen,seen=" .. PT .. "(gh) " ..
      "local okRun,sum=" .. PT .. "(function() local x=0 for j=1,16 do x=x+j end return x end) " ..
      "local okRestore=" .. PT .. "(st) " ..
      "if okSeen and seen==cb and okRun and sum==136 and okRestore and fired==0 then " ..
      names.ADT .. "=" .. names.ADT .. "+2 end " ..
      "end end end end end"
    lines[#lines + 1] = hookSelfTest
  end
  -- Ambiguous and soft probes are already demoted above when the host looks
  -- like an executor, so a healthy session's own hook cannot trip this. The
  -- hard probes (library behaviour, wrapped pcall/select) keep their weight on
  -- an executor and still deviate a tampered one, matching Antidebug.probe.
  lines[#lines + 1] = "if " .. names.ADT .. ">=" .. cfg.threshold .. " then " ..
    names.ADT .. "=1 else " .. names.ADT .. "=0 end"
  return lines
end

-- Emitted inside the integrity tick (once per ~3000 dispatches). It advances a
-- two-hit latch only when no load-time probe fired and the host did not look
-- like an executor: a debug hook installed after the chunk started is the one
-- instruction-trace shape the load-time probes cannot see. Consecutive hits
-- are required, so a momentary hook from an unrelated tool does not trip it,
-- and the integrity layer turns a confirmed latch into its usual nil-index
-- failure. Hosts without a functioning gethook (autofix sandbox, Luau) stay
-- at zero because the call would return nil anyway.
function Antidebug.lateCheck(names)
  if not (names.ADB and names.AGH and names.ADE and names.ADH) then
    return ""
  end
  local TY = tyOf(names)
  local PC = names.G3 or "pcall"
  -- A profiler may attach/detach hooks at any point.  Do not escalate
  -- hook presence into the integrity latch: only deterministic behaviour
  -- regressions (below) can contribute.  No debug state is mutated here.
  local parts = {}
  -- Periodic library re-checks. The load-time probe block runs once; these
  -- re-run the two cheapest behavioural checks on every integrity tick, so a
  -- wrapper installed after load is caught while the script keeps running.
  -- Only the non-executor, non-deviated path is touched, and a failure is the
  -- same two-hit late latch the hook check uses. Both calls are ordinary
  -- library reads on a healthy host, so they cost nothing measurable per tick.
  if names.DM and names.ADS and names.ADB then
    local BK = keyOf(names, "byte")
    parts[#parts + 1] = "if " .. names.ADT .. "==0 and " .. names.ADE ..
      "==0 and " .. names.ADS .. " and " .. TY .. "(" .. names.ADS .. "[" ..
      BK .. "])==\"function\" then local ok,v=" .. PC .. "(" .. names.ADS ..
      "[" .. BK .. "],\"A\") if not ok or v~=65 then " .. names.ADH ..
      "=" .. names.ADH .. "+2 end end"
    local TK, CK = keyOf(names, "table"), keyOf(names, "concat")
    parts[#parts + 1] = "if " .. names.ADT .. "==0 and " .. names.ADE ..
      "==0 then local TB=" .. names.E .. "[" .. TK .. "] if " .. TY ..
      "(TB)==\"table\" and " .. TY .. "(TB[" .. CK .. "])==\"function\" then " ..
      "local ok,v=" .. PC .. "(TB[" .. CK .. "],{\"a\",\"b\"}) if not ok or " ..
      "v~=\"ab\" then " .. names.ADH .. "=" .. names.ADH .. "+2 end end end"
  end
  -- Environment re-check. An environment logger installed after load has one
  -- of two cheap-to-see tells: it sanitizes tostring output (two fresh tables
  -- print the same string) or it proxies _G with a function-valued
  -- __index/__newindex. Both are re-tested here, through the same protected
  -- read helper the load-time probes use. Gated on ADY so a build without the
  -- capability snapshot (direct callers, tests) emits nothing, and on the
  -- clean-session flags so an executor or an already-deviated run is untouched.
  if names.ADY and names.DM and names.E and names.ADB and names.ADS then
    local function k(text) return names.DM .. "(" .. codes(text) .. ")" end
    parts[#parts + 1] = "if " .. names.ADT .. "==0 and " .. names.ADE ..
      "==0 then local ok,v=" .. PC .. "(function() local F=" .. names.ADY ..
      "(" .. names.E .. "," .. k("tostring") .. ") if " .. TY ..
      "(F)~=\"function\" then return true end local a=F({}) local b=F({}) " ..
      "return " .. TY .. "(a)==\"string\" and a~=b end) " ..
      "if not ok or v~=true then " .. names.ADH .. "=" .. names.ADH ..
      "+2 end end"
    parts[#parts + 1] = "if " .. names.ADT .. "==0 and " .. names.ADE ..
      "==0 then local ok,bad=" .. PC .. "(function() local GM=" .. names.ADY ..
      "(" .. names.E .. "," .. k("getmetatable") .. ") local G=" .. names.ADY ..
      "(" .. names.E .. "," .. k("_G") .. ") if " .. TY .. "(GM)~=\"function\" " ..
      "or " .. TY .. "(G)~=\"table\" then return false end local mt=GM(G) if " ..
      TY .. "(mt)~=\"table\" then return false end return " .. TY .. "(mt[" ..
      k("__index") .. "])==\"function\" or " .. TY .. "(mt[" ..
      k("__newindex") .. "])==\"function\" end) if ok and bad then " ..
      names.ADH .. "=" .. names.ADH .. "+2 end end"
  end
  -- Rotating late re-checks: every tick verifies one library family chosen by
  -- a counter, so a wrapper installed after load is caught within a handful of
  -- ticks instead of only at load time. Each check is read-only and
  -- deterministic; a missing library skips, a wrong answer is a definitive
  -- tamper hit (+2). Gated on the same clean, non-executor session as the
  -- other late probes.
  if names.ADZ and names.ADT and names.ADE and names.ADH and names.DM and
     names.E then
    local function k(text) return names.DM .. "(" .. codes(text) .. ")" end
    local S = names.E .. "[" .. k("string") .. "]"
    local function check(body)
      return "local ok,v=" .. PC .. "(function() local S=" .. S .. " if " .. TY ..
        "(S)~=\"table\" then return true end " .. body .. " end) " ..
        "if ok and v~=true then " .. names.ADH .. "=" .. names.ADH .. "+2 end"
    end
    local fmt = check("local F=S[" .. k("format") ..
      "] if " .. TY .. "(F)~=\"function\" then return true end " ..
      "return F(\"%05.2f\",1.5)==\"01.50\"")
    local fnd = check("local F=S[" .. k("find") ..
      "] if " .. TY .. "(F)~=\"function\" then return true end " ..
      "return F(\"a.c\",\".\",1,true)==2 and F(\"abc\",\"z\",1,true)==nil")
    local gsb = check("local G=S[" .. k("gsub") ..
      "] if " .. TY .. "(G)~=\"function\" then return true end local n=0 " ..
      "local s=G(\"ab12\",\"%d\",function(d) n=n+1 return d end) " ..
      "return n==2 and s==\"ab12\"")
    local sel = check("local SL=" .. names.E .. "[" .. k("select") .. "] if " ..
      TY .. "(SL)~=\"function\" then return true end " ..
      "local a,b,c=SL(2,1,nil,false,\"t\") return a==nil and b==false " ..
      "and c==\"t\" and SL(\"#\",1,nil,3)==3")
    parts[#parts + 1] = "if " .. names.ADT .. "==0 and " .. names.ADE ..
      "==0 then " .. names.ADZ .. "=" .. names.ADZ .. "%4+1 " ..
      "if " .. names.ADZ .. "==1 then " .. fmt ..
      " elseif " .. names.ADZ .. "==2 then " .. fnd ..
      " elseif " .. names.ADZ .. "==3 then " .. gsb ..
      " else " .. sel .. " end end"
  end
  return concat(parts, " ")
end

-- Runtime deviation: rotate the letters of every value-only string constant
-- (case preserved, z/Z wraps to a/A) while leaving digits, punctuation and
-- control bytes untouched. Global and field names are excluded by vmgen (a
-- corrupted name would become a nil lookup), and the rotation is guarded so a
-- session without the string or table library keeps running instead of
-- raising.
--
-- Serialized M6 pools are rotated per ciphertext blob only: the entry headers
-- carry key/plaintext/blob lengths that the generated decoder trusts, and a
-- rotated header made the decoder raise after the load-time checks (the
-- swallow-all pcall then turned that into a silent no-op). Blob bytes are
-- pure data, so the decoder still runs and the program silently computes on
-- wrong constants.
--
-- Every blob byte is shifted, not just letters: a short XOR blob is raw
-- ciphertext and often holds no ASCII letters at all, so a letters-only
-- rotation left those constants untouched (and a hooked session produced the
-- clean output). The shift keeps the blob length and never touches the
-- headers, so entry boundaries and the decoder's offset walk stay valid; the
-- per-scheme decoders either map bytes 1:1 (xor/feistel/lookup) or look up a
-- fixed-size alphabet (base64/huffman), all of which accept any byte.
local function serializeLists(lists)
  local parts = {}
  for pi = 1, #lists do
    local idx = {}
    for i = 1, #lists[pi] do idx[i] = tostring(lists[pi][i]) end
    parts[pi] = "{" .. concat(idx, ",") .. "}"
  end
  return "{" .. concat(parts, ",") .. "}"
end

local function serializePools(pools, count)
  local parts = {}
  for pi = 1, count do
    local items = {}
    local list = (pools and pools[pi]) or {}
    for i = 1, #list do
      items[i] = "{" .. list[i].index .. ",{" ..
        concat(list[i].ranges, ",") .. "}}"
    end
    parts[pi] = "{" .. concat(items, ",") .. "}"
  end
  return "{" .. concat(parts, ",") .. "}"
end

local function serializeCounts(counts)
  if not counts then return "{}" end
  local parts = {}
  for pi = 1, #counts do parts[pi] = tostring(counts[pi]) end
  return "{" .. concat(parts, ",") .. "}"
end

function Antidebug.deviation(names, safe, pools, counts, salt)
  local T, S, P, Q, W = names.ADT, names.ADS, names.P, names.ADQ, names.ADW
  local E, R = names.E, names.ADRST
  -- Build-specific offset mixed into every rotation below. Digits are never
  -- rotated, so a tripped run still shows plausible numbers while every
  -- string it prints is wrong in a way the next build will not repeat.
  local BS = (tonumber(salt) or 0) % 192
  -- Constant pools are sealed per prototype and open lazily, so `#k` is not a
  -- reliable length before the first read. The emitter knows every pool size
  -- and passes it in; the fallback keeps direct callers working.
  local KN = names.KN or (P .. "c")
  -- Hardcoded library handles: the rotation and the restore hook run on the
  -- values copied at load, so a hook installed after the chunk started cannot
  -- redirect them to a no-op.
  local SB = names.B1 or (S .. ".byte")
  local SC = names.C1 or (S .. ".char")
  local SU = names.U1 or (S .. ".sub")
  local TC = names.C2 or ((names.G2 or (E .. ".table")) .. ".concat")
  local PC = names.G3 or (E .. ".pcall")
  local TY = names.G4 or (E .. ".type")
  -- The constant pool field is renamed per build like every other prototype
  -- field; the fallback keeps direct callers working.
  local KF = names.PKK or "k"
  -- BK holds the original strings (Lua interned strings, so this is a
  -- reference copy, not a byte copy). The entry retries on the clean runtime
  -- when a corrupted API string makes the deviated run raise.
  return {
    "local " .. Q .. "=" .. serializeLists(safe or {}),
    "local " .. W .. "=" .. serializePools(pools, #(safe or {})),
    "local " .. KN .. "=" .. serializeCounts(counts),
    "local BK={}",
    "local " .. R,
    "if " .. T .. "==1 and " .. S .. " and " .. TC .. " and " .. TY .. "(" .. PC ..
      ")==\"function\" then",
    "(" .. PC .. ")(function()",
    "for pi=1,#" .. P .. " do local k=" .. P .. "[pi]." .. KF .. " local j=" ..
      Q .. "[pi]",
    "local bk=BK[pi] if not bk then bk={} BK[pi]=bk end",
    "for x=1,#j do local i=j[x] local s=k[i]",
    "if " .. TY .. "(s)==\"string\" and #s>0 then bk[i]=s local b={}",
    "local rt=" .. SB .. "(s,1)%26+1",
    "local dr=" .. SB .. "(s,#s)%2*2-1",
    "for z=1,#s do local v=" .. SB .. "(s,z)",
    "if v<48 or v>57 then",
    "if v>=97 and v<=122 then v=97+(v-97+dr*rt+" .. BS .. ")%26 elseif v>=65 " ..
      "and v<=90 then v=65+(v-65+dr*rt+" .. BS .. ")%26 else v=(v+dr*(rt+" ..
      BS .. "))%256 end end",
    "b[z]=" .. SC .. "(v) end",
    "k[i]=" .. TC .. "(b) end end end",
    "for pi=1,#" .. P .. " do local k=" .. P .. "[pi]." .. KF .. " local j=" ..
      W .. "[pi]",
    "local bk=BK[pi] if not bk then bk={} BK[pi]=bk end",
    "for x=1,#j do local q=j[x] local s=k[q[1]]",
    "if " .. TY .. "(s)==\"string\" and #s>0 then local b={} local r=q[2]",
    "bk[q[1]]=s",
    "for z=1,#s do b[z]=" .. SU .. "(s,z,z) end",
    "for y=1,#r,2 do local lo=r[y] local hi=r[y+1]",
    "local rt=" .. SB .. "(s,lo)%251+1",
    "for z=lo,hi do local v=(" .. SB .. "(s,z)+rt+" .. BS .. ")%256",
    "b[z]=" .. SC .. "(v) end end",
    "k[q[1]]=" .. TC .. "(b) end end end",
    R .. "=function() for pi=1,#" .. P .. " do local k=" .. P .. "[pi]." .. KF ..
      " local bk=BK[pi] if bk then local cn=" .. KN ..
      "[pi] if not cn then cn=#k end for i=1,cn do local s=bk[i] " ..
      "if s then k[i]=s end end end end end",
    "end)",
    "end",
  }
end

-- FNV-1a32 of a string, used by tests to fingerprint the deviation.
Antidebug._probeFn = probeFn

return Antidebug
