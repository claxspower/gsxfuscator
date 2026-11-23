-- vmgen.lua -- emits the self-contained Lua file: randomized opcodes, decoy
-- opcodes, shuffled dispatcher, string decoder, integrity and anti-debug code.
local U = require("src.util")
local Tamper = require("src.tamper")

local VMGen = {}

local OPS = {
  "LOADK", "LOADBOOL", "LOADNIL", "LOADSTR", "MOVE",
  "GETGLOBAL", "SETGLOBAL", "GETUPVAL", "SETUPVAL",
  "GETTABLE", "GETFIELD", "SETTABLE", "SETFIELD", "SELF",
  "NEWTABLE", "SETLIST", "SETIDX",
  "ADD", "SUB", "MUL", "DIV", "MOD", "POW", "IDIV", "CONCAT",
  "UNM", "NOT", "LEN", "BAND", "BOR", "BXOR", "BNOT", "SHL", "SHR",
  "EQ", "NE", "LT", "LE", "GT", "GE",
  "JMP", "JMPF", "JMPT",
  "CALL", "RETURN", "CLOSURE", "VARARG",
  "FORPREP", "FORLOOP", "TFORCALL", "TFORLOOP",
  "CELLINIT", "CELLGET", "CELLSET", "NOP",
}

local DEFAULT_DECOYS = 12
local MAX_DECOYS = 64

-- Locals of the emitted VM that get a fresh random name on every build. Fields
-- are written with the same token as the local they belong to, so a whole-word
-- rename stays consistent for both the declaration and every access.
local NAME_KEYS = {
  "N", "MM", "SB", "SC", "SJ", "SS", "SU", "SP", "SY", "ST", "RG",
  "X", "R", "K", "code", "pc", "TOP", "AN", "A", "CK", "I", "o", "W",
  "J1", "J2", "J3", "J4", "J5",
  "FQ", "integrityFailure", "SW",
}

local RESERVED = {
  ["and"] = true, ["break"] = true, ["do"] = true, ["else"] = true,
  ["elseif"] = true, ["end"] = true, ["false"] = true, ["for"] = true,
  ["function"] = true, ["goto"] = true, ["if"] = true, ["in"] = true,
  ["local"] = true, ["nil"] = true, ["not"] = true, ["or"] = true,
  ["repeat"] = true, ["return"] = true, ["then"] = true, ["true"] = true,
  ["until"] = true, ["while"] = true,
  error = true, print = true, game = true, type = true, pcall = true,
  select = true, tostring = true, tonumber = true, next = true, pairs = true,
  ipairs = true, rawget = true, rawset = true, setmetatable = true,
  getmetatable = true, getfenv = true, setfenv = true, loadstring = true,
  load = true, unpack = true, require = true, string = true, table = true,
  math = true, coroutine = true, debug = true, os = true, io = true,
  bit32 = true, utf8 = true, _env = true, _g = true, _version = true,
}

local LETTERS = "abcdefghijklmnopqrstuvwxyz"
local ALNUM = LETTERS .. "0123456789"

local function shortIdent()
  local len = U.randomInt(3, 5)
  local out = {}
  local p = U.randomInt(1, #LETTERS)
  out[1] = LETTERS:sub(p, p)
  for i = 2, len do
    p = U.randomInt(1, #ALNUM)
    out[i] = ALNUM:sub(p, p)
  end
  return table.concat(out)
end

local function serializePlain(v)
  local t = type(v)
  if t == "string" then return U.quote(v) end
  if t == "number" then return U.formatNumber(v) end
  if t == "boolean" then return tostring(v) end
  if t == "table" then
    local parts = {}
    for i = 1, #v do parts[i] = serializePlain(v[i]) end
    return "{" .. table.concat(parts, ",") .. "}"
  end
  return "nil"
end

local XOR = {}
for a = 0, 15 do
  XOR[a] = {}
  for b = 0, 15 do
    local x, y, n, p = a, b, 0, 1
    for _ = 1, 4 do
      if x % 2 ~= y % 2 then n = n + p end
      x, y, p = math.floor(x / 2), math.floor(y / 2), p * 2
    end
    XOR[a][b] = n
  end
end

local function xor32(a, b)
  local n, p = 0, 1
  for _ = 1, 8 do
    n = n + XOR[a % 16][b % 16] * p
    a, b, p = math.floor(a / 16), math.floor(b / 16), p * 16
  end
  return n
end

local function rotate(x, p, q)
  return (x % q) * p + math.floor(x / q)
end

local function cipherBlock(key, counter)
  local s = { 1634760805, 857760878, 2036477234, 1797285236 }
  for i = 1, 8 do s[4 + i] = key[i] end
  s[13], s[14], s[15], s[16] = counter, key[9], key[10], key[11]
  local w = {}
  for i = 1, 16 do w[i] = s[i] end
  local function quarter(a, b, c, d)
    w[a] = (w[a] + w[b]) % 4294967296
    w[d] = rotate(xor32(w[d], w[a]), 65536, 65536)
    w[c] = (w[c] + w[d]) % 4294967296
    w[b] = rotate(xor32(w[b], w[c]), 4096, 1048576)
    w[a] = (w[a] + w[b]) % 4294967296
    w[d] = rotate(xor32(w[d], w[a]), 256, 16777216)
    w[c] = (w[c] + w[d]) % 4294967296
    w[b] = rotate(xor32(w[b], w[c]), 128, 33554432)
  end
  for _ = 1, 10 do
    quarter(1, 5, 9, 13); quarter(2, 6, 10, 14)
    quarter(3, 7, 11, 15); quarter(4, 8, 12, 16)
    quarter(1, 6, 11, 16); quarter(2, 7, 12, 13)
    quarter(3, 8, 9, 14); quarter(4, 5, 10, 15)
  end
  for i = 1, 16 do w[i] = (w[i] + s[i]) % 4294967296 end
  return w
end

VMGen.cipherBlock = cipherBlock

local function packCode(code, key, alphabet)
  local out, block, counter = {}, nil, -1
  for i = 1, #code do
    for j = 1, 5 do
      local at = (i - 1) * 5 + j - 1
      local cb = math.floor(at / 16)
      if cb ~= counter then block, counter = cipherBlock(key, cb), cb end
      local v = code[i][j]
      if type(v) ~= "number" or v ~= math.floor(v) or
        v < -2147483648 or v > 2147483647 then
        error("bytecode operand outside signed 32-bit range", 0)
      end
      v = v < 0 and -v * 2 - 1 or v * 2
      v = xor32(v, block[at % 16 + 1])
      local text = {}
      for k = 1, 5 do
        local n = v % 85 + 1
        text[k] = alphabet:sub(n, n)
        v = math.floor(v / 85)
      end
      out[#out + 1] = table.concat(text)
    end
  end
  return table.concat(out)
end

local function cryptBytes(text, key, counter)
  local out, block = {}, nil
  for i = 1, #text do
    local at = (i - 1) % 64
    if at == 0 then block = cipherBlock(key, counter + math.floor((i - 1) / 64)) end
    local mask = math.floor(block[math.floor(at / 4) + 1] / 256^(at % 4)) % 256
    local b = text:byte(i)
    out[i] = string.char(XOR[math.floor(b / 16)][math.floor(mask / 16)] * 16 +
      XOR[b % 16][mask % 16])
  end
  return table.concat(out)
end

local function dataHash(v, h)
  h = h or 0
  local t = type(v)
  if t == "table" then
    h = (h * 31 + #v + 3) % 2147483647
    for i = 1, #v do h = dataHash(v[i], h) end
  elseif t == "string" then
    h = (h * 31 + #v + 1) % 2147483647
    for i = 1, #v do h = (h * 31 + v:byte(i)) % 2147483647 end
  else
    h = (h * 31 + v + 2) % 2147483647
  end
  return h
end

local function protoHash(p)
  return dataHash({p.c, p.t, p.n, p.k, p.u, p.a, p.v and 1 or 0})
end

local function constantText(v)
  if type(v) == "boolean" then return v and "t" or "f" end
  if v ~= v then return "x" end
  if v == math.huge then return "+" end
  if v == -math.huge then return "-" end
  return "n" .. U.formatNumber(v)
end

local function serializeProto(P)
  return "{c=" .. U.quote(P.c) .. ",t=" .. serializePlain(P.t) .. ",n=" .. P.n ..
    ",k=" .. serializePlain(P.k) .. ",u=" .. serializePlain(P.u) ..
    ",a=" .. P.a .. ",v=" .. (P.v and 1 or 0) ..
    ",hk=" .. serializePlain(P.hk or {}) .. "}"
end

function VMGen.generate(compiled, opts)
  opts = opts or {}
  local decoyCount = math.floor(tonumber(opts.decoys) or DEFAULT_DECOYS)
  if decoyCount < 0 then decoyCount = 0 end
  if decoyCount > MAX_DECOYS then decoyCount = MAX_DECOYS end
  local protos = compiled.protos
  local sourceStrings = compiled.strings or {}

  ---------------------------------------------------------------------------
  -- Random opcode assignment (shuffled, with unused decoy opcodes).
  ---------------------------------------------------------------------------
  local numbers = {}
  for i = 1, #OPS + decoyCount do numbers[i] = i end
  U.shuffle(numbers)
  local opnum = {}
  for i = 1, #OPS do opnum[OPS[i]] = numbers[i] end
  local decoys = {}
  for i = #OPS + 1, #numbers do decoys[#decoys + 1] = numbers[i] end

  local encoded = {}
  for pi = 1, #protos do
    local P = protos[pi]
    local ec = {}
    for i = 1, #P.code do
      local inst = P.code[i]
      local n = opnum[inst.op]
      if not n then error("internal: unknown opcode " .. tostring(inst.op), 0) end
      ec[i] = { n, inst.a or 0, inst.b or 0, inst.c or 0, inst.d or 0 }
    end
    encoded[pi] = {
      c = ec, k = P.k or {}, u = P.updesc or {}, a = P.params or 0,
      v = P.vararg and true or false,
    }
  end

  -- Decoy prototype: a valid word the entry point never invokes, so a dumped
  -- instruction stream has an extra dead proto to explain.
  encoded[#encoded + 1] = {
    c = {
      { opnum.LOADK, 0, 1, 0, 0 },
      { opnum.RETURN, 0, 0, 0, 0 },
    },
    k = { 0 }, u = {}, a = 0, v = false,
  }

  local symbols = {}
  for b = 33, 126 do
    if b ~= 34 and b ~= 39 and b ~= 92 then symbols[#symbols + 1] = string.char(b) end
  end
  U.shuffle(symbols)
  local alphabet = table.concat(symbols, "", 1, 85)
  local checksum, protoSums = 0, {}
  local descriptors, stringKey, stringSums = {}, {}, {}
  for i = 1, 11 do stringKey[i] = U.nextRandom() end
  local counter = 0
  local function addString(text)
    local encrypted = cryptBytes(text, stringKey, counter)
    descriptors[#descriptors + 1] = {encrypted, counter, #text}
    counter = counter + math.max(1, math.ceil(#text / 64))
    return #descriptors
  end
  for i = 1, #sourceStrings do addString(sourceStrings[i]) end
  for pi = 1, #encoded do
    local p, refs = encoded[pi], {}
    for i = 1, #p.k do refs[i] = addString(constantText(p.k[i])) end
    p.k = refs
  end
  -- Decoy pool entries: encrypted noise the VM never asks for, so the pool
  -- cannot be trimmed by counting live references alone.
  for i = 1, 4 do
    local junk = {}
    local len = U.randomInt(6, 12)
    for j = 1, len do
      local p = U.randomInt(1, #ALNUM)
      junk[j] = ALNUM:sub(p, p)
    end
    addString(table.concat(junk))
  end
  -- Self-check canary: a random string decoded at startup and periodically.
  local canaryChars = {}
  local ca = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
  for i = 1, 16 do
    local p = U.randomInt(1, #ca)
    canaryChars[i] = ca:sub(p, p)
  end
  local canary = table.concat(canaryChars)
  local canaryIndex = addString(canary)
  local order, remap, shuffled = {}, {}, {}
  for i = 1, #descriptors do order[i] = i end
  U.shuffle(order)
  for i = 1, #order do
    remap[order[i]] = i
    shuffled[i] = descriptors[order[i]]
  end
  descriptors = shuffled
  canaryIndex = remap[canaryIndex]
  for i = 1, #descriptors do stringSums[i] = dataHash(descriptors[i]) end
  for pi = 1, #encoded do
    local p, key = encoded[pi], {}
    for i = 1, #p.k do p.k[i] = remap[p.k[i]] end
    for i = 1, #p.c do
      local row = p.c[i]
      if row[1] == opnum.LOADSTR or row[1] == opnum.GETGLOBAL or row[1] == opnum.SETGLOBAL then
        row[3] = remap[row[3]]
      elseif row[1] == opnum.GETFIELD or row[1] == opnum.SETFIELD or row[1] == opnum.SELF then
        row[4] = remap[row[4]]
      end
    end
    for i = 1, 11 do key[i] = U.nextRandom() end
    p.n, p.t = #p.c, key
    p.c = packCode(p.c, key, alphabet)
    local hk = {}
    for i = 1, #p.c, 512 do
      hk[#hk + 1] = dataHash(p.c:sub(i, i + 511))
    end
    p.hk = hk
    protoSums[pi] = protoHash(p)
    checksum = (checksum * 31 + protoSums[pi]) % 2147483647
  end

  ---------------------------------------------------------------------------
  -- Per-build identifier renaming. Generated names are reserved against
  -- keywords, library globals and the rename keys themselves, so the emitted
  -- word replacement can never touch a name twice or shadow a builtin.
  ---------------------------------------------------------------------------
  local nameMap, nameList, usedNames = {}, {}, {}
  local reserved = {}
  for k in pairs(RESERVED) do reserved[k] = true end
  for i = 1, #NAME_KEYS do reserved[NAME_KEYS[i]] = true end
  for i = 1, #NAME_KEYS do
    local key = NAME_KEYS[i]
    local value
    repeat value = shortIdent() until not usedNames[value] and not reserved[value]
    usedNames[value] = true
    nameMap[key] = value
    nameList[#nameList + 1] = key
  end
  table.sort(nameList, function(a, b) return #a > #b end)
  local function applyNames(s)
    for i = 1, #nameList do
      local k = nameList[i]
      s = s:gsub("%f[%w_]" .. k .. "%f[%W_]", nameMap[k])
    end
    return s
  end

  local lines = {}
  local function add(s) lines[#lines + 1] = applyNames(s) end
  -- Proto and string tables are pure data; they take the renamed root name but
  -- skip the word pass so multi-megabyte tables stay linear-time to emit.
  local function addRaw(s) lines[#lines + 1] = s end
  local nm = nameMap
  local function num(n) return tostring(n) end

  -- Entry wall: the chunk opens with a plain function whose parameter list is
  -- rebuilt on every build; the last parameter takes the state table and the
  -- interpreter body lives in a nested function, so the wall costs no
  -- registers in the body frame.
  local wall = {}
  do
    local n = U.randomInt(34, 42)
    while #wall < n do
      local p = U.randomInt(1, #LETTERS)
      local name = LETTERS:sub(p, p)
      if U.randomInt(1, 3) ~= 1 then
        local q = U.randomInt(1, #ALNUM)
        name = name .. ALNUM:sub(q, q)
      end
      if not usedNames[name] and not reserved[name] then
        usedNames[name] = true
        wall[#wall + 1] = name
      end
    end
  end
  local wallText = table.concat(wall, ",")

  add("return({QT=function(" .. wallText .. ",...)" .. wall[#wall] .. "={};return (function(...)")
  add("local N={}")
  add("local MM=math")
  add("local SB=string.byte")
  add("local SC=string.char")
  add("local SJ=table.concat")
  add("local SS=string.sub")
  add("local SU=type(table.unpack)==\"function\" and table.unpack or unpack")
  add("local SP=select")
  add("local SY=pcall")
  add("local ST=type")
  add("local EI=\"bytecode integrity mismatch\"")
  add("local RG=rawget")

  add("N.P={}")
  for pi = 1, #encoded do
    addRaw(nm.N .. ".P[" .. pi .. "]=" .. serializeProto(encoded[pi]))
  end
  local sumParts = {}
  for i = 1, #protoSums do sumParts[i] = tostring(protoSums[i]) end
  addRaw(nm.N .. ".ck={" .. table.concat(sumParts, ",") .. "}")
  add("N.S={}")
  for i = 1, #descriptors do
    addRaw(nm.N .. ".S[" .. i .. "]=" .. serializePlain(descriptors[i]))
  end
  addRaw(nm.N .. ".sk=" .. serializePlain(stringKey))
  addRaw(nm.N .. ".sc=" .. serializePlain(stringSums))
  add("N.C=" .. checksum)
  -- Roblox's shared _G is not the chunk environment; getfenv preserves split-piece locals.
  add("N.E=_ENV or (function() local r=_G or {} " ..
    "local g=getfenv or RG(r,SC(103,101,116,102,101,110,118)) " ..
    "if ST(g)==\"function\" then local ok,v=SY(function() return g(1) end) " ..
    "if ok and ST(v)==\"table\" and ST(v[SC(115,116,114,105,110,103)])==\"table\" " ..
    "and ST(v[SC(112,99,97,108,108)])==\"function\" then return v end end " ..
    "g=getgenv or RG(r,SC(103,101,116,103,101,110,118)) " ..
    "if ST(g)==\"function\" then local ok,v=SY(g) " ..
    "if ok and ST(v)==\"table\" and ST(v[SC(115,116,114,105,110,103)])==\"table\" " ..
    "and ST(v[SC(112,99,97,108,108)])==\"function\" then return v end end " ..
    "return nil end)() or _G or {}")

  -- Stop this chunk only. The caller can handle the failure with pcall.
  addRaw(string.format("local function %s() error(%q,0) end", nm.integrityFailure, U.integrityError))

  -- Read-only seal and late-tamper capture. getmetatable is taken once; the two
  -- root tables the interpreter resolves through are pinned so a harness cannot
  -- re-metatable them after load, and the seal is only armed when the load-time
  -- round trip itself behaves (a wrapped getmetatable leaves it inert instead
  -- of tripping). The debug table's hook functions are recorded so a hook
  -- installed later becomes a hard failure on the next tick.
  add("local GM=getmetatable")
  add("SY(function() N.dg=N.E[SC(100,101,98,117,103)] if ST(N.dg)==\"table\" then N.hg=N.dg.gethook N.hs=N.dg.sethook N.du=1 end end)")
  add("N.im=0 if ST(GM)==\"function\" then local o1=SY(function() GM(N.P,{__metatable=false}) end) if o1 and GM(N.P)==false then N.im=1 end end")
  -- Dump-banner tripwire: a re-emitted file keeps the dumper's header in the
  -- chunk name. getinfo/string.find are read through the sealed env; each API
  -- call is pcall-guarded on its own, because wrapping the check in pcall
  -- would swallow the trip itself. Luau only has debug.info(level,"s").
  -- Level 2 is the enclosing function, since the call goes through pcall.
  -- Every keyword is stored shifted-by-TK in hex and rebuilt by gsub here, so
  -- the shipped file holds no readable keyword and no plain ASCII byte list.
  -- TK reuses an already-drawn string key instead of drawing a new random
  -- number, so adding this layer does not shift the rest of the build (the
  -- deadcode/decoy shape stays byte-for-byte what an older seed produced).
  local TK = math.floor((stringKey[7] or 0.5) * 251) % 251 + 1
  local function sc(s)
    local o = {}
    for i = 1, #s do
      o[i] = string.format("%02x", (string.byte(s, i) + TK) % 256)
    end
    return "XD(\"" .. table.concat(o) .. "\")"
  end
  add("local XD=function(h) return (string.gsub(h,\"%x%x\",function(c)return SC((tonumber(c,16)-" .. TK .. ")%256)end)) end")
  add("local bnd=N.E and N.E[" .. sc("debug") .. "] local bss local bgi,bi2 if ST(bnd)==\"table\" then local o,v=SY(function() return bnd[" .. sc("getinfo") .. "] end) if o then bgi=v end if bgi==nil then local o2,v2=SY(function() return bnd[" .. sc("info") .. "] end) if o2 then bi2=v2 end end end if ST(bgi)==\"function\" then local ok,a=SY(bgi,2,\"S\") if ok and ST(a)==\"table\" then local o3,v3=SY(function() return a[" .. sc("short_src") .. "] end) if o3 then bss=v3 end end elseif ST(bi2)==\"function\" then local ok,v=SY(bi2,2,\"s\") if ok then bss=v end end local bsl=string.lower if ST(bsl)==\"function\" and ST(bss)==\"string\" then bss=bsl(bss) end local bsf=string.find if ST(bss)==\"string\" and(bsf(bss," .. sc("dumped") .. ",1,true) or bsf(bss," .. sc("deobf") .. ",1,true) or bsf(bss," .. sc("dex utility") .. ",1,true)) then integrityFailure() end")

  -- Game-side tamper probes (same contract as the strong engine): inert off a
  -- live DataModel, skipped when an API is missing, counted only on an
  -- impossible answer. Placed after the decoder so marker strings stay hex.
  add(Tamper.emit())

  -- Load-time library integrity for the compact engine. Six deterministic
  -- semantics a devirt harness or instrumentation layer has to rewrite are
  -- checked once; two wrong answers abort this chunk. A missing API is
  -- skipped, never counted, so a stripped host stays quiet. The executor flag
  -- is recorded here too: executors legitimately install their own debug hooks
  -- and the runtime must not mistake that for instrumentation.
  add("local probeOk,badLibrary=SY(function() local E=N.E local B=0 local function ck(f) local o,v=SY(f) if o and v~=true then B=B+1 end end " ..
    "local s=E[" .. sc("string") .. "] if ST(s)==\"table\" then " ..
    "if ST(s[" .. sc("byte") .. "])==\"function\" then ck(function() return s[" .. sc("byte") .. "](\"A\")==65 end) end " ..
    "if ST(s[" .. sc("format") .. "])==\"function\" then ck(function() local F=s[" .. sc("format") .. "] return F(\"%05.2f\",1.5)==\"01.50\" end) end " ..
    "if ST(s[" .. sc("find") .. "])==\"function\" then ck(function() local F=s[" .. sc("find") .. "] return F(\"a.c\",\".\",1,true)==2 and F(\"abc\",\"z\",1,true)==nil end) end " ..
    "if ST(s[" .. sc("sub") .. "])==\"function\" then ck(function() return s[" .. sc("sub") .. "](\"abc\",-2)==\"bc\" end) end end " ..
    "local t=E[" .. sc("table") .. "] if ST(t)==\"table\" and ST(t[" .. sc("concat") .. "])==\"function\" then ck(function() return t[" .. sc("concat") .. "]({\"a\",\"b\"})==\"ab\" end) end " ..
    "local pc=E[" .. sc("pcall") .. "] local er=E[" .. sc("error") .. "] if ST(pc)==\"function\" and ST(er)==\"function\" then ck(function() local ok,v=pc(function() return 7 end) if ok~=true or v~=7 then return false end local mk={} local e2,o2=pc(function() return er(mk) end) return e2==false and o2==mk end) end " ..
    "local sl=E[" .. sc("select") .. "] if ST(sl)==\"function\" then ck(function() return sl(\"#\",1,nil,3)==3 and sl(\"#\")==0 end) end " ..
    "if ST(E[" .. sc("getgenv") .. "])==\"function\" or ST(E[" .. sc("gethui") .. "])==\"function\" or ST(E[" .. sc("hookfunction") .. "])==\"function\" or ST(E[" .. sc("getscriptbytecode") .. "])==\"function\" then N.ex=1 end " ..
    "return B>=2 end) if probeOk and badLibrary then integrityFailure() end")

  -- Decoy routines: never referenced by the VM, but they carry real loops,
  -- arithmetic and a decoder-shaped body so a dump has to prove them dead.
  add("local J1=function(x,y)")
  add("local z=x")
  add("for i=1,3 do z=z+y end")
  add("if z~=z then return x end")
  add("local t={z,x,y}")
  add("return t[1]+t[2]-t[3]")
  add("end")
  add("local J2=J1(" .. U.randomInt(0, 9) .. "," .. U.randomInt(1, 9) .. ")")
  add("local J3={}")
  add("for i=1,4 do J3[i]=(J2+i)*" .. U.randomInt(2, 97) .. " end")
  add("if J3[1]~=J3[1] then J3[2]=J3[1] end")
  add("local J4=function(s,k)")
  add("local o={}")
  add("for i=1,#s do o[i]=SC((SB(s,i)+SB(k,(i-1)%#k+1))%256) end")
  add("return SJ(o)")
  add("end")
  add("local J5=J4(" .. U.quote(shortIdent()) .. "," .. U.quote(shortIdent()) .. ")")
  add("if J5==nil then J5=J2 end")

  -- Byte XOR table (4-bit halves), built with pure arithmetic so the emitted
  -- decoder stays portable across Lua 5.1-5.4 and Luau.
  add("N.X={} for a=0,15 do N.X[a]={} for b=0,15 do local z,pw,x,y=0,1,a,b for q=1,4 do local xa=x%2 local yb=y%2 if xa~=yb then z=z+pw end x=(x-xa)/2 y=(y-yb)/2 pw=pw*2 end N.X[a][b]=z end end")
  addRaw(nm.N .. ".B=" .. U.quote(alphabet))
  add("N.M={} for j=1,85 do N.M[SB(N.B,j)]=j-1 end")
  add("N.x=function(a,b)local n,pw=0,1 for j=1,8 do n=n+N.X[a%16][b%16]*pw a=MM.floor(a/16) b=MM.floor(b/16) pw=pw*16 end return n end")
  add("N.rt=function(x,pw,q)return (x%q)*pw+MM.floor(x/q)end")
  add("N.cb=function(k,ct)")
  add("local s={1634760805,857760878,2036477234,1797285236} for j=1,8 do s[j+4]=k[j] end s[13]=ct s[14]=k[9] s[15]=k[10] s[16]=k[11]")
  add("local w={} for j=1,16 do w[j]=s[j] end")
  add("local function qr(a,b,c,d) w[a]=(w[a]+w[b])%4294967296 w[d]=N.rt(N.x(w[d],w[a]),65536,65536) w[c]=(w[c]+w[d])%4294967296 w[b]=N.rt(N.x(w[b],w[c]),4096,1048576) w[a]=(w[a]+w[b])%4294967296 w[d]=N.rt(N.x(w[d],w[a]),256,16777216) w[c]=(w[c]+w[d])%4294967296 w[b]=N.rt(N.x(w[b],w[c]),128,33554432) end")
  add("for j=1,10 do qr(1,5,9,13) qr(2,6,10,14) qr(3,7,11,15) qr(4,8,12,16) qr(1,6,11,16) qr(2,7,12,13) qr(3,8,9,14) qr(4,5,10,15) end")
  add("for j=1,16 do w[j]=(w[j]+s[j])%4294967296 end return w end")
  -- Four bounded windows keep loop back-edges from repeatedly decrypting pages.
  add("N.i=function(p,pc)")
  add("if pc<1 or pc>p.n or pc~=MM.floor(pc) then error(\"invalid bytecode position\",0) end")
  add("local base=MM.floor((pc-1)/32)*32+1 p.q=p.q or {} local q=p.q[base] if q==nil then q={} local ct=-1 local ks for i=base,MM.min(base+31,p.n) do local row={} for j=1,5 do local at=(i-1)*5+j-1 local cb=MM.floor(at/16) if cb~=ct then ks=N.cb(p.t,cb) ct=cb end local v,pw=0,1 for k=1,5 do local digit=N.M[SB(p.c,at*5+k)] if digit==nil then error(\"invalid bytecode digit\",0) end v=v+digit*pw pw=pw*85 end if v>=4294967296 then error(\"invalid bytecode word\",0) end v=N.x(v,ks[at%16+1]) row[j]=(v%2==0)and(v/2)or(-(v+1)/2) end q[i-base+1]=row end p.z=p.z or {} p.e=(p.e or 0)%4+1 local old=p.z[p.e] if old then p.q[old]=nil end p.z[p.e]=base p.q[base]=q end return q[pc-base+1] end")
  -- Flat decode: rows are built once per prototype and kept on it, so the hot
  -- loop pays one table read instead of a decoder call per instruction. The
  -- integrity tick still checks the ciphertext, so a tampered file is caught
  -- exactly as before.
  add("N.iflat=function(p) local o={} for j=1,p.n do o[j]=N.i(p,j) end p.q=nil p.z=nil return o end")
  -- Rotating slice hash of the packed code (512 bytes per tick). The table of
  -- expected values is baked at build time, so a verifier never needs the full
  -- hash on the hot path.
  add("N.sl=function(p,j) local s=p.c local st=(j-1)*512+1 return N.dh(SS(s,st,st+511)) end")
  add("N.db=function(s,k,ct) local o,w={} for j=1,#s do local at=(j-1)%64 if at==0 then w=N.cb(k,ct+MM.floor((j-1)/64)) end local m=MM.floor(w[MM.floor(at/4)+1]/256^(at%4))%256 local b=SB(s,j) o[j]=SC(N.X[MM.floor(b/16)][MM.floor(m/16)]*16+N.X[b%16][m%16]) end return SJ(o) end")
  add("N.dh=function(v,h) h=h or 0 local t=ST(v) if t==\"table\" then h=(h*31+#v+3)%2147483647 for j=1,#v do h=N.dh(v[j],h) end elseif t==\"string\" then h=(h*31+#v+1)%2147483647 for j=1,#v do h=(h*31+SB(v,j))%2147483647 end else h=(h*31+v+2)%2147483647 end return h end")
  add("N.cs=function(i) local e=N.S[i] if not e or N.dh(e)~=N.sc[i] then integrityFailure() end return e end")

  -- Decoded-string cache. Field and global names repeat on the hot path, and
  -- every lookup used to re-run the full scheme decoder (a per-byte loop over
  -- the descriptor). One table read now replaces that walk after the first
  -- use, which is what keeps a script that indexes tables in a loop at frame
  -- rate.
  add("N.Q={}")
  add("N.qh={}")
  add("N.q=function(i)")
  add("local v=N.Q[i] if v~=nil then return v end")
  add("local entry=N.cs(i) if #entry[1]~=entry[3] then error(\"string length mismatch\",0) end v=N.db(entry[1],N.sk,entry[2])")
  add("N.Q[i]=v N.qh[i]=N.dh(v)")
  add("return v")
  add("end")

  add("N.hp=function(p) return N.dh({p.c,p.t,p.n,p.k,p.u,p.a,p.v}) end")
  add("N.h=function() local s=0 for j=1,#N.P do s=(s*31+N.hp(N.P[j]))%2147483647 end return s end")
  add("N.v=function(p) if p.kc then return p.kc end local k={} for j=1,#p.k do local v=N.q(p.k[j]) local t=SS(v,1,1) if t==\"n\" then k[j]=tonumber(SS(v,2)) if k[j]==nil then error(\"invalid numeric constant\",0) end elseif t==\"t\" then k[j]=true elseif t==\"f\" then k[j]=false elseif t==\"+\" then k[j]=1/0 elseif t==\"-\" then k[j]=-1/0 elseif t==\"x\" then k[j]=0/0 else error(\"invalid constant tag\",0) end end p.kc=k return k end")

  add("N.pk=function(...)return {n=SP(\"#\",...),...}end")
  add("N.bw=function(x,y,m)")
  add("x=MM.floor(x)%9007199254740992 y=MM.floor(y)%9007199254740992 local r=0 local pw=1")
  add("for j=1,53 do local xa=x%2 local xb=y%2 local z")
  add("if m==1 then z=((xa==1)and(xb==1))and 1 or 0 elseif m==2 then z=((xa==1)or(xb==1))and 1 or 0 else z=(xa~=xb)and 1 or 0 end")
  add("r=r+z*pw x=(x-xa)/2 y=(y-xb)/2 pw=pw*2 end")
  add("return (MM.tointeger and MM.tointeger(r)) or r")
  add("end")
  add("N.bn=function(x)local n=MM.floor(x)local r=-n-1 return (MM.tointeger and MM.tointeger(r)) or r end")
  add("N.sh=function(x,y,d)")
  add("x=MM.floor(x) if y<0 then if d==1 then return N.sh(x,-y,0) else return N.sh(x,-y,1) end end")
  add("if y>=53 then return 0 end")
  add("if d==1 then for j=1,y do x=x*2 end return (MM.tointeger and MM.tointeger(x)) or x end")
  add("for j=1,y do x=MM.floor(x/2) end return (MM.tointeger and MM.tointeger(x)) or x")
  add("end")

  -- Guard the entire self-check so malformed data receives the same diagnostic.
  add("if not SY(function() if N.h()~=N.C then error() end if N.dh(N.sk)~=" ..
    dataHash(stringKey) .. " or #N.S~=" .. #descriptors ..
    " then error() end for j=1,#N.S do N.cs(j) end if N.q(" .. canaryIndex ..
    ")~=" .. U.quote(canary) .. " then error() end end) then integrityFailure() end")

  ---------------------------------------------------------------------------
  -- Dispatcher. Branch order is shuffled per build.
  ---------------------------------------------------------------------------
  local branchFor = {
    LOADK = "R[a]=K[b]",
    LOADBOOL = "R[a]=(b~=0)",
    LOADNIL = "R[a]=nil",
    LOADSTR = "R[a]=N.q(b)",
    MOVE = "R[a]=R[b]",
    GETGLOBAL = "R[a]=N.E[N.q(b)]",
    SETGLOBAL = "N.E[N.q(b)]=R[a]",
    GETUPVAL = "R[a]=u[b][1]",
    SETUPVAL = "u[b][1]=R[a]",
    GETTABLE = "R[a]=R[b][R[c]]",
    GETFIELD = "R[a]=R[b][N.q(c)]",
    SETTABLE = "R[a][R[b]]=R[c]",
    SETFIELD = "R[a][N.q(c)]=R[b]",
    SELF = "local tt=R[b] R[a]=tt[N.q(c)] R[a+1]=tt",
    NEWTABLE = "R[a]={}",
    SETLIST = "local nn=(b<0)and(TOP-c)or b if nn<0 then nn=0 end for j=1,nn do R[a][d+j-1]=R[c+j-1] end",
    SETIDX = "R[a][b]=R[c]",
    ADD = "R[a]=R[b]+R[c]",
    SUB = "R[a]=R[b]-R[c]",
    MUL = "R[a]=R[b]*R[c]",
    DIV = "R[a]=R[b]/R[c]",
    MOD = "R[a]=R[b]%R[c]",
    POW = "R[a]=R[b]^R[c]",
    IDIV = "if R[c]==0 then error(\"attempt to perform 'n//0'\") end R[a]=MM.floor(R[b]/R[c])",    CONCAT = "R[a]=R[b]..R[c]",
    UNM = "R[a]=-R[b]",
    NOT = "R[a]=not R[b]",
    LEN = "R[a]=#R[b]",
    BAND = "R[a]=N.bw(R[b],R[c],1)",
    BOR = "R[a]=N.bw(R[b],R[c],2)",
    BXOR = "R[a]=N.bw(R[b],R[c],3)",
    BNOT = "R[a]=N.bn(R[b])",
    SHL = "R[a]=N.sh(R[b],R[c],1)",
    SHR = "R[a]=N.sh(R[b],R[c],0)",
    EQ = "R[a]=(R[b]==R[c])",
    NE = "R[a]=(R[b]~=R[c])",
    LT = "R[a]=(R[b]<R[c])",
    LE = "R[a]=(R[b]<=R[c])",
    GT = "R[a]=(R[b]>R[c])",
    GE = "R[a]=(R[b]>=R[c])",
    JMP = "pc=pc+b",
    JMPF = "if not R[a] then pc=pc+b end",
    JMPT = "if R[a] then pc=pc+b end",
    CALL = "local nn=(b<0)and(TOP-a-1)or b if nn<0 then nn=0 end local ZZ=R[a] local RW if nn==0 then RW=N.pk(ZZ()) elseif nn==1 then RW=N.pk(ZZ(R[a+1])) elseif nn==2 then RW=N.pk(ZZ(R[a+1],R[a+2])) else local GA={} for j=1,nn do GA[j]=R[a+j] end RW=N.pk(ZZ(SU(GA,1,nn))) end if c<0 then for j=1,RW.n do R[d+j-1]=RW[j] end TOP=d+RW.n elseif c>0 then for j=1,c do R[d+j-1]=RW[j] end end",
    RETURN = "local nn=b if b<0 then nn=TOP-a end if nn<=0 then return end return SU(R,a,a+nn-1)",
    CLOSURE = "local Q=N.P[b] local VV={} for j=1,#Q.u do local E=Q.u[j] if E[1]==1 then VV[j]=R[E[2]] else VV[j]=u[E[2]] end end R[a]=N.f(Q,VV)",
    VARARG = "local nn=b if b<0 then nn=AN-p.a if nn<0 then nn=0 end TOP=a+nn end for j=1,nn do R[a+j-1]=A[p.a+j] end",
    FORPREP = "local init,limit,step=R[a],R[a+1],R[a+2] local run if step>0 then run=not(init>limit) elseif step<0 then run=not(init<limit) else run=true end if run then R[a+3]=(c==1)and{init}or init else pc=pc+b end",
    FORLOOP = "local step=R[a+2] local v=R[a]+step R[a]=v local run if step>0 then run=not(v>R[a+1]) elseif step<0 then run=not(v<R[a+1]) else run=true end if run then R[a+3]=(c==1)and{v}or v pc=pc+b end",
    TFORCALL = "local it,st,ct=R[a],R[a+1],R[a+2] local W=N.pk(it(st,ct)) for j=1,b do R[a+2+j]=W[j] end",
    TFORLOOP = "if R[a+3]~=nil then R[a+2]=R[a+3] pc=pc+c end",
    CELLINIT = "R[a]={R[a]}",
    CELLGET = "R[a]=R[b][1]",
    CELLSET = "R[b][1]=R[a]",
    NOP = "pc=pc+0",
  }

  -- Dispatch order follows build-time opcode frequency: the interpreter walks
  -- this chain with `o==num` compares, so the opcodes a script repeats land
  -- first and a hot loop pays a handful of compares per instruction instead of
  -- crossing the whole randomized list. Frequencies are per build; a decoy
  -- counts zero. A few decoys are sprinkled into the hot prefix and the rest
  -- stay in the shuffled tail, so the order does not cleanly separate live
  -- entries from dead ones.
  local freq = {}
  for pi = 1, #protos do
    local code = protos[pi].code
    for i = 1, #code do
      local op = code[i].op
      freq[op] = (freq[op] or 0) + 1
    end
  end
  local branches = {}
  for i = 1, #OPS do
    local name = OPS[i]
    local code = branchFor[name]
    if not code then error("internal: missing VM branch for " .. name, 0) end
    branches[#branches + 1] = {
      num = opnum[name], code = code, w = freq[name] or 0,
    }
  end
  local decoySnippets = {
    "pc=pc+0",
    "TOP=TOP+0",
    "R[a]=R[a]",
    "if a==b then pc=pc end",
    "local z=(a*0)+(b*0) pc=pc+z",
    "if c==d then TOP=TOP end",
    "local z=a+b pc=pc+(z-z)",
    "if a~=a then pc=pc end",
    "R[a]=R[a]==nil and R[a] or R[a]",
    "local z=0 for j=1,z do pc=pc end",
    "if b==b then TOP=TOP else TOP=TOP end",
    "local z=c-d pc=pc+(z-z)",
    "if d==d then pc=pc else pc=pc+1 end",
    "local z=(a+b+c+d)*0 pc=pc+z",
    "R[a]=R[a]~=nil and R[a] or R[a]",
    "local z=b-c pc=pc+(z-z)",
    "for j=1,0 do pc=pc end",
    "local z=0 while z>0 do z=z-1 end pc=pc+z",
    "if a<a then pc=pc end",
    "R[a]=R[a] and R[a] or R[a]",
  }
  local dead = {}
  for i = 1, #decoys do
    dead[#dead + 1] = {
      num = decoys[i],
      code = decoySnippets[(i - 1) % #decoySnippets + 1],
      w = 0,
    }
  end
  U.shuffle(dead)
  U.shuffle(branches)
  table.sort(branches, function(x, y) return x.w > y.w end)
  -- Decoys are interleaved among the middle branches, not before the hot ones:
  -- the dispatcher is a linear chain, so every decoy above a hot opcode adds a
  -- compare to each of its executions.
  local sprinkled = math.min(#dead, 8)
  for i = 1, sprinkled do
    local lo = math.min(#branches, 10)
    local pos = U.randomInt(lo + 1, math.min(#branches, 32))
    table.insert(branches, pos, table.remove(dead, 1))
  end
  for i = 1, #dead do branches[#branches + 1] = dead[i] end

  add("local X")
  add("X=function(p,u,...)")
  add("local FQ=p.fq if FQ==nil then FQ=N.iflat(p) p.fq=FQ end")
  add("local R,K,pc,TOP={},N.v(p),1,0")
  add("local AN=SP(\"#\",...)")
  add("local A={...}")
  add("for j=1,p.a do R[j]=A[j] end")
  add("local CK=0 local SW=0")
  add("while true do")
  add("local I=FQ[pc] if I==nil then error(\"invalid bytecode position\",0) end pc=pc+1")
  add("local o,a,b,c,d=I[1],I[2],I[3],I[4],I[5]")
  for i = 1, #branches do
    local kw = (i == 1) and "if" or "elseif"
    add(kw .. " o==" .. branches[i].num .. " then " .. branches[i].code)
  end
  add("else error(\"invalid bytecode opcode\",0) end")
  add("CK=CK+1")
  -- Tick every 12000 dispatches. The packed code is checked one rotating
  -- 512-byte slice at a time (expected hashes baked at build time); a full
  -- prototype hash runs every 64th tick. Hashing the whole ciphertext on every
  -- tick cost more than the interpreter itself on loop-heavy scripts.
  add("if CK>12000 then CK=0 local pi=(N.k or 0)%#N.P+1 N.k=pi local pp=N.P[pi] SW=SW+1 local sj=SW%#pp.hk+1 if N.sl(pp,sj)~=pp.hk[sj] or N.q(" .. canaryIndex .. ")~=" .. U.quote(canary) .. " then integrityFailure() end if SW%64==0 and N.hp(pp)~=N.ck[pi] then integrityFailure() end N.si=(N.si or 0)%#N.S+1 N.cs(N.si) if N.im==1 and GM(N.P)~=false then integrityFailure() end local qv=N.Q[N.si] if qv~=nil and N.dh(qv)~=N.qh[N.si] then integrityFailure() end if N.du==1 and not SY(function() return N.dg.gethook==N.hg and N.dg.sethook==N.hs end) then integrityFailure() end " ..
    "local sst=N.E[" .. sc("string") .. "] if ST(sst)==\"table\" then " ..
    "if ST(sst[" .. sc("byte") .. "])==\"function\" and sst[" .. sc("byte") .. "](\"A\")~=65 then integrityFailure() end " ..
    "if ST(sst[" .. sc("format") .. "])==\"function\" and sst[" .. sc("format") .. "](\"%05.2f\",1.5)~=\"01.50\" then integrityFailure() end end " ..
    "local ttl=N.E[" .. sc("table") .. "] if ST(ttl)==\"table\" and ST(ttl[" .. sc("concat") .. "])==\"function\" and ttl[" .. sc("concat") .. "]({\"a\",\"b\"})~=\"ab\" then integrityFailure() end " ..
    "local slt=N.E[" .. sc("select") .. "] if ST(slt)==\"function\" and (slt(\"#\",1,nil,3)~=3 or slt(\"#\")~=0) then integrityFailure() end " ..
    "local pct=N.E[" .. sc("pcall") .. "] if ST(pct)==\"function\" then local o3,v3=SY(function() local a3,b3=pct(function() return 7 end) return a3==true and b3==7 end) if o3 and v3~=true then integrityFailure() end end " ..
    "if N.du==1 and N.ex~=1 then local o4,hk=SY(function() return N.dg.gethook() end) if o4 and hk~=nil then integrityFailure() end end end")
  add("end")
  add("end")
  add("N.f=function(p,u)return function(...)return X(p,u,...)end end")
  add("local W=N.f(N.P[1],{})")
  add("return W(...)")
  add("end)(...)end}).QT(" .. wallText .. ",...)")

  return table.concat(lines, "\n"), {
    bytes = #table.concat(lines, "\n") + 1,
    opcodes = #OPS,
    decoys = #decoys,
    strings = #descriptors,
    protos = #encoded,
    checksum = checksum,
  }
end

return VMGen
