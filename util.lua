-- util.lua -- shared helpers for the obfuscator (Lua 5.1 compatible).
local U = {}
U.banner = '--[[ This, File Protected By GsXFuscator V0.6 ]]'
U.integrityError = 'GsXFuscator: integrity check failed'

local unpackFn = table.unpack or unpack
U.unpack = unpackFn

function U.pack(...)
  return { n = select("#", ...), ... }
end

-- xorshift32 PRNG, seeded per build. Deterministic when a seed is supplied.
local rngState = 0x9e3779b9 % 4294967296
function U.seed(n)
  rngState = (n or os.time()) % 4294967296
  if rngState == 0 then rngState = 0xC0FFEE end
end

local function nextRandom()
  local x = rngState
  x = (x * 1664525 + 1013904223) % 4294967296
  rngState = x
  return x
end
U.nextRandom = nextRandom

function U.randomInt(lo, hi)
  if hi < lo then lo, hi = hi, lo end
  local span = hi - lo + 1
  if span <= 0 then return lo end
  return lo + (nextRandom() % span)
end

function U.chance(pct)
  return (nextRandom() % 100) < pct
end

-- Shuffle a copy of an array in place (Fisher-Yates driven by our PRNG).
function U.shuffle(t)
  for i = #t, 2, -1 do
    local j = U.randomInt(1, i)
    t[i], t[j] = t[j], t[i]
  end
  return t
end

-- Random identifier: always the requested _0x prefix, never colliding with
-- source identifiers because the prefix only appears in generated names.
function U.ident(prefix)
  local alphabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
  local out = {}
  local len = U.randomInt(6, 11)
  for i = 1, len do
    local n = nextRandom()
    out[i] = alphabet:sub(n % #alphabet + 1, n % #alphabet + 1)
  end
  local d = nextRandom() % 100000
  return (prefix or "_0x") .. table.concat(out) .. string.format("%05d", d)
end

function U.hex(n)
  return string.format("%x", n)
end

function U.formatNumber(v)
  if v ~= v then return "(0/0)" end
  if v == math.huge then return "(1/0)" end
  if v == -math.huge then return "(-1/0)" end
  if v == 0 and 1 / v < 0 then return "-0.0" end
  if math.type and math.type(v) == "integer" then return tostring(v) end
  local text = string.format("%.17g", v)
  if math.type and math.type(v) == "float" and not text:find("[%.eE]") then
    text = text .. ".0"
  end
  return text
end

function U.quote(s)
  local out = { '"' }
  for i = 1, #s do
    local b = s:byte(i)
    if b == 34 then out[#out + 1] = '\\"'
    elseif b == 92 then out[#out + 1] = "\\\\"
    elseif b == 10 then out[#out + 1] = "\\n"
    elseif b == 13 then out[#out + 1] = "\\r"
    elseif b == 9 then out[#out + 1] = "\\t"
    elseif b < 32 or b >= 127 then out[#out + 1] = string.format("\\%03d", b)
    else out[#out + 1] = string.char(b) end
  end
  out[#out + 1] = '"'
  return table.concat(out)
end

function U.compact(code)
  local tokens, errors = require("src.lexer").lex(code)
  if #errors > 0 then error(errors[1].msg, 0) end
  local out, tail, previousNumber = {}, "", false
  for i = 1, #tokens - 1 do
    local t = tokens[i]
    local text = t.t == "string" and U.quote(t.v) or t.raw or t.v
    local first = text:sub(1, 1)
    if (tail:match("[%w_]") and first:match("[%w_]")) or
      (tail == "-" and first == "-") or
      (tail == "." and (first == "." or first:match("%d"))) or
      (previousNumber and first == ".") then
      out[#out + 1] = " "
    end
    out[#out + 1] = text
    tail = text:sub(-1)
    previousNumber = t.t == "number"
  end
  return table.concat(out)
end

function U.deepcopy(v, seen)
  if type(v) ~= "table" then return v end
  seen = seen or {}
  if seen[v] then return seen[v] end
  local t = {}
  seen[v] = t
  for k, val in pairs(v) do t[U.deepcopy(k, seen)] = U.deepcopy(val, seen) end
  return t
end

function U.sortedKeys(t)
  local keys = {}
  for k in pairs(t) do keys[#keys + 1] = k end
  table.sort(keys, function(a, b) return tostring(a) < tostring(b) end)
  return keys
end

-- Safe property access used by the compiler when inspecting parser nodes.
function U.isTable(v) return type(v) == "table" end

return U
