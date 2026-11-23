-- strings.lua -- polymorphic string encryption (four independently generated schemes).
-- The obfuscator only encrypts here; the matching decoders are emitted by vmgen.
local U = require("src.util")
local S = {}

-- Pure-arithmetic byte XOR (the obfuscator itself must run on Lua 5.1 too).
local function xorByte(a, b)
  local r, pw = 0, 1
  for _ = 1, 8 do
    local xa, xb = a % 2, b % 2
    if xa ~= xb then r = r + pw end
    a = (a - xa) / 2
    b = (b - xb) / 2
    pw = pw * 2
  end
  return r
end

local function xorBytes(bytes, key)
  local out = {}
  local kl = #key
  for i = 1, #bytes do
    local b = bytes:byte(i)
    local k = key:byte((i - 1) % kl + 1)
    out[i] = string.char(xorByte(b, k))
  end
  return table.concat(out)
end

local function randomKey()
  local len = U.randomInt(2, 7)
  local t = {}
  for i = 1, len do t[i] = string.char(U.randomInt(1, 255)) end
  return table.concat(t)
end

-- The symbol alphabet is every printable 7-bit ASCII glyph except `"` and `\`:
-- 92 symbols against base64's 64. A payload stream drawn from it is not
-- decodable by any off-the-shelf alphabet, and the artifact stays 7-bit clean
-- so no executor, clipboard or loader can mangle it on the way in.
local function randomAlphabet()
  local chars = {}
  for c = 33, 126 do
    if c ~= 34 and c ~= 92 then chars[#chars + 1] = string.char(c) end
  end
  U.shuffle(chars)
  return table.concat(chars)
end

-- Four base-92 digits per three bytes: the same 4/3 expansion as base64, but
-- the digit values span 0..91, so a four-symbol group covers the whole 24-bit
-- range with no padding markers. The final group is zero-padded and the
-- decoder truncates to the stored plaintext length.
local function symbolEncode(bytes, alphabet)
  local out = {}
  local len = #bytes
  local i = 1
  while i <= len do
    local b1 = bytes:byte(i) or 0
    local b2 = bytes:byte(i + 1) or 0
    local b3 = bytes:byte(i + 2) or 0
    local n = b1 * 65536 + b2 * 256 + b3
    local d1 = math.floor(n / 778688) % 92
    local d2 = math.floor(n / 8464) % 92
    local d3 = math.floor(n / 92) % 92
    local d4 = n % 92
    out[#out + 1] = alphabet:sub(d1 + 1, d1 + 1)
    out[#out + 1] = alphabet:sub(d2 + 1, d2 + 1)
    out[#out + 1] = alphabet:sub(d3 + 1, d3 + 1)
    out[#out + 1] = alphabet:sub(d4 + 1, d4 + 1)
    i = i + 3
  end
  return table.concat(out)
end

-- Huffman tree over the bytes of a single string.
local function buildHuffman(bytes)
  local freq = {}
  local order = {}
  for i = 1, #bytes do
    local b = bytes:byte(i)
    if not freq[b] then freq[b] = 0; order[#order + 1] = b end
    freq[b] = freq[b] + 1
  end
  if #order < 2 then return nil end
  -- Stable tie-break: equal frequencies must not fall through to a table
  -- address comparison (Lua's tostring on tables), or two builds with the same
  -- seed would produce different trees and different files.
  local seq = 0
  local nodes = {}
  for i = 1, #order do
    seq = seq + 1
    nodes[#nodes + 1] = { f = freq[order[i]], b = order[i], q = seq }
  end
  while #nodes > 1 do
    table.sort(nodes, function(x, y)
      if x.f ~= y.f then return x.f < y.f end
      local xb = x.b or 1000
      local yb = y.b or 1000
      if xb ~= yb then return xb < yb end
      return x.q < y.q
    end)
    local x = table.remove(nodes, 1)
    local y = table.remove(nodes, 1)
    seq = seq + 1
    nodes[#nodes + 1] = { f = x.f + y.f, l = x, r = y, q = seq }
  end
  local root = nodes[1]
  local codes = {}
  local function walk(node, prefix)
    if node.b ~= nil then
      codes[node.b] = (prefix == "" and "0" or prefix)
    else
      walk(node.l, prefix .. "0")
      walk(node.r, prefix .. "1")
    end
  end
  walk(root, "")
  local parts = {}
  for i = 1, #bytes do parts[#parts + 1] = codes[bytes:byte(i)] end
  return table.concat(parts), root
end

local function serializeTree(node)
  if node.b ~= nil then
    return "{0,0," .. U.formatNumber(node.b) .. "}"
  end
  return "{" .. serializeTree(node.l) .. "," .. serializeTree(node.r) .. "}"
end
S.serializeTree = serializeTree

-- Returns descriptor: array whose first element is a logical scheme id (1..4).
-- vmgen remaps these ids per build and emits the decoder.
function S.encrypt(plain)
  local bytes = plain
  local scheme = U.randomInt(1, 4)
  if #bytes == 0 then scheme = 1 end
  if scheme == 3 then
    local bits, tree = buildHuffman(bytes)
    if bits then
      return { 3, bits, tree, true }
    end
    scheme = U.randomInt(1, 2)
  end
  if scheme == 2 then
    local alphabet = randomAlphabet()
    return { 2, alphabet, symbolEncode(bytes, alphabet), #bytes }
  elseif scheme == 4 and #bytes >= 4 then
    local partsCount = U.randomInt(2, math.min(4, #bytes))
    local parts = {}
    local idx = 1
    for p = 1, partsCount do
      local remaining = #bytes - idx + 1
      local remainingParts = partsCount - p + 1
      local take
      if remainingParts == 1 then
        take = remaining
      else
        take = U.randomInt(1, remaining - (remainingParts - 1))
      end
      local chunk = bytes:sub(idx, idx + take - 1)
      local key = randomKey()
      parts[#parts + 1] = { key, xorBytes(chunk, key) }
      idx = idx + take
    end
    return { 4, parts }
  else
    local key = randomKey()
    return { 1, key, xorBytes(bytes, key) }
  end
end

return S
