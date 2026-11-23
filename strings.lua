-- strings.lua -- polymorphic string encryption (layer 6).
--
-- Pipeline position:
--   analyze -> consts -> flatten -> opaque -> strings -> compiler
--
-- Every non-empty String literal is replaced with a call to one generated
-- decoder index:
--
--   "hello"  ->  _0x1a2b...3c4d(7)
--
-- All ciphertext lives in one self-describing byte string (the pool). The
-- decoder is generated as a single function value bound to a per-build local;
-- module 7 compiles that value into a VM proto, so the final artifact keeps no
-- host-level function by that name. Strings are only encrypted here: the
-- decoder never leaves an identifier called `decrypt` in the output.
--
-- Schemes (each string draws its own key and 16-bit salt, so two occurrences
-- of the same text share nothing):
--
--   xor      rotating-key XOR
--   b64      shuffled-alphabet Base64 + rotating-key XOR
--   huff     per-string Huffman + rotating-key XOR
--   feistel  4..8 round 8-bit Feistel network
--   lookup   salted 256-entry S-box + rotating-key XOR
--
-- Trap layer (on by default, `traps = false` disables it):
--
--   * local identifier decoys blur real entries in the shuffled pool;
--   * every decoy doubles as a canary: its plaintext hash is verified when the
--     decoder is built, and a mismatch raises the integrity error;
--   * out-of-range indices synthesize a deterministic token instead of an
--     empty string, so brute-force enumeration yields fake material too.
--
-- Everything is pure arithmetic (`% * + / floor`) and uses only escapes the
-- Lua 5.1 lexer accepts, so the emitted decoder runs unchanged on 5.1-5.4 and
-- Luau.

local Ast = require("src.ast")
local Parser = require("src.parser")
local Release = require("src.release")

local Strings = {}

-- Seeds can arrive as floats (os.clock on 5.3+) and math.floor may keep the
-- float subtype (Fengari does), which `%x` and `%d` reject. Format by hand.
local HEXDIGITS = {
  "0", "1", "2", "3", "4", "5", "6", "7",
  "8", "9", "a", "b", "c", "d", "e", "f",
}

local function hex8(n)
  n = math.floor(tonumber(n) or 0) % 4294967296
  local out = {}
  for i = 8, 1, -1 do
    local digit = n % 16
    out[i] = HEXDIGITS[digit + 1]
    n = (n - digit) / 16
  end
  return table.concat(out)
end

local function numberRaw(value)
  value = tonumber(value) or 0
  if value % 1 == 0 and math.abs(value) < 2 ^ 62 then
    return string.format("%.0f", value)
  end
  return string.format("%.17g", value)
end

local DEFAULTS = {
  seed = 0x5CE41D,
  enabled = true,
  prob = 1.0,
  minLength = 1,
  schemes = { "xor", "b64", "huff", "feistel", "lookup", "chain" },
}

Strings.SCHEMES = { "xor", "b64", "huff", "feistel", "lookup", "chain" }

-- ---------------------------------------------------------------- arithmetic

-- 4-bit XOR table; all bytes are split into nibbles so no host needs bit ops.
local XOR4 = {}
for a = 0, 15 do
  XOR4[a] = {}
  for b = 0, 15 do
    local z, pw, x, y = 0, 1, a, b
    for _ = 1, 4 do
      local xa, yb = x % 2, y % 2
      if xa ~= yb then z = z + pw end
      x = (x - xa) / 2
      y = (y - yb) / 2
      pw = pw * 2
    end
    XOR4[a][b] = z
  end
end

local function xorByte(a, b)
  return XOR4[math.floor(a / 16)][math.floor(b / 16)] * 16 + XOR4[a % 16][b % 16]
end

-- Portable LCG. Intermediates stay below 2^53 on every host.
local function makeRng(seed)
  local state = math.floor(math.abs(seed or 0)) % 4294967296
  return function(n)
    state = (state * 1664525 + 1013904223) % 4294967296
    if n <= 65536 then return (math.floor(state / 65536) % n) + 1 end
    return (state % n) + 1
  end
end

local function shuffle(list, rng)
  for i = #list, 2, -1 do
    local j = rng(i)
    list[i], list[j] = list[j], list[i]
  end
  return list
end

-- ---------------------------------------------------------------- flavours

-- Repeating-key XOR is trivially breakable by frequency analysis, so the key
-- byte is mixed with a salt-seeded LCG key-stream and the output is chained:
-- every ciphertext byte is folded into the next position's mask. Flipping one
-- byte therefore corrupts the following byte too, positions can no longer be
-- attacked independently, and the stream never repeats. The runtime R mirrors
-- this byte for byte (chaining reads ciphertext, so decode stays forward-only).
-- Folds the secret key bytes into the stream seed, so the keystream depends on
-- key material rather than on the 16-bit salt alone. Keep every product under
-- 2^53 so plain-double hosts (5.1/5.2) stay exact.
local function rotSeed(key, salt)
  local h = (salt * 2654435761 + 1013904223) % 4294967296
  for i = 1, #key do
    h = (h + key:byte(i) * (i * 977 + 1)) % 4294967296
  end
  return h
end

local function rot(s, key, salt, dec)
  local out = {}
  local kl = #key
  -- The stream seed folds the secret key bytes in, so knowing the 16-bit salt
  -- no longer reproduces the keystream. Each position mixes the key byte, a
  -- keystream byte and the chained byte from the previous position.
  local st = rotSeed(key, salt)
  local pv = salt % 256
  for i = 1, #s do
    st = (st * 1664525 + 1013904223) % 4294967296
    local kb = key:byte((i - 1 + salt) % kl + 1)
    local mb = math.floor(st / 65536) % 256
    local v = xorByte(xorByte(xorByte(s:byte(i), kb), mb), pv)
    out[i] = string.char(v)
    -- The chain always folds the ciphertext byte: on encode that is `v`, on
    -- decode the input byte, so both directions advance the same keystream.
    pv = xorByte(dec and s:byte(i) or v, i % 256)
  end
  return table.concat(out)
end

-- Position-chained additive stream, a different algebraic family from the
-- LCG-XOR stream above. Each output byte folds the key byte, the previous
-- ciphertext byte and a position weight, so bytes cannot be attacked
-- independently and the two schemes do not share a weakness. Decode stays one
-- forward pass; the chain reads ciphertext, so it is invertible byte by byte.
local function chainEncode(s, key, salt)
  local out, kl = {}, #key
  local pv = salt % 256
  for i = 1, #s do
    local kb = key:byte((i - 1 + salt) % kl + 1)
    local w = (i * 13 + salt) % 256
    local v = (s:byte(i) + kb + pv + w) % 256
    out[i] = string.char(v)
    pv = v
  end
  return table.concat(out)
end

local function chainDecode(s, key, salt)
  local out, kl = {}, #key
  local pv = salt % 256
  for i = 1, #s do
    local kb = key:byte((i - 1 + salt) % kl + 1)
    local w = (i * 13 + salt) % 256
    local cb = s:byte(i)
    out[i] = string.char((cb - kb - pv - w) % 256)
    pv = cb
  end
  return table.concat(out)
end

-- Whole-pool seal. Every serialized header (scheme id, key, salt, lengths) is
-- masked by a key-seeded table, so a dump of the constant shows no parseable
-- entry structure at all. The mask is periodic (1024 bytes) so the runtime can
-- unmask any single byte by table lookup instead of materialising the whole
-- plaintext pool: there is never a fully decrypted copy to dump. The mask is
-- length-preserving, so blob offsets and the anti-debug byte ranges stay
-- aligned.
local MASK_LEN = 1024

local function maskTable(key)
  local hi = math.floor(key / 65536) % 65536
  local lo = key % 65536
  local st = (lo * 65536 + hi + 374761393) % 4294967296
  local t = {}
  for i = 1, MASK_LEN do
    st = (st * 1664525 + 1013904223) % 4294967296
    t[i] = math.floor(st / 16777216) % 256
  end
  return t
end

local function poolSeal(s, key)
  local mt = maskTable(key)
  local out = {}
  for i = 1, #s do
    out[i] = string.char(xorByte(s:byte(i), mt[(i - 1) % MASK_LEN + 1]))
  end
  return table.concat(out)
end

-- ----------------------------------------------------- per-entry permutation
-- A keyed byte permutation applied on top of every scheme. It is nonlinear
-- with respect to the xor keystream (a byte permutation, not xor), so undoing
-- the stream alone does not recover the plaintext. The runtime mirrors this
-- with the inverse table and folds the lookup into the existing decode loop.

local function permSeed(key, salt)
  local h = (salt * 2654435761 + 1013904223) % 4294967296
  for i = 1, #key do
    h = (h + key:byte(i) * (i * 131 + 7)) % 4294967296
  end
  return h
end

local function permTable(key, salt)
  local t = {}
  for i = 1, 256 do t[i] = i - 1 end
  local st = permSeed(key, salt)
  for i = 256, 2, -1 do
    st = (st * 1664525 + 1013904223) % 4294967296
    local j = st % i + 1
    t[i], t[j] = t[j], t[i]
  end
  return t
end

local function invPermTable(key, salt)
  local t = permTable(key, salt)
  local inv = {}
  for i = 1, 256 do inv[t[i]] = i - 1 end
  return inv
end

-- Per-entry byte rotation folded around the shared S-box. The rotation is
-- derived from the entry's own key and salt, so two entries with the same
-- plaintext still get different ciphertext while the session pays for only one
-- 256-entry table. Rotating the input before the lookup makes the effective
-- per-entry permutation distinct (a rotation composed with the S-box), and the
-- runtime undoes it with one subtraction per byte.
local function permShift(key, salt)
  return (salt * 7 + key:byte(1) * 13) % 256
end

local function permute(s, map, shift)
  if not map then return s end
  shift = shift or 0
  local out = {}
  for i = 1, #s do
    out[i] = string.char(map[(s:byte(i) + shift) % 256 + 1])
  end
  return table.concat(out)
end

local function unpermute(s, inv, shift)
  if not inv then return s end
  shift = shift or 0
  local out = {}
  for i = 1, #s do out[i] = string.char((inv[s:byte(i)] - shift) % 256) end
  return table.concat(out)
end

-- Four little-endian bytes of the session pool key. The global byte
-- permutation derives from these, so the whole pool shares one S-box instead
-- of paying a 256-step shuffle per entry.
local function keyBytes(n)
  return string.char(n % 256, math.floor(n / 256) % 256,
    math.floor(n / 65536) % 256, math.floor(n / 16777216) % 256)
end

-- 64 byte values in standard Base64 order, shuffled by the salt.
local function alphabetBytes(salt)
  local a = {}
  for c = 65, 90 do a[#a + 1] = c end
  for c = 97, 122 do a[#a + 1] = c end
  for c = 48, 57 do a[#a + 1] = c end
  a[#a + 1] = 43
  a[#a + 1] = 47
  local st = (salt * 2654435761 + 40503) % 4294967296
  for i = 64, 2, -1 do
    st = (st * 1664525 + 1013904223) % 4294967296
    local j = st % i + 1
    a[i], a[j] = a[j], a[i]
  end
  return a
end

local function alphabetString(salt)
  local bytes = alphabetBytes(salt)
  local out = {}
  for i = 1, 64 do out[i] = string.char(bytes[i]) end
  return table.concat(out)
end

local function b64Encode(plain, salt)
  local al = alphabetString(salt)
  local out = {}
  for i = 1, #plain, 3 do
    local b1 = plain:byte(i) or 0
    local b2 = plain:byte(i + 1) or 0
    local b3 = plain:byte(i + 2) or 0
    local n = b1 * 65536 + b2 * 256 + b3
    local d1 = math.floor(n / 262144) % 64
    local d2 = math.floor(n / 4096) % 64
    local d3 = math.floor(n / 64) % 64
    local d4 = n % 64
    out[#out + 1] = al:sub(d1 + 1, d1 + 1)
    out[#out + 1] = al:sub(d2 + 1, d2 + 1)
    out[#out + 1] = al:sub(d3 + 1, d3 + 1)
    out[#out + 1] = al:sub(d4 + 1, d4 + 1)
  end
  return table.concat(out)
end

local function b64Decode(blob, salt, len)
  local al = alphabetString(salt)
  local rev = {}
  for j = 1, 64 do rev[al:byte(j)] = j - 1 end
  local out = {}
  for i = 1, #blob, 4 do
    local d1 = rev[blob:byte(i)] or 0
    local d2 = rev[blob:byte(i + 1)] or 0
    local d3 = rev[blob:byte(i + 2)] or 0
    local d4 = rev[blob:byte(i + 3)] or 0
    local n = d1 * 262144 + d2 * 4096 + d3 * 64 + d4
    out[#out + 1] = string.char(math.floor(n / 65536) % 256)
    out[#out + 1] = string.char(math.floor(n / 256) % 256)
    out[#out + 1] = string.char(n % 256)
  end
  return table.concat(out):sub(1, len)
end

-- Returns meta, packed. meta = two-byte symbol count followed by (byte, len)
-- pairs; packed is the bit stream, most significant bit first.
local function huffEncode(plain)
  local freq, order = {}, {}
  for i = 1, #plain do
    local b = plain:byte(i)
    if not freq[b] then freq[b] = 0; order[#order + 1] = b end
    freq[b] = freq[b] + 1
  end

  local nodes = {}
  local uid = 0
  for i = 1, #order do
    uid = uid + 1
    nodes[#nodes + 1] = { f = freq[order[i]], min = order[i], id = uid, b = order[i] }
  end
  local function cmp(x, y)
    if x.f ~= y.f then return x.f < y.f end
    if x.min ~= y.min then return x.min < y.min end
    return x.id < y.id
  end
  while #nodes > 1 do
    table.sort(nodes, cmp)
    local x = table.remove(nodes, 1)
    local y = table.remove(nodes, 1)
    uid = uid + 1
    nodes[#nodes + 1] = {
      f = x.f + y.f, min = math.min(x.min, y.min), id = uid, l = x, r = y,
    }
  end

  local lens, maxLen = {}, 0
  local function walk(node, depth)
    if node.b then
      lens[node.b] = depth
      if depth > maxLen then maxLen = depth end
    else
      walk(node.l, depth + 1)
      walk(node.r, depth + 1)
    end
  end
  walk(nodes[1], 1)
  -- Canonical codes are accumulated numerically; 40 bits stays exact.
  if maxLen > 40 then return nil end

  local symbols = {}
  for b in pairs(lens) do symbols[#symbols + 1] = b end
  table.sort(symbols)

  local sorted = {}
  for i = 1, #symbols do sorted[i] = symbols[i] end
  table.sort(sorted, function(a, b)
    if lens[a] == lens[b] then return a < b end
    return lens[a] < lens[b]
  end)

  local count = {}
  for i = 1, #sorted do
    local l = lens[sorted[i]]
    count[l] = (count[l] or 0) + 1
  end
  local first, code = {}, 0
  for l = 1, maxLen do
    code = (code + (count[l - 1] or 0)) * 2
    first[l] = code
  end
  local nextCode = {}
  for l = 1, maxLen do nextCode[l] = first[l] end
  local canon = {}
  for i = 1, #sorted do
    local b = sorted[i]
    local l = lens[b]
    canon[b] = nextCode[l]
    nextCode[l] = nextCode[l] + 1
  end

  local meta = { string.char(math.floor(#symbols / 256), #symbols % 256) }
  for i = 1, #symbols do
    meta[#meta + 1] = string.char(symbols[i], lens[symbols[i]])
  end

  local out, cur, bits = {}, 0, 0
  for i = 1, #plain do
    local b = plain:byte(i)
    local c, l = canon[b], lens[b]
    for k = l - 1, 0, -1 do
      local bit = math.floor(c / 2 ^ k) % 2
      cur = cur * 2 + bit
      bits = bits + 1
      if bits == 8 then
        out[#out + 1] = string.char(cur)
        cur, bits = 0, 0
      end
    end
  end
  if bits > 0 then
    for _ = bits, 7 do cur = cur * 2 end
    out[#out + 1] = string.char(cur)
  end
  return table.concat(meta), table.concat(out)
end

local function huffDecode(blob, meta, len)
  local total = meta:byte(1) * 256 + meta:byte(2)
  local entries = {}
  for j = 1, total do
    entries[#entries + 1] = { meta:byte(2 * j + 1), meta:byte(2 * j + 2) }
  end
  table.sort(entries, function(x, y)
    if x[2] == y[2] then return x[1] < y[1] end
    return x[2] < y[2]
  end)
  local maxLen = 0
  local count = {}
  for j = 1, #entries do
    local l = entries[j][2]
    count[l] = (count[l] or 0) + 1
    if l > maxLen then maxLen = l end
  end
  local first, code = {}, 0
  for l = 1, maxLen do
    code = (code + (count[l - 1] or 0)) * 2
    first[l] = code
  end
  local index, run = {}, 0
  for l = 1, maxLen do
    index[l] = run + 1
    run = run + (count[l] or 0)
  end

  local out = {}
  local bitPos, produced = 0, 0
  while produced < len do
    local value, hit = 0, false
    for l = 1, maxLen do
      bitPos = bitPos + 1
      local by = blob:byte(math.floor((bitPos - 1) / 8) + 1) or 0
      local bit = math.floor(by / 2 ^ (8 - ((bitPos - 1) % 8) - 1)) % 2
      value = value * 2 + bit
      local c = count[l] or 0
      if c > 0 and value - first[l] < c then
        produced = produced + 1
        out[produced] = string.char(entries[index[l] + (value - first[l])][1])
        hit = true
        break
      end
    end
    if not hit then break end
  end
  return table.concat(out)
end

local function feistel(s, key, salt, decrypt)
  local rounds = 4 + salt % 5
  local kl = #key
  local out = {}
  for j = 1, #s do
    local v = s:byte(j)
    local l, r = math.floor(v / 16), v % 16
    if decrypt then
      for q = rounds, 1, -1 do
        local f = (l * 3 + key:byte((q - 1) % kl + 1) * 5 + q * 7) % 16
        l, r = XOR4[r][f], l
      end
    else
      for q = 1, rounds do
        local f = (r * 3 + key:byte((q - 1) % kl + 1) * 5 + q * 7) % 16
        l, r = r, XOR4[l][f]
      end
    end
    out[j] = string.char(l * 16 + r)
  end
  return table.concat(out)
end

local function sbox(salt)
  local box = {}
  for i = 1, 256 do box[i] = i - 1 end
  local st = (salt * 40503 + 7919) % 4294967296
  for i = 256, 2, -1 do
    st = (st * 1664525 + 1013904223) % 4294967296
    local j = st % i + 1
    box[i], box[j] = box[j], box[i]
  end
  return box
end

local function lookupEncode(s, salt)
  local box = sbox(salt)
  local out = {}
  for i = 1, #s do out[i] = string.char(box[s:byte(i) + 1]) end
  return table.concat(out)
end

local function lookupDecode(s, salt)
  local box = sbox(salt)
  local inv = {}
  for i = 1, 256 do inv[box[i]] = i - 1 end
  local out = {}
  for i = 1, #s do out[i] = string.char(inv[s:byte(i)]) end
  return table.concat(out)
end

-- ---------------------------------------------------------------- descriptors

local ENCODERS = {
  xor = function(plain, key, salt) return rot(plain, key, salt) end,
  b64 = function(plain, key, salt)
    return rot(b64Encode(plain, salt), key, salt)
  end,
  huff = function(plain, key, salt)
    local meta, packed = huffEncode(plain)
    if not meta then return nil end
    return rot(packed, key, salt), meta
  end,
  feistel = function(plain, key, salt) return feistel(plain, key, salt, false) end,
  lookup = function(plain, key, salt)
    return rot(lookupEncode(plain, salt), key, salt)
  end,
  chain = function(plain, key, salt) return chainEncode(plain, key, salt) end,
}

-- Decode mirrors the encoder in reverse: undo the stream, undo the keyed
-- permutation, then undo the scheme. The runtime folds the permutation into
-- the same byte loop, so no extra pass exists there.
local function plainBytes(d, inv)
  return unpermute(d.blob, inv, permShift(d.key, d.salt))
end

local DECODERS = {
  xor = function(d, inv) return rot(plainBytes(d, inv), d.key, d.salt, true) end,
  b64 = function(d, inv)
    return b64Decode(rot(plainBytes(d, inv), d.key, d.salt, true), d.salt, d.plainLen)
  end,
  huff = function(d, inv)
    return huffDecode(rot(plainBytes(d, inv), d.key, d.salt, true), d.meta, d.plainLen)
  end,
  feistel = function(d, inv) return feistel(plainBytes(d, inv), d.key, d.salt, true) end,
  lookup = function(d, inv)
    return lookupDecode(rot(plainBytes(d, inv), d.key, d.salt, true), d.salt)
  end,
  chain = function(d, inv)
    return chainDecode(plainBytes(d, inv), d.key, d.salt)
  end,
}

-- ---------------------------------------------------------------- trap

local DECOY_WORDS = {
  "cache", "config", "core", "data", "edge", "frame", "graph", "index",
  "item", "layer", "layout", "media", "mesh", "node", "object", "page",
  "queue", "record", "scene", "shard", "slot", "sprite", "state", "storage",
  "sync", "tile", "trace", "view", "worker",
}
local DECOY_SEPS = { "_", "-", "." }

local function pick(rng, list) return list[rng(#list)] end

local function runOf(rng, first, last, count)
  local out = {}
  for i = 1, count do
    out[i] = string.char(first + rng(last - first + 1) - 1)
  end
  return table.concat(out)
end

local function hexRun(rng, count)
  local out = {}
  for i = 1, count do out[i] = HEXDIGITS[rng(16)] end
  return table.concat(out)
end

-- Dead entries that look like real program strings. The strongest decoys are
-- the program's own literals: a decoded pool then holds a dozen plausible
-- copies of every value, and "which entry is live" stops being a readability
-- test. A light mutation (one byte changed, a digit suffix) keeps the pool free
-- of exact duplicates so a call-log cannot pair entries by value.
local function recycleString(rng, list)
  if #list == 0 then return nil end
  local s = list[rng(#list)]
  if type(s) ~= "string" or #s == 0 or #s > 96 then return nil end
  local mode = rng(4)
  if mode == 1 then return s end
  local pos = rng(#s)
  if mode == 2 and s:sub(pos, pos):match("%a") then
    local other = string.char(97 + rng(26))
    return s:sub(1, pos - 1) .. other .. s:sub(pos + 1)
  elseif mode == 3 then
    return s .. tostring(1 + rng(999))
  end
  if pos > 1 then return s:sub(1, pos - 1) .. s:sub(pos + 1) end
  return s
end

-- Local-only shapes add dump noise without inventing external destinations.
local function decoyString(rng)
  local kind = rng(5)
  local w1, w2 = pick(rng, DECOY_WORDS), pick(rng, DECOY_WORDS)
  if kind == 1 then
    local sep = pick(rng, DECOY_SEPS)
    return w1 .. sep .. w2 .. sep .. hexRun(rng, 6 + rng(19))
  elseif kind == 2 then
    local uuid = hexRun(rng, 8) .. "-" .. hexRun(rng, 4) .. "-" ..
      hexRun(rng, 4) .. "-" .. hexRun(rng, 4) .. "-" .. hexRun(rng, 12)
    local form = rng(3)
    if form == 1 then return uuid end
    if form == 2 then return "{" .. uuid .. "}" end
    return w1 .. ":" .. uuid
  elseif kind == 3 then
    return "_" .. w1 .. runOf(rng, 65, 90, rng(4)) .. "_" .. hexRun(rng, 8 + rng(17))
  elseif kind == 4 then
    return w1 .. "[" .. runOf(rng, 48, 57, 2 + rng(7)) .. "]" ..
      pick(rng, DECOY_SEPS) .. hexRun(rng, 6 + rng(11))
  end
  return w1 .. ":" .. w2 .. ":" .. hexRun(rng, 12 + rng(21))
end

-- Polynomial hash mirrored by the emitted canary check. Stays far below 2^31.
local function checksum(s)
  local h = 0
  for i = 1, #s do h = (h * 31 + s:byte(i)) % 1048576 end
  return h
end

local function randomKey(rng, length)
  local out = {}
  for i = 1, length do out[i] = string.char(rng(255)) end
  return table.concat(out)
end

-- Build-time encode of one string. Returns nil when the scheme declines the
-- input (Huffman needs a short-enough code).
function Strings.encode(plain, scheme, rng, perm)
  local salt = rng(65536) - 1
  local key = randomKey(rng, 6 + rng(5) - 1)
  local blob, meta = ENCODERS[scheme](plain, key, salt)
  if not blob then return nil end
  blob = permute(blob, perm, permShift(key, salt))
  return {
    scheme = scheme, key = key, salt = salt, meta = meta or "",
    blob = blob, plain = plain, plainLen = #plain,
  }
end

-- Build-time decode; the runtime decoder below is an independent mirror.
function Strings.decode(desc, inv)
  return DECODERS[desc.scheme](desc, inv)
end

local function u16(n)
  return string.char(math.floor(n / 256) % 256, n % 256)
end

local function u24(n)
  return string.char(math.floor(n / 65536) % 256,
    math.floor(n / 256) % 256, n % 256)
end

local function serialize(desc)
  return table.concat({
    string.char(xorByte(desc.id, desc.key:byte(1))), string.char(#desc.key), desc.key,
    u16(desc.salt), u24(desc.plainLen), u16(#desc.meta), desc.meta,
    u24(#desc.blob), desc.blob,
  })
end

-- Per-entry {start, stop} ciphertext blob ranges of a serialized pool, in pool
-- order. The anti-debug layer rotates only these bytes when it deviates: blob
-- bytes are pure data, so a rotated blob still decodes (to different text)
-- with the same length, while the headers that carry the key length, salt,
-- lengths and offsets stay intact. Rotating the whole entry could shorten a
-- key or shift a blob offset after the load-time checks, which made a tripped
-- session raise and the swallow-all pcall then hid the failure completely.
-- Entries whose plaintext is used as a field name are filtered by the caller.
-- A sealed pool is opaque to this parser (its headers are masked), so the
-- encoder records the ranges it already computed from the plaintext and hands
-- them back by exact string identity. Build-time only; never emitted.
local sealedRanges = {}

function Strings.registerPoolRanges(sealed, ranges)
  if sealed and ranges then sealedRanges[sealed] = ranges end
end

function Strings.poolBlobs(s)
  if type(s) ~= "string" then return nil end
  local known = sealedRanges[s]
  if known then return known end
  if #s < 16 then return nil end
  local out, pos = {}, 1
  while pos <= #s do
    local kl = s:byte(pos + 1)
    if not kl or kl < 1 or kl > 10 then return nil end
    local plen = pos + 4 + kl
    local a, b, c = s:byte(plen), s:byte(plen + 1), s:byte(plen + 2)
    if not c then return nil end
    if a * 65536 + b * 256 + c > 65535 then return nil end
    local mlen = plen + 3
    local e, f = s:byte(mlen), s:byte(mlen + 1)
    if not f then return nil end
    local blen = mlen + 2 + e * 256 + f
    local x, y, z = s:byte(blen), s:byte(blen + 1), s:byte(blen + 2)
    if not z then return nil end
    local bl = x * 65536 + y * 256 + z
    local bstart, bend = blen + 3, blen + 2 + bl
    if bend > #s then return nil end
    out[#out + 1] = { start = bstart, stop = bend, length = bl }
    pos = bend + 1
  end
  if #out < 1 then return nil end
  return out
end

-- ---------------------------------------------------------------- emit

local function quote(s)
  local out = { '"' }
  for i = 1, #s do
    local b = s:byte(i)
    if b == 34 then out[#out + 1] = '\\"'
    elseif b == 92 then out[#out + 1] = "\\\\"
    elseif b < 32 or b >= 127 then out[#out + 1] = string.format("\\%03d", b)
    else out[#out + 1] = string.sub(s, i, i) end
  end
  out[#out + 1] = '"'
  return table.concat(out)
end

-- Decoder source. `P` is the pool; `D(i)` returns the plaintext of entry i.
-- Entry layout: sch(1) klen(1) key salt(2) plen(3) mlen(2) meta blen(3) blob.
-- `trap` carries the pool entry count and canary table (index, checksum); when
-- absent the decoder behaves exactly as before, with neither canaries nor the
-- out-of-range token synthesis.
-- `poolKey` masks the pool bytes; `permKey` seeds the shared byte permutation.
-- They are the same value in a build, but a caller can hand a plain pool with
-- only `permKey` (tests) without the decoder trying to unmask plain bytes.
local function runtimeSource(name, pool, ids, trap, poolKey, permKey, permKey2)
  local lines = {}
  local function add(s) lines[#lines + 1] = s end
  add("local " .. name .. " = (function(P)")
  add("local M=math.floor local B=string.byte local C=string.char")
  -- Only the string pool decoder uses this join. Exposing each decrypted
  -- literal as table.concat(out) lets a table.concat spy record the whole
  -- plaintext in one call. A balanced binary concatenation keeps data inside
  -- Lua's .. operator instead; it remains observable by a compromised host.
  -- Pairwise joining is O(n log n) character copies, not O(n^2).
  add("local function JT(t) local n=#t while n>1 do local k=0 " ..
    "for i=1,n,2 do k=k+1 if i<n then t[k]=t[i]..t[i+1] " ..
    "else t[k]=t[i] end end n=k end return t[1] or \"\" end")
  add("local T=JT local S=string.sub")
  add("local X={} for a=0,15 do X[a]={} for b=0,15 do local z,pw,x,y=0,1,a,b for q=1,4 do local xa=x%2 local yb=y%2 if xa~=yb then z=z+pw end x=(x-xa)/2 y=(y-yb)/2 pw=pw*2 end X[a][b]=z end end")
  -- Native byte XOR: Luau (Roblox executors) exposes bit32, so the hot decode
  -- helpers call it directly instead of walking the nibble table. The table
  -- stays as the fallback for hosts without it (5.1, LuaJIT); API names are
  -- char-coded like the rest of the artifact.
  local function chLit(s)
    local t = {}
    for i = 1, #s do t[i] = string.byte(s, i) end
    return "C(" .. table.concat(t, ",") .. ")"
  end
  add("local bt=(function() local ok,v=pcall(function() return " .. chLit("bit32") ..
    " end) if ok and type(v)==\"table\" then return v end end)()")
  add("local bx=bt and bt[" .. chLit("bxor") .. "]")
  add("local F")
  add("if type(bx)==\"function\" then F=function(a,b) return bx(a,b) end")
  add("else F=function(a,b) return X[M(a/16)][M(b/16)]*16+X[a%16][b%16] end end")
  add("local W8={128,64,32,16,8,4,2,1}")
  -- The pool stays masked for the whole session: every header byte and blob
  -- slice is unmasked on access, so a memory dump only ever holds ciphertext.
  if poolKey then
    local hi = math.floor(poolKey / 65536) % 65536
    local lo = poolKey % 65536
    add("local MT={} local ms=(" .. numberRaw(lo) .. "*65536+" .. numberRaw(hi) .. "+374761393)%4294967296 for i=1,1024 do ms=(ms*1664525+1013904223)%4294967296 MT[i]=M(ms/16777216)%256 end")
  else
    add("local MT={} for i=1,1024 do MT[i]=0 end")
  end
  add("local function HB(i) local c=B(P,i) if not c then return nil end return F(c,MT[(i-1)%1024+1]) end")
  add("local function MU(a,b) local o={} for z=a,b do local c=HB(z) if not c then break end o[#o+1]=C(c) end return T(o) end")
  add("local function UU(p,n) local v=0 for j=0,n-1 do local d=HB(p+j) if not d then return v end v=v*256+d end return v end")
  add("local function RK(k,o) local h=(o*2654435761+1013904223)%4294967296 for i=1,#k do h=(h+B(k,i)*(i*977+1))%4294967296 end return h end")
  -- One keyed byte permutation per session, mirroring the build side's
  -- permTable with the same folded 4-byte perm key. The whole pool shares the
  -- inverse S-box, so each decoded byte costs a single table lookup instead of
  -- a 256-step shuffle. Without the key the identity stands in, so the
  -- scaffold source stays valid while decoding nothing useful.
  if permKey then
    local kb = {}
    local seeds = { permKey, permKey2 or 0 }
    for s = 1, #seeds do
      local v = seeds[s]
      kb[#kb + 1] = v % 256
      kb[#kb + 1] = math.floor(v / 256) % 256
      kb[#kb + 1] = math.floor(v / 65536) % 256
      kb[#kb + 1] = math.floor(v / 16777216) % 256
    end
    local parts = {}
    for i = 1, #kb do parts[i] = numberRaw(kb[i]) end
    add("local GI={} do local t={} for i=1,256 do t[i]=i-1 end local st=(23130*2654435761+1013904223)%4294967296 local KB={" ..
      table.concat(parts, ",") .. "} for i=1," .. #kb ..
      " do st=(st+KB[i]*(i*131+7))%4294967296 end for i=256,2,-1 do st=(st*1664525+1013904223)%4294967296 local j=st%i+1 t[i],t[j]=t[j],t[i] end for i=1,256 do GI[t[i]]=i-1 end end")
  else
    add("local GI={} for i=0,255 do GI[i]=i end")
  end
  add("local function R(s,k,o) local out={} local kl=#k local st=RK(k,o) local pv=o%256 local sh=(o*7+B(k,1)*13)%256 for j=1,#s do st=(st*1664525+1013904223)%4294967296 local z=(GI[B(s,j)]-sh)%256 local v=F(F(F(z,B(k,(j-1+o)%kl+1)),M(st/65536)%256),pv) out[j]=C(v) pv=F(z,j%256) end return T(out) end")
  add("local function AL(salt) local a={} for c=65,90 do a[#a+1]=c end for c=97,122 do a[#a+1]=c end for c=48,57 do a[#a+1]=c end a[#a+1]=43 a[#a+1]=47 local st=(salt*2654435761+40503)%4294967296 for i=64,2,-1 do st=(st*1664525+1013904223)%4294967296 local j=st%i+1 a[i],a[j]=a[j],a[i] end return a end")
  add("local function D6(s,k,o,n) local a=AL(o) local rv={} for j=1,64 do rv[a[j]]=j-1 end local u=R(s,k,o) local out={} for j=1,#u,4 do local v=(rv[B(u,j)] or 0)*262144+(rv[B(u,j+1)] or 0)*4096+(rv[B(u,j+2)] or 0)*64+(rv[B(u,j+3)] or 0) out[#out+1]=C(M(v/65536)%256) out[#out+1]=C(M(v/256)%256) out[#out+1]=C(v%256) end return S(T(out),1,n) end")
  add("local function SB(salt) local b={} for i=1,256 do b[i]=i-1 end local st=(salt*40503+7919)%4294967296 for i=256,2,-1 do st=(st*1664525+1013904223)%4294967296 local j=st%i+1 b[i],b[j]=b[j],b[i] end return b end")
  add("local function UL(s,k,o) local b=SB(o) local inv={} for j=1,256 do inv[b[j]]=j-1 end local u=R(s,k,o) local out={} for j=1,#u do out[j]=C(inv[B(u,j)]) end return T(out) end")
  add("local function FE(s,k,o,d) local rn=4+o%5 local kl=#k local sp=d and GI local sh=(o*7+B(k,1)*13)%256 local out={} for j=1,#s do local v=sp and (GI[B(s,j)]-sh)%256 or B(s,j) local l=M(v/16) local r=v%16 if d then for q=rn,1,-1 do local f=(l*3+B(k,(q-1)%kl+1)*5+q*7)%16 l,r=F(r,f),l end else for q=1,rn do local f=(r*3+B(k,(q-1)%kl+1)*5+q*7)%16 l,r=r,F(l,f) end end out[j]=C(l*16+r) end return T(out) end")
  add("local function CH(s,k,o) local out={} local kl=#k local pv=o%256 local sh=(o*7+B(k,1)*13)%256 for j=1,#s do local kb=B(k,(j-1+o)%kl+1) local w=(j*13+o)%256 local cb=(GI[B(s,j)]-sh)%256 out[j]=C((cb-kb-pv-w)%256) pv=cb end return T(out) end")
  add("local function HF(b,me,n) local sy={} local c=(B(me,1) or 0)*256+(B(me,2) or 0) for j=1,c do local a,d=B(me,2*j+1),B(me,2*j+2) if a and d then sy[#sy+1]={a,d} end end table.sort(sy,function(x,y) if x[2]==y[2] then return x[1]<y[1] end return x[2]<y[2] end) local mx=0 local ct={} for j=1,#sy do local l=sy[j][2] ct[l]=(ct[l] or 0)+1 if l>mx then mx=l end end local fc={} local cd=0 for l=1,mx do cd=(cd+(ct[l-1] or 0))*2 fc[l]=cd end local ix={} local run=0 for l=1,mx do ix[l]=run+1 run=run+(ct[l] or 0) end local out={} local bi=0 local oi=0 while oi<n do local cv=0 local hit=false for l=1,mx do bi=bi+1 local by=B(b,M((bi-1)/8)+1) or 0 local bit=M(by/W8[(bi-1)%8+1])%2 cv=cv*2+bit local c2=ct[l] or 0 if c2>0 and cv-fc[l]<c2 then oi=oi+1 out[oi]=C(sy[ix[l]+(cv-fc[l])][1]) hit=true break end end if not hit then break end end return T(out) end")
  add("local function U(p,n) local v=0 for j=0,n-1 do local d=HB(p+j) if not d then return v end v=v*256+d end return v end")
  if trap then
    add("local HX={\"0\",\"1\",\"2\",\"3\",\"4\",\"5\",\"6\",\"7\",\"8\",\"9\",\"a\",\"b\",\"c\",\"d\",\"e\",\"f\"}")
    add("local NT=" .. trap.total)
    add("local function Z(i) local h=((i%4294967296)*1664525.0+" .. numberRaw(trap.synthSeed or 0) .. ")%4294967296 local n=24+M(h/65536)%25 local o={} for j=1,n do h=(h*1664525.0+1013904223)%4294967296 o[j]=HX[M(h/268435456)+1] end return T(o) end")
  end
  add("local O={} local V={}")
  -- Offset walk: entries are parsed forward from the last known index, so the
  -- whole pool is walked once no matter how many indices are requested. A walk
  -- that restarted at entry 1 for each new index made large pools quadratic.
  add("local FI=0 local FP=1")
  add("local function D(i)")
  add("local v=V[i] if v~=nil then return v end")
  if trap then add("if i>NT then v=Z(i) V[i]=v return v end") end
  add("local pos=O[i]")
  add("if not pos then local j=FI+1 local q=FP while j<=i do local kl=HB(q+1) if not kl then break end O[j]=q local ml=U(q+7+kl,2) local bl=U(q+9+kl+ml,3) q=q+12+kl+ml+bl FI=j j=j+1 end FP=q pos=O[i] end")
  add('if not pos then v="" V[i]=v return v end')
  add("local kl=HB(pos+1)")
  add('if not kl or kl<1 or kl>10 then v="" V[i]=v return v end')
  add("local k=MU(pos+2,pos+1+kl)")
  -- The scheme id is stored XORed with the first key byte, and the key is read
  -- first, so a dumper that unmasks the headers still cannot read the scheme
  -- of an entry without undoing the rest of the entry as well.
  add("local m=F(HB(pos) or 0,B(k,1))")
  add("local so=(HB(pos+2+kl) or 0)*256+(HB(pos+3+kl) or 0)")
  add('local n=U(pos+4+kl,3) if n>65535 then v="" V[i]=v return v end')
  add("local ml=U(pos+7+kl,2) local me=MU(pos+9+kl,pos+8+kl+ml)")
  add("local bl=U(pos+9+kl+ml,3) local b=MU(pos+12+kl+ml,pos+11+kl+ml+bl)")
  add("if m==" .. ids.xor .. " then v=R(b,k,so)")
  add("elseif m==" .. ids.b64 .. " then v=D6(b,k,so,n)")
  add("elseif m==" .. ids.huff .. " then v=HF(R(b,k,so),me,n)")
  add("elseif m==" .. ids.feistel .. " then v=FE(b,k,so,true)")
  add("elseif m==" .. ids.lookup .. " then v=UL(b,k,so)")
  add("elseif m==" .. ids.chain .. " then v=CH(b,k,so)")
  add('else v="" end')
  add("V[i]=v return v")
  add("end")
  if trap then
    add('local function K(i,t) local v=D(i) local h=0 for j=1,#v do h=(h*31+B(v,j))%1048576 end if h~=t then error(' .. string.format("%q", Release.integrityError) .. ',0) end end')
    -- One table, one loop: the call graph carries no per-entry call site, so
    -- an analyzer cannot tell the canary indices from ordinary pool reads
    -- without evaluating the table.
    local rows = {}
    for i = 1, #trap.canaries do
      local c = trap.canaries[i]
      rows[i] = "{" .. c.index .. "," .. c.check .. "}"
    end
    add("local CA={" .. table.concat(rows, ",") ..
      "} for q=1,#CA do K(CA[q][1],CA[q][2]) end")
  end
  add("return D")
  add("end)(" .. quote(pool) .. ")")
  return table.concat(lines, "\n")
end

-- ---------------------------------------------------------------- names

local function collectNames(ast)
  local taken = {}
  Ast.walk(ast, function(node)
    local t = node.type
    if t == "Name" then taken[node.value] = true
    elseif t == "Local" then
      for i = 1, #(node.names or {}) do taken[node.names[i]] = true end
    elseif t == "Function" then
      for i = 1, #(node.params or {}) do taken[node.params[i]] = true end
    elseif t == "LocalFunction" then taken[node.name] = true
    elseif t == "NumericFor" then taken[node.var] = true
    elseif t == "GenericFor" then
      for i = 1, #(node.names or {}) do taken[node.names[i]] = true end
    elseif t == "Label" or t == "Goto" then taken[node.name] = true
    end
  end)
  return taken
end

local function makeName(rng, taken)
  while true do
    local name = "_0x" .. hex8(rng(4294967296) - 1) .. hex8(rng(4294967296) - 1)
    if not taken[name] then
      taken[name] = true
      return name
    end
  end
end

-- ---------------------------------------------------------------- driver

-- Fengari's `%%` returns the float subtype even for integer operands, so the
-- build-side LCGs hand back integral floats. Normalise them: these passes only
-- synthesize integers, and a float-typed one would decode as a float in the VM
-- and change `tostring` output.
local tointeger = math.tointeger
local function intValue(value)
  if tointeger then
    local i = tointeger(value)
    if i ~= nil then return i end
  end
  return value
end

local function numberNode(value, line, col)
  value = intValue(value)
  return {
    type = "Number", value = value, raw = numberRaw(value),
    line = line, col = col, children = {}, synthetic = true,
  }
end

function Strings.run(ast, opts)
  opts = opts or {}
  local cfg = {
    seed = opts.seed or DEFAULTS.seed,
    enabled = opts.enabled ~= false,
    prob = opts.prob or DEFAULTS.prob,
    minLength = opts.minLength or DEFAULTS.minLength,
    schemes = opts.schemes or DEFAULTS.schemes,
    name = opts.name,
    traps = opts.traps ~= false,
  }

  local stats = {
    strings = 0, total = 0, bytes = 0, blobBytes = 0, added = 0, decoderNodes = 0,
    schemes = {}, decoySchemes = {}, skipped = { disabled = 0, prob = 0, empty = 0, short = 0 },
    runtimeName = nil, pool = nil, entries = {}, calls = {}, decoys = {},
    decoyCount = 0, canaries = {}, totalEntries = 0, poolOrder = nil,
    schemeIds = nil, trap = nil,
  }
  for i = 1, #Strings.SCHEMES do stats.schemes[Strings.SCHEMES[i]] = 0 end

  if not Ast.isNode(ast) or ast.type ~= "Chunk" then
    stats.skipped.disabled = 1
    return stats
  end
  if not cfg.enabled then
    stats.skipped.disabled = 1
    return stats
  end

  local rng = makeRng(cfg.seed)

  -- One key-derived byte permutation shared by the whole pool. It is drawn
  -- before any entry so the same table covers real strings and decoys, and it
  -- costs one 256-step shuffle per session rather than one per entry.
  local poolKey = rng(4294967296) - 1
  -- 64-bit S-box seed: a second independent 32-bit draw, so the shared
  -- permutation space is not limited to the 32-bit seal key. It comes from a
  -- separate generator: drawing here on the main stream would shift every
  -- later draw (keys, salts, deck) and change the string layout on rebuilds.
  local permRng = makeRng((math.floor(math.abs(cfg.seed)) % 2147483648) * 2 + 1)
  local permKey2 = permRng(4294967296) - 1
  local permBytes = keyBytes(poolKey) .. keyBytes(permKey2)
  local gperm = permTable(permBytes, 23130)
  local ginv = invPermTable(permBytes, 23130)

  local enabled = {}
  local seen = {}
  for i = 1, #cfg.schemes do
    local name = cfg.schemes[i]
    if ENCODERS[name] and not seen[name] then
      seen[name] = true
      enabled[#enabled + 1] = name
    end
  end
  if #enabled == 0 then
    for i = 1, #Strings.SCHEMES do enabled[i] = Strings.SCHEMES[i] end
  end

  local idPool = {}
  for i = 1, 255 do idPool[i] = i end
  shuffle(idPool, rng)
  local ids = {}
  for i = 1, #Strings.SCHEMES do ids[Strings.SCHEMES[i]] = idPool[i] end
  stats.schemeIds = ids

  local deck = {}
  for i = 1, #enabled do deck[i] = enabled[i] end
  shuffle(deck, rng)
  local deckPos = 1
  -- huff decodes bit by bit, so it costs far more instructions per output byte
  -- than the byte-wise schemes. Inside the VM that multiplies into decode time,
  -- so it is reserved for short literals: one long string must not stall the
  -- artifact while it warms up.
  local SCHEME_MAXLEN = { huff = 64 }
  local function nextScheme(len)
    for _ = 1, #deck + 1 do
      if deckPos > #deck then
        shuffle(deck, rng)
        deckPos = 1
      end
      local name = deck[deckPos]
      deckPos = deckPos + 1
      local cap = SCHEME_MAXLEN[name]
      if not cap or len <= cap then return name end
    end
    return nil
  end

  local taken = collectNames(ast)
  local runtimeName = cfg.name
  if type(runtimeName) ~= "string" or not runtimeName:match("^[%a_][%w_]*$") then
    runtimeName = makeName(rng, taken)
  end

  local function gate()
    if cfg.prob >= 1 then return true end
    if rng(1000) > cfg.prob * 1000 then
      stats.skipped.prob = stats.skipped.prob + 1
      return false
    end
    return true
  end

  local function makeCall(index, src)
    local call = {
      type = "Call", line = src.line, col = src.col, children = {}, synthetic = true,
    }
    call.children[1] = {
      type = "Name", value = runtimeName, line = src.line, col = src.col,
      children = {}, synthetic = true,
    }
    call.children[2] = numberNode(index, src.line, src.col)
    return call
  end

  local function replace(str, fieldName)
    stats.total = stats.total + 1
    local plain = tostring(str.value)
    if #plain == 0 then
      stats.skipped.empty = stats.skipped.empty + 1
      return nil
    end
    if #plain < cfg.minLength then
      stats.skipped.short = stats.skipped.short + 1
      return nil
    end
    if not gate() then return nil end

    local scheme = nextScheme(#plain) or "xor"
    local desc = Strings.encode(plain, scheme, rng, gperm)
    if not desc then
      scheme = "xor"
      desc = Strings.encode(plain, scheme, rng, gperm)
    end
    desc.id = ids[scheme]
    desc.inv = ginv
    desc.seq = #stats.entries + 1
    -- A decoded field name reaches a GETTABLE key register, not the k table,
    -- so vmgen cannot see it: record it here and keep the layer 11 deviation
    -- away from these entries (a garbage field name is a nil call).
    if fieldName then desc.fieldName = true end

    stats.entries[#stats.entries + 1] = desc
    stats.strings = stats.strings + 1
    stats.bytes = stats.bytes + #plain
    stats.schemes[scheme] = stats.schemes[scheme] + 1
    local call = makeCall(desc.seq, str)
    stats.calls[#stats.calls + 1] = { seq = desc.seq, node = call.children[2] }
    return call
  end

  local function visit(node)
    if node.synthetic then return end
    local kids = node.children
    for i = 1, #kids do
      local child = kids[i]
      if child.synthetic then
        -- already generated by an earlier pass
      elseif child.type == "String" then
        -- A dotted member key (`t.name`) is a name, not data: the deviation
        -- must leave it alone. An Index keeps its key as children[2].
        local field = node.type == "Index" and node.dot and i == 2
        local repl = replace(child, field)
        if repl then
          kids[i] = repl
          if node.type == "TableField" and node.key == child then node.key = repl end
        end
      elseif child.type == "TableField" and child.kind == "name" then
        -- `{ a = 1 }` leaks the key text; bracket form can carry a call.
        local key = child.key
        local repl = nil
        if key and key.type == "String" and not key.synthetic then
          repl = replace(key, true)
        end
        if repl then
          child.kind = "key"
          child.children[1] = repl
          child.key = repl
        end
        visit(child)
      else
        visit(child)
      end
    end
  end
  visit(ast)

  if stats.strings == 0 then
    stats.runtimeName = nil
    return stats
  end

  -- Trap: decoys share the pool with real entries, so call indices have to be
  -- remapped onto the shuffled order.
  local decoys = {}
  if cfg.traps then
    local plains = {}
    local realList = {}
    for i = 1, #stats.entries do
      local plain = stats.entries[i].plain
      plains[plain] = true
      if type(plain) == "string" and #plain > 0 and #plain <= 96 then
        realList[#realList + 1] = plain
      end
    end
    local want = math.min(180, math.max(24, math.floor(stats.strings * 0.9)))
    for _ = 1, want do
      local plain
      for _attempt = 1, 12 do
        local candidate
        if #realList > 0 and rng(100) <= 78 then
          candidate = recycleString(rng, realList)
        end
        if not candidate then candidate = decoyString(rng) end
        if #candidate <= 96 and not plains[candidate] then
          plain, plains[candidate] = candidate, true
          break
        end
      end
      if plain then
        local scheme = nextScheme(#plain) or "xor"
        local desc = Strings.encode(plain, scheme, rng, gperm)
        if not desc then
          scheme = "xor"
          desc = Strings.encode(plain, scheme, rng, gperm)
        end
        desc.id = ids[scheme]
        desc.inv = ginv
        desc.decoy = true
        decoys[#decoys + 1] = desc
        stats.decoySchemes[scheme] = (stats.decoySchemes[scheme] or 0) + 1
      end
    end
  end

  local order = {}
  for i = 1, #stats.entries do order[#order + 1] = stats.entries[i] end
  for i = 1, #decoys do order[#order + 1] = decoys[i] end
  shuffle(order, rng)

  local place = {}
  for pos = 1, #order do
    local entry = order[pos]
    entry.poolIndex = pos
    if entry.seq then place[entry.seq] = pos end
  end
  for i = 1, #stats.calls do
    local call = stats.calls[i]
    local pos = place[call.seq]
    call.node.value = pos
    call.node.raw = numberRaw(pos)
  end

  -- Pool indices whose plaintext is a field name. vmgen hands these to the
  -- anti-debug layer so a deviated session corrupts data only, never the names
  -- the program needs to keep running.
  local fieldKeys = {}
  for i = 1, #stats.entries do
    local entry = stats.entries[i]
    if entry.fieldName then fieldKeys[place[entry.seq]] = true end
  end
  stats.fieldKeys = fieldKeys
  ast.fieldKeys = fieldKeys

  local parts, offset = {}, 1
  for pos = 1, #order do
    local part = serialize(order[pos])
    order[pos].poolOffset = offset
    offset = offset + #part
    parts[pos] = part
  end
  local pool = table.concat(parts)

  -- The artifact carries the masked pool; stats keeps the plaintext copy for
  -- tests and for the entry-range walk below. Offsets are unchanged by the
  -- seal, so the recorded ranges stay valid against the masked bytes.
  local sealed = poolSeal(pool, poolKey)
  Strings.registerPoolRanges(sealed, Strings.poolBlobs(pool))

  -- Verify each canary before returning the decoder.
  local canaries = {}
  if cfg.traps and #decoys > 0 then
    for i = 1, #decoys do
      local entry = decoys[i]
      canaries[#canaries + 1] = {
        index = entry.poolIndex,
        check = checksum(entry.plain),
        blobOffset = entry.poolOffset + 12 + #entry.key + #entry.meta,
      }
    end
  end

  -- Retain the index map for callers that inspect the pool layout.
  local canaryKeys = {}
  for i = 1, #canaries do canaryKeys[canaries[i].index] = true end
  stats.canaryKeys = canaryKeys
  ast.canaryKeys = canaryKeys

  stats.pool = pool
  stats.poolSealed = sealed
  stats.poolKey = poolKey
  stats.poolKey2 = permKey2
  stats.poolPerm = gperm
  stats.poolInv = ginv
  stats.blobBytes = #pool
  stats.decoys = decoys
  stats.decoyCount = #decoys
  stats.canaries = canaries
  stats.totalEntries = #order
  stats.poolOrder = order
  stats.trap = cfg.traps and {
    total = #order, canaries = canaries, synthSeed = rng(4294967296) - 1,
  } or nil

  local source = runtimeSource(runtimeName, sealed, ids, stats.trap, poolKey, poolKey,
    permKey2)
  local rast, errors = Parser.parse(source, "@strings")
  local first = errors and errors[1]
  if first then
    error("strings: generated decoder failed to parse at " ..
      tostring(first.line) .. ":" .. tostring(first.col) .. " " .. tostring(first.msg))
  end
  local runtimeChunk = Ast.normalize(rast)
  local runtimeLocal = runtimeChunk.children[1]
  runtimeLocal.synthetic = true
  table.insert(ast.children, 1, runtimeLocal)

  stats.decoderNodes = Ast.count(runtimeChunk).nodes
  stats.added = stats.decoderNodes + stats.strings * 2
  stats.runtimeName = runtimeName
  return stats
end

Strings.runtimeSource = runtimeSource
Strings.quote = quote
Strings.checksum = checksum

return Strings
