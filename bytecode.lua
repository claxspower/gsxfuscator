-- bytecode.lua -- layer 9: packed, encrypted bytecode payload.
--
-- Pipeline position:
--   compiler -> vmgen.randomize (plan) -> bytecode.pack -> vmgen.emit
--
-- The layer 8 plan carries prototype tables as plain Lua data. This module
-- turns them into one byte string with a 16-byte header and an encrypted body,
-- so no instruction word, constant or prototype header ever appears as text in
-- the shipped file.
--
-- Format
--   header[1..4]   FNV-1a 32-bit checksum of the ciphertext body, LE
--   header[5..8]   plaintext body length, LE
--   header[9..12]  SipHash-2-4 32-bit tag of the four key bytes, LE
--   header[13]     format version, derived from the key tag
--   header[14..16] format marker bytes, derived from the key tag
--   body           ChaCha20 counter-mode ciphertext in 64-byte blocks
--   trailer[1..8]   SipHash-2-4 of exact header + body, low then high word, LE;
--                  keyed by the build key and a domain-separated second seed.
-- FNV detects cheap corruption; the keyed trailer supplies integrity. All key
-- material still derives from a 32-bit build seed, not a high-entropy secret.
--
-- The plaintext body is a varint stream:
--   proto count, then per proto: params, vararg flag, instruction count,
--   instructions as (key, zigzag a, b, c, tagged d), constant count, constants as
--   tagged length-prefixed values, upvalue descriptor count, descriptors.
--
-- All arithmetic is Lua 5.1-safe: no bitwise operators, no string.pack, no
-- integer division. The emitted runtime in src/vmgen.lua mirrors every helper
-- below exactly.
local VMGen = require("src.vmgen")

local Bytecode = {}

Bytecode.VERSION = 9
-- The three signature bytes are a per-build value: they are the low bytes
-- of the key tag, so no fixed byte pattern identifies the packer.
local function magicOf(tag)
  return { math.floor(tag / 16777216) % 256, tag % 256,
    math.floor(tag / 256) % 256, math.floor(tag / 65536) % 256 }
end
Bytecode.magicOf = magicOf
Bytecode.KEY_BITS = 4294967296

local floor = math.floor
local char = string.char
local byte = string.byte
local sub = string.sub
local rep = string.rep
local concat = table.concat
local format = string.format

-- ---------------------------------------------------------------- primitives
local XOR4 = {}
for a = 0, 15 do
  for b = 0, 15 do
    local z, pw, x, y = 0, 1, a, b
    for _ = 1, 4 do
      local xa = x % 2
      local yb = y % 2
      if xa ~= yb then z = z + pw end
      x = (x - xa) / 2
      y = (y - yb) / 2
      pw = pw * 2
    end
    XOR4[a * 16 + b] = z
  end
end

local function xor8(a, b)
  return XOR4[floor(a / 16) * 16 + floor(b / 16)] * 16 +
    XOR4[(a % 16) * 16 + (b % 16)]
end

-- (a * b) mod 2^32 without exceeding 2^53 anywhere. The 0.0 keeps the product
-- in the float domain: hosts whose lua_Integer is 32-bit (Fengari) would
-- otherwise wrap `a0 * b0`.
local function mul32(a, b)
  local a0 = a % 65536
  local a1 = (a - a0) / 65536
  local b0 = b % 65536
  local b1 = (b - b0) / 65536
  local lo = (a0 + 0.0) * b0
  local mid = a0 * b1 + a1 * b0
  return (lo + (mid % 65536) * 65536) % 4294967296
end

-- ------------------------------------------------------------- chacha20 core
-- RFC 8439 ChaCha20, written with arithmetic-only 32-bit ops so the packed
-- runtime behaves identically on Lua 5.1..5.4 and on Luau (no bit operators).
--
-- Encryption happens at build time on the packer's host, so when that host
-- does have real 32-bit bit operators the permutation also has a compiled
-- fast path (see chachaBlock). The emitted decoder never changes: both paths
-- produce the identical keystream, so packed output is byte-for-byte equal.
local MOD = 4294967296

-- Full 8-bit xor table: one lookup per byte instead of nibble composition.
-- Values carry the float subtype so xor32 products stay exact on hosts with
-- 32-bit integers.
local XORB = {}
for a = 0, 255 do
  local base = a * 256
  for b = 0, 255 do XORB[base + b] = xor8(a, b) + 0.0 end
end

local function xor32(a, b)
  local a0 = a % 256
  local b0 = b % 256
  local r = XORB[a0 * 256 + b0]
  a = (a - a0) / 256
  b = (b - b0) / 256
  a0 = a % 256
  b0 = b % 256
  r = r + XORB[a0 * 256 + b0] * 256
  a = (a - a0) / 256
  b = (b - b0) / 256
  a0 = a % 256
  b0 = b % 256
  r = r + XORB[a0 * 256 + b0] * 65536
  a = (a - a0) / 256
  b = (b - b0) / 256
  return r + XORB[a * 256 + b] * 16777216
end

local function add32(a, b)
  local s = a + b
  if s >= MOD then s = s - MOD end
  return s
end

-- rotate left by n: mul = 2^n, div = 2^(32-n)
local function rot32(v, mul, div)
  return (v * mul) % MOD + (v - v % div) / div
end

-- ---------------------------------------------------------------- siphash2-4
-- SipHash-2-4 with the 64-bit state split into (hi, lo) 32-bit words, so the
-- whole permutation is exact on 5.1..5.4, Luau and Fengari without bit
-- operators or 64-bit integers. Return the legacy folded 32-bit digest first,
-- then the raw high/low words for the container's 8-byte integrity trailer.
local function sipAdd(h, l, bh, bl)
  local lo = l + bl
  local carry = 0
  if lo >= MOD then lo = lo - MOD carry = 1 end
  local hi = h + bh + carry
  if hi >= MOD then hi = hi - MOD end
  return hi, lo
end

local function sipRot(h, l, mul, div)
  return (h * mul) % MOD + (l - l % div) / div,
    (l * mul) % MOD + (h - h % div) / div
end

local function sipRound(v)
  local v0h, v0l, v1h, v1l = v[1], v[2], v[3], v[4]
  local v2h, v2l, v3h, v3l = v[5], v[6], v[7], v[8]
  v0h, v0l = sipAdd(v0h, v0l, v1h, v1l)
  v1h, v1l = sipRot(v1h, v1l, 8192, 524288)
  v1h, v1l = xor32(v1h, v0h), xor32(v1l, v0l)
  v0h, v0l = v0l, v0h
  v2h, v2l = sipAdd(v2h, v2l, v3h, v3l)
  v3h, v3l = sipRot(v3h, v3l, 65536, 65536)
  v3h, v3l = xor32(v3h, v2h), xor32(v3l, v2l)
  v0h, v0l = sipAdd(v0h, v0l, v3h, v3l)
  v3h, v3l = sipRot(v3h, v3l, 2097152, 2048)
  v3h, v3l = xor32(v3h, v0h), xor32(v3l, v0l)
  v2h, v2l = sipAdd(v2h, v2l, v1h, v1l)
  v1h, v1l = sipRot(v1h, v1l, 131072, 32768)
  v1h, v1l = xor32(v1h, v2h), xor32(v1l, v2l)
  v2h, v2l = v2l, v2h
  v[1], v[2], v[3], v[4] = v0h, v0l, v1h, v1l
  v[5], v[6], v[7], v[8] = v2h, v2l, v3h, v3l
end

-- Raw entry point: four 32-bit words form the 128-bit key (a,b = k0 hi/lo,
-- c,d = k1 hi/lo). Exposed so the published SipHash-2-4 vectors can be run
-- against it directly.
local function sipRaw(s, a, b, c, d)
  local v = { xor32(a, 0x736f6d65), xor32(b, 0x70736575),
    xor32(c, 0x646f7261), xor32(d, 0x6e646f6d),
    xor32(a, 0x6c796765), xor32(b, 0x6e657261),
    xor32(c, 0x74656462), xor32(d, 0x79746573) }
  local n = #s
  local last = n - n % 8
  local i = 1
  while i <= last do
    local b0, b1, b2, b3 = byte(s, i, i + 3)
    local c0, c1, c2, c3 = byte(s, i + 4, i + 7)
    local ml = b0 + b1 * 256 + b2 * 65536 + b3 * 16777216.0
    local mh = c0 + c1 * 256 + c2 * 65536 + c3 * 16777216.0
    v[7], v[8] = xor32(v[7], mh), xor32(v[8], ml)
    sipRound(v) sipRound(v)
    v[1], v[2] = xor32(v[1], mh), xor32(v[2], ml)
    i = i + 8
  end
  local ml, mh = 0, (n % 256) * 16777216.0
  if n % 8 > 0 then
    local p = last + 1
    local b0, b1, b2, b3 = byte(s, p, p + 3)
    local c0, c1, c2 = byte(s, p + 4, p + 6)
    ml = b0 + (b1 or 0) * 256 + (b2 or 0) * 65536 + (b3 or 0) * 16777216.0
    mh = mh + (c0 or 0) + (c1 or 0) * 256 + (c2 or 0) * 65536
  end
  v[7], v[8] = xor32(v[7], mh), xor32(v[8], ml)
  sipRound(v) sipRound(v)
  v[1], v[2] = xor32(v[1], mh), xor32(v[2], ml)
  v[6] = xor32(v[6], 255)
  sipRound(v) sipRound(v) sipRound(v) sipRound(v)
  local hi = xor32(xor32(v[1], v[3]), xor32(v[5], v[7]))
  local lo = xor32(xor32(v[2], v[4]), xor32(v[6], v[8]))
  return xor32(hi, lo), hi, lo
end

-- Two 32-bit seeds expand into the four key words of the permutation. This
-- expansion does not increase the entropy of the embedded 32-bit build key.
local function sip32(s, k0, k1)
  local a = k0 % MOD
  local b = (mul32(a, 2246822507) + 3266489909) % MOD
  local c = k1 % MOD
  local d = (mul32(c, 2507323147) + 1515870810) % MOD
  return sipRaw(s, a, b, c, d)
end

local SIGMA = { 0x61707865 + 0.0, 0x3320646e + 0.0,
  0x79622d32 + 0.0, 0x6b206574 + 0.0 }

local function quarter(s, i, j, k, l)
  local x, y, z, w = s[i], s[j], s[k], s[l]
  x = add32(x, y); w = rot32(xor32(w, x), 65536, 65536)
  z = add32(z, w); y = rot32(xor32(y, z), 4096, 1048576)
  x = add32(x, y); w = rot32(xor32(w, x), 256, 16777216)
  z = add32(z, w); y = rot32(xor32(y, z), 128, 33554432)
  s[i], s[j], s[k], s[l] = x, y, z, w
end

local function chachaRounds(w)
  for _ = 1, 10 do
    quarter(w, 1, 5, 9, 13); quarter(w, 2, 6, 10, 14)
    quarter(w, 3, 7, 11, 15); quarter(w, 4, 8, 12, 16)
    quarter(w, 1, 6, 11, 16); quarter(w, 2, 7, 12, 13)
    quarter(w, 3, 8, 9, 14); quarter(w, 4, 5, 10, 15)
  end
  return w
end

-- Bit-operator syntax cannot appear in this file (the packer itself must
-- parse on 5.1), so the fast path is compiled from a source string. Detection
-- is deliberately strict: the mask must survive a value above 2^31, logical
-- right shift must fill zeros, and a float state word must convert exactly.
-- Hosts that fail any of it (5.1/LuaJIT/Luau, 32-bit-integer builds such as
-- Fengari) keep the portable path.
local DETECT_SRC = [==[
local m = 0xffffffff
return (m & m) == m and (0x9e3779b9 ~ 0) == 2654435769
  and (((0xdeadbeef << 16) & m) == 0xbeef0000)
  and ((0x80000000 >> 31) == 1)
  and ((1634760805.0 & m) == 0x61707865)
]==]

local FAST_SRC = [==[
local M = 0xffffffff
local function q(s, i, j, k, l)
  local x, y, z, w = s[i] & M, s[j] & M, s[k] & M, s[l] & M
  x = (x + y) & M w = (((w ~ x) << 16) | ((w ~ x) >> 16)) & M
  z = (z + w) & M y = (((y ~ z) << 12) | ((y ~ z) >> 20)) & M
  x = (x + y) & M w = (((w ~ x) << 8) | ((w ~ x) >> 24)) & M
  z = (z + w) & M y = (((y ~ z) << 7) | ((y ~ z) >> 25)) & M
  s[i], s[j], s[k], s[l] = x, y, z, w
end
return function(state)
  local w = {}
  for i = 1, 16 do w[i] = state[i] & M end
  for _ = 1, 10 do
    q(w, 1, 5, 9, 13) q(w, 2, 6, 10, 14)
    q(w, 3, 7, 11, 15) q(w, 4, 8, 12, 16)
    q(w, 1, 6, 11, 16) q(w, 2, 7, 12, 13)
    q(w, 3, 8, 9, 14) q(w, 4, 5, 10, 15)
  end
  for i = 1, 16 do w[i] = (w[i] + state[i]) & M end
  return w
end
]==]

local fastBlock
do
  local loader = loadstring or load
  if loader then
    local ok, detect = pcall(loader, DETECT_SRC)
    if ok and detect then
      local ok2, pass = pcall(detect)
      if ok2 and pass == true then
        local ok3, build = pcall(loader, FAST_SRC)
        if ok3 and build then
          local ok4, fn = pcall(build)
          if ok4 and type(fn) == "function" then fastBlock = fn end
        end
      end
    end
  end
end
Bytecode.chachaFast = fastBlock ~= nil

-- state[13] carries the block counter; the input state is preserved.
local function chachaBlock(state)
  if fastBlock then return fastBlock(state) end
  local w = {}
  for i = 1, 16 do w[i] = state[i] end
  chachaRounds(w)
  for i = 1, 16 do w[i] = add32(w[i], state[i]) end
  return w
end

-- Raw keystream block, exposed for RFC 8439 conformance tests.
function Bytecode.chacha20Block(key, nonce, counter)
  local state = { SIGMA[1], SIGMA[2], SIGMA[3], SIGMA[4] }
  for i = 1, 8 do
    local o = (i - 1) * 4
    state[4 + i] = byte(key, o + 1) + byte(key, o + 2) * 256.0 +
      byte(key, o + 3) * 65536.0 + byte(key, o + 4) * 16777216.0
  end
  for i = 1, 3 do
    local o = (i - 1) * 4
    state[13 + i] = byte(nonce, o + 1) + byte(nonce, o + 2) * 256.0 +
      byte(nonce, o + 3) * 65536.0 + byte(nonce, o + 4) * 16777216.0
  end
  state[13] = floor(tonumber(counter) or 0) % MOD
  local w = chachaBlock(state)
  local out = {}
  for i = 1, 16 do
    local q = w[i]
    local q0 = q % 256
    local q1 = (q - q0) / 256 % 256
    local q2 = (q - q0 - q1 * 256) / 65536 % 256
    out[#out + 1] = char(q0, q1, q2,
      (q - q0 - q1 * 256 - q2 * 65536) / 16777216)
  end
  return concat(out)
end

-- FNV-1a prime is 2^24 + 403, so x*prime mod 2^32 reduces to
-- (x*403 + (x%256)*2^24) mod 2^32 with every intermediate under 2^42.
local function fnv1a(s)
  local h = 2166136261
  local n = #s
  local i = 1
  while i + 3 <= n do
    local b0, b1, b2, b3 = byte(s, i, i + 3)
    local l = h % 256
    local x = h - l + XORB[l * 256 + b0]
    h = (x * 403 + (x % 256) * 16777216) % 4294967296
    l = h % 256
    x = h - l + XORB[l * 256 + b1]
    h = (x * 403 + (x % 256) * 16777216) % 4294967296
    l = h % 256
    x = h - l + XORB[l * 256 + b2]
    h = (x * 403 + (x % 256) * 16777216) % 4294967296
    l = h % 256
    x = h - l + XORB[l * 256 + b3]
    h = (x * 403 + (x % 256) * 16777216) % 4294967296
    i = i + 4
  end
  while i <= n do
    local l = h % 256
    local x = h - l + XORB[l * 256 + byte(s, i)]
    h = (x * 403 + (x % 256) * 16777216) % 4294967296
    i = i + 1
  end
  return h
end

local function le32(n)
  n = n % 4294967296
  return char(n % 256, floor(n / 256) % 256,
    floor(n / 65536) % 256, floor(n / 16777216) % 256)
end

-- Keyed 32-bit tag of one 32-bit word: SipHash-2-4 over its little-endian
-- bytes, keyed with the word itself and a second, unrelated expansion of it.
local function tagOf(k)
  k = k % 4294967296
  local tag = sip32(le32(k), k, (mul32(k, 2654435761) + 1013904223) % 4294967296)
  return tag
end

-- The container key schedule: the 32-bit build key expands into the eight
-- ChaCha key words; the three nonce words bind the keystream to the header
-- (key tag, plaintext length, padded body length), so a length-patched or
-- re-keyed payload decrypts to garbage.
local function containerState(key, plainLength, bodyLength)
  local state = { SIGMA[1], SIGMA[2], SIGMA[3], SIGMA[4] }
  local s = (key + 1515870810) % MOD
  for i = 1, 8 do
    s = (s * 1664525 + 1013904223) % MOD
    state[4 + i] = s
  end
  local tag = tagOf(key)
  state[13] = 0
  state[14] = (tag + mul32(plainLength, 2654435761)) % MOD
  state[15] = (mul32(tag, 2246822519) + bodyLength) % MOD
  state[16] = (plainLength + mul32(bodyLength, 3266489917)) % MOD
  return state
end

-- The emitted decoder derives its cipher key from the embedded key and the
-- padded body length; every entry point below must use the same derivation.
local function sessionKey(key, bodyLength)
  return (key + (bodyLength % 65536) * 2654435769 + 1515870810) % MOD
end

-- ChaCha20 in counter mode over 64-byte blocks. Symmetric: the same call
-- encrypts and decrypts; the plaintext is zero-padded to a block boundary and
-- the caller truncates to the header length.
local function chachaCrypt(data, key, plainLength)
  local pad = (64 - #data % 64) % 64
  if pad > 0 then data = data .. rep("\0", pad) end
  local state = containerState(key, plainLength, #data)
  local out = {}
  local block = 0
  local j = 1
  while j <= #data do
    state[13] = block
    local w = chachaBlock(state)
    local parts = {}
    for i = 1, 16 do
      local q = w[i]
      local q0 = q % 256
      local q1 = (q - q0) / 256 % 256
      local q2 = (q - q0 - q1 * 256) / 65536 % 256
      local q3 = (q - q0 - q1 * 256 - q2 * 65536) / 16777216
      local b0, b1, b2, b3 = byte(data, j, j + 3)
      parts[#parts + 1] = char(xor8(b0, q0), xor8(b1, q1),
        xor8(b2, q2), xor8(b3, q3))
      j = j + 4
    end
    out[#out + 1] = concat(parts)
    block = block + 1
  end
  return concat(out)
end

local function encrypt(plain, key)
  local padded = math.ceil(#plain / 64) * 64
  return chachaCrypt(plain, sessionKey(key, padded), #plain)
end

local function decrypt(cipher, key, plainLength)
  local want = plainLength or #cipher
  local plain = chachaCrypt(cipher, sessionKey(key, #cipher), want)
  if want < #plain then plain = sub(plain, 1, want) end
  return plain
end

-- ---------------------------------------------------------------- varint I/O
local function uvar(n)
  if n ~= n or n < 0 or n > 9007199254740991 then
    error("bytecode: varint range", 0)
  end
  n = floor(n)
  if n < 128 then return char(n) end
  if n < 16384 then return char(n % 128 + 128, floor(n / 128)) end
  local out = {}
  repeat
    local b = n % 128
    n = (n - b) / 128
    if n > 0 then out[#out + 1] = char(b + 128)
    else out[#out + 1] = char(b) end
  until n == 0
  return concat(out)
end

local function zigzag(n)
  n = floor(n)
  if n < 0 then return -2 * n - 1 end
  return 2 * n
end

local function unzigzag(v)
  -- floor keeps the integer subtype on 5.3/5.4 so unpacked operands match the
  -- source plan exactly (plain / always returns a float there).
  if v % 2 == 1 then return -floor((v + 1) / 2) end
  return floor(v / 2)
end

-- ---------------------------------------------------------------- constants
local function encodeValue(v)
  local t = type(v)
  if t == "nil" then return char(0) end
  if t == "boolean" then return char(v and 2 or 1) end
  if t == "number" then
    if v ~= v then return char(7) end
    if v == math.huge then return char(5) end
    if v == -math.huge then return char(6) end
    local s
    if v == 0 and 1 / v < 0 then
      s = "-0.0"
    elseif math.type and math.type(v) == "integer" then
      -- tostring is exact for 64-bit integers; %.17g would round through a
      -- double and could also change the subtype.
      s = tostring(v)
    else
      s = format("%.17g", v)
      -- Lua 5.3+ distinguishes integer and float subtypes; the text must force
      -- a float parse so results like tostring stay identical.
      if math.type and math.type(v) == "float" and
         not s:find("[%.eE]") then
        s = s .. ".0"
      end
    end
    return char(3) .. uvar(#s) .. s
  end
  local s = tostring(v)
  return char(4) .. uvar(#s) .. s
end

-- Instruction operand `d` can carry a float immediate (e.g. 1.0). Zigzag
-- varints are integer-only, so tag the field: 0 = integer varint, and the
-- constant number tags (3/5/6/7) when the float subtype must survive. Integer
-- magnitudes above 2^52 take the text path too because zigzag doubling and
-- varint accumulation would exceed the 53-bit exact range on 5.1/5.2.
local FIELD_LIMIT = 4503599627370496
local function encodeField(d)
  if math.type and math.type(d) == "float" then return encodeValue(d) end
  if d ~= floor(d) or d >= FIELD_LIMIT or d < -FIELD_LIMIT then
    return encodeValue(d)
  end
  if d == 0 and 1 / d < 0 then return encodeValue(d) end
  return char(0) .. uvar(zigzag(d))
end

-- The container body is decrypted as one string at load, so every constant
-- would otherwise sit in plaintext memory for the whole session. Each
-- prototype's constant section is therefore sealed a second time with its own
-- state; the runtime opens the section on the first constant read of that
-- prototype. A dump taken at any point only shows the pools the program has
-- actually touched, and every uncalled function stays ciphertext.
local function constState(key, pi, len)
  return (key + pi * 2654435761 + len * 2246822519 + 1999999973) % 4294967296
end

local function constCrypt(data, state, dec)
  local st = state
  -- Every mask folds the previous ciphertext byte, so positions can no longer
  -- be attacked independently: a chosen-plaintext probe at one offset reveals
  -- nothing about the stream at another. `dec` picks which byte advances the
  -- chain (ciphertext on decode, output on encode).
  local pv = state % 256
  local out = {}
  for i = 1, #data do
    local cb = byte(data, i)
    st = (st * 1664525 + 1013904223) % 4294967296
    local v = xor8(cb, xor8(floor(st / 16777216) % 256, pv))
    out[i] = char(v)
    pv = dec and cb or v
  end
  return concat(out)
end

-- --------------------------------------------------------------------- pack
local function encodeProtos(plan, key)
  if key == nil then key = Bytecode.deriveKey(plan.seed) end
  local parts = { uvar(#plan.protos) }
  for pi = 1, #plan.protos do
    local P = plan.protos[pi]
    parts[#parts + 1] = uvar(P.a or 0)
    parts[#parts + 1] = uvar(P.v and 1 or 0)
    if P.sm then
      -- Layer 10: instructions live in self-decoding blocks instead of a
      -- plain tuple list. Each block is a 4-byte state prefix + encrypted
      -- plaintext, and the chain value binds it to the previous block's
      -- build-time ciphertext.
      parts[#parts + 1] = uvar(1)
      parts[#parts + 1] = uvar(P.B)
      parts[#parts + 1] = uvar(P.cap)
      parts[#parts + 1] = uvar(P.total)
      parts[#parts + 1] = uvar(#P.blocks)
      for i = 1, #P.blocks do
        parts[#parts + 1] = uvar(P.chain[i])
        parts[#parts + 1] = uvar(#P.blocks[i])
        parts[#parts + 1] = P.blocks[i]
      end
    else
      parts[#parts + 1] = uvar(0)
      parts[#parts + 1] = uvar(#P.c)
      for i = 1, #P.c do
        local I = P.c[i]
        parts[#parts + 1] = uvar(I[1])
        parts[#parts + 1] = uvar(zigzag(I[2] or 0))
        parts[#parts + 1] = uvar(zigzag(I[3] or 0))
        parts[#parts + 1] = uvar(zigzag(I[4] or 0))
        parts[#parts + 1] = encodeField(I[5] or 0)
      end
    end
    parts[#parts + 1] = uvar(#P.k)
    if #P.k > 0 then
      local enc = {}
      for i = 1, #P.k do enc[i] = encodeValue(P.k[i]) end
      local body = le32(fnv1a(concat(enc))) .. concat(enc)
      local state = constState(key, pi, #body)
      local sealed = le32(state) .. constCrypt(body, state)
      parts[#parts + 1] = uvar(#sealed)
      parts[#parts + 1] = sealed
    end
    parts[#parts + 1] = uvar(#P.u)
    for i = 1, #P.u do
      parts[#parts + 1] = uvar(P.u[i][1])
      parts[#parts + 1] = uvar(P.u[i][2])
    end
  end
  return concat(parts)
end

function Bytecode.deriveKey(seed)
  local s = floor(tonumber(seed) or 0) % 4294967296
  if s < 0 then s = s + 4294967296 end
  s = (s * 1664525 + 1013904223) % 4294967296
  s = (s * 1664525 + 1013904223) % 4294967296
  return s
end

function Bytecode.pack(plan, opts)
  opts = opts or {}
  if type(plan) ~= "table" or type(plan.protos) ~= "table" then
    error("bytecode: vmgen plan expected", 0)
  end
  local key = opts.key
  if key == nil then key = Bytecode.deriveKey(plan.seed) end
  key = floor(tonumber(key) or 0) % 4294967296
  if key < 0 then key = key + 4294967296 end

  local plain = encodeProtos(plan, key)
  local body = encrypt(plain, key)
  local checksum = fnv1a(body)
  local keyTag = tagOf(key)
  local magic = magicOf(keyTag)
  local blob = le32(checksum) .. le32(#plain) .. le32(keyTag) ..
    char(magic[1], magic[2], magic[3], magic[4]) .. body

  local _, hi, lo = sip32(blob, key, (key + 0x41555448) % MOD)
  blob = blob .. le32(lo) .. le32(hi)

  return {
    blob = blob,
    key = key,
    version = Bytecode.VERSION,
    plainLength = #plain,
    plainBytes = #plain,
    cipherBytes = #body,
    blobBytes = #blob,
    checksum = checksum,
    keyTag = keyTag,
  }
end

-- ------------------------------------------------------------------- unpack
function Bytecode.parseHeader(blob)
  if type(blob) ~= "string" or #blob < 24 then
    return nil, "bytecode: truncated payload"
  end
  local b1, b2, b3, b4 = byte(blob, 1, 4)
  local b5, b6, b7, b8 = byte(blob, 5, 8)
  local b9, b10, b11, b12 = byte(blob, 9, 12)
  return {
    checksum = b1 + b2 * 256 + b3 * 65536 + b4 * 16777216,
    plainLength = b5 + b6 * 256 + b7 * 65536 + b8 * 16777216,
    keyTag = b9 + b10 * 256 + b11 * 65536 + b12 * 16777216,
    version = byte(blob, 13),
    magic = { byte(blob, 14), byte(blob, 15), byte(blob, 16) },
    body = sub(blob, 17, -9),
    tag = sub(blob, -8),
  }
end

-- Every section gets its own cursor and limit, including decrypted lazy data.
local function reader(s, start)
  local pos = start or 1
  local function take(n)
    if n > #s - pos + 1 then error("bytecode: section bounds", 0) end
    local v = sub(s, pos, pos + n - 1)
    pos = pos + n
    return v
  end
  local function rd()
    local v, m = 0, 1.0
    for i = 1, 8 do
      local b = byte(take(1))
      if (i == 8 and b > 15) or (i > 1 and b == 0) then
        error("bytecode: varint range or encoding", 0)
      end
      v = v + (b % 128) * m
      if b < 128 then return floor(v) end
      m = m * 128
    end
    error("bytecode: varint range", 0)
  end
  local function number()
    local v = tonumber(take(rd()))
    if not v or v ~= v or v == math.huge or v == -math.huge then
      error("bytecode: bad number", 0)
    end
    return v
  end
  local function field()
    local tag = byte(take(1))
    if tag == 0 then return unzigzag(rd()) end
    if tag == 3 then return number() end
    if tag == 5 then return math.huge end
    if tag == 6 then return -math.huge end
    if tag == 7 then return 0 / 0 end
    error("bytecode: field tag", 0)
  end
  local function count(n, size)
    if n > floor((#s - pos + 1) / size) then
      error("bytecode: section count", 0)
    end
  end
  local function done()
    if pos ~= #s + 1 then error("bytecode: trailing data", 0) end
  end
  return { rd = rd, take = take, number = number, field = field,
    count = count, done = done }
end

local function word(s)
  return byte(s, 1) + byte(s, 2) * 256.0 +
    byte(s, 3) * 65536.0 + byte(s, 4) * 16777216.0
end

local function instructions(r, count, out)
  r.count(count, 5)
  for i = 1, count do
    local ins = { r.rd(), unzigzag(r.rd()), unzigzag(r.rd()),
      unzigzag(r.rd()), r.field() }
    if out then out[i] = ins end
  end
end

local function decodeProtos(plain, key)
  local r = reader(plain)
  local rd = r.rd
  local protos = {}
  local np = rd()
  if np < 1 then error("bytecode: prototype count", 0) end
  r.count(np, 6)
  for pi = 1, np do
    local a, v, sm = rd(), rd(), rd()
    if v > 1 or sm > 1 then error("bytecode: flags", 0) end
    local P = { a = a, v = v == 1, c = {}, k = {}, u = {} }
    if sm == 1 then
      P.sm = true
      local B, cap, total, nb = rd(), rd(), rd(), rd()
      if B < 1 or total < 1 or cap < 1 or cap > total or
         cap < math.min(B, total) or (cap < total and cap % B ~= 0) or
         nb ~= floor((total - 1) / B) + 1 then
        error("bytecode: block counts", 0)
      end
      r.count(nb, 15)
      P.B, P.cap, P.total, P.blocks, P.chain = B, cap, total, {}, {}
      for i = 1, nb do
        local chain, ln = rd(), rd()
        local need = math.min(B, total - (i - 1) * B)
        if chain >= MOD or ln < 8 or need > floor((ln - 8) / 5) then
          error("bytecode: block bounds", 0)
        end
        local sealed = r.take(ln)
        P.chain[i], P.blocks[i] = chain, sealed
        local sv = word(sealed)
        local st = (key + pi * 2654435761 + i * 2246822519 +
          sv % 65536 + floor(sv / 65536) * 40961 + chain) % MOD
        local out = {}
        for j = 5, #sealed do
          st = (st * 1664525 + 1013904223) % MOD
          out[#out + 1] = char(xor8(byte(sealed, j), floor(st / 16777216)))
        end
        local body = concat(out)
        if fnv1a(sub(body, 5)) ~= word(body) then
          error("bytecode: block checksum", 0)
        end
        local br = reader(body, 5)
        instructions(br, need)
        br.done()
      end
    else
      instructions(r, rd(), P.c)
    end
    local nk = rd()
    if nk > 0 then
      local kl = rd()
      if kl < 8 or nk > kl - 8 then error("bytecode: constant bounds", 0) end
      local sealed = r.take(kl)
      local body = constCrypt(sub(sealed, 5), word(sealed), true)
      if fnv1a(sub(body, 5)) ~= word(body) then
        error("bytecode: constant checksum mismatch", 0)
      end
      local kr = reader(body, 5)
      for i = 1, nk do
        local tag = byte(kr.take(1))
        if tag == 1 then P.k[i] = false
        elseif tag == 2 then P.k[i] = true
        elseif tag == 3 then P.k[i] = kr.number()
        elseif tag == 4 then P.k[i] = kr.take(kr.rd())
        elseif tag == 5 then P.k[i] = math.huge
        elseif tag == 6 then P.k[i] = -math.huge
        elseif tag == 7 then P.k[i] = 0 / 0
        elseif tag ~= 0 then error("bytecode: constant tag", 0)
        end
      end
      kr.done()
    end
    local nu = rd()
    r.count(nu, 2)
    for i = 1, nu do
      local kind, index = rd(), rd()
      if kind > 1 then error("bytecode: upvalue flag", 0) end
      P.u[i] = { kind, index }
    end
    protos[pi] = P
  end
  r.done()
  return protos
end

function Bytecode.unpack(blob, key, opts)
  opts = opts or {}
  if type(opts) ~= "table" then return nil, "bytecode: bad options" end
  key = tonumber(key) or 0
  if key ~= key or key == math.huge or key == -math.huge then
    return nil, "bytecode: bad key"
  end
  local header, err = Bytecode.parseHeader(blob)
  if not header then return nil, err end
  if fnv1a(header.body) ~= header.checksum then
    return nil, "bytecode: checksum mismatch"
  end
  key = floor(tonumber(key) or 0) % 4294967296
  if key < 0 then key = key + 4294967296 end
  if tagOf(key) ~= header.keyTag then
    return nil, "bytecode: bad key"
  end
  local expect = magicOf(header.keyTag)
  if header.version ~= expect[1] or header.magic[1] ~= expect[2] or
     header.magic[2] ~= expect[3] or header.magic[3] ~= expect[4] then
    return nil, "bytecode: unsupported format"
  end
  local _, hi, lo = sip32(sub(blob, 1, -9), key, (key + 0x41555448) % MOD)
  if header.tag ~= le32(lo) .. le32(hi) then
    return nil, "bytecode: authentication mismatch"
  end
  local n, pn = #header.body, header.plainLength
  if n == 0 or n % 64 ~= 0 or pn < 1 or pn > n or n - pn >= 64 then
    return nil, "bytecode: invalid length"
  end
  if opts.verifyOnly then return true end
  local ok, result = pcall(function()
    return decodeProtos(decrypt(header.body, key, pn), key)
  end)
  if not ok then return nil, "bytecode: decode failed: " .. tostring(result) end
  return result
end

-- [VM9-AUDIT] Build-time round-trip verification, independent of VM emission.
-- The shipped code contains no audit metadata. A bad packer/serializer must
-- not silently release a different program, even if its outer seal is valid.
-- This is not a cryptographic trust boundary: the build key ships in the VM.
function Bytecode.auditPacked(plan, payload)
  if type(plan) ~= "table" or type(plan.protos) ~= "table" or
     type(plan.slots) ~= "table" or type(payload) ~= "table" or
     type(payload.blob) ~= "string" then
    return nil, "bytecode: invalid audit input"
  end
  local decoded, err = Bytecode.unpack(payload.blob, payload.key)
  if not decoded then return nil, err end
  if #decoded ~= #plan.protos then
    return nil, "bytecode: audit prototype count mismatch"
  end
  local function equal(a,b)
    if a == b then
      -- Compare signed zero, too: register arithmetic can observe its sign.
      if a == 0 and type(a) == "number" and type(b) == "number" then
        return 1/a == 1/b
      end
      return true
    end
    return type(a) == "number" and type(b) == "number" and
      a ~= a and b ~= b -- NaN constants
  end
  local function bad(pi, field)
    return nil, "bytecode: audit prototype "..pi.." "..field.." mismatch"
  end
  local instructions, lazy = 0, 0
  for pi = 1, #decoded do
    local original, restored = plan.protos[pi], decoded[pi]
    if original.a ~= restored.a or (not not original.v) ~= restored.v or
       (not not original.sm) ~= (not not restored.sm) then
      return bad(pi, "flags")
    end
    if #original.k ~= #restored.k then return bad(pi, "constants count") end
    for ki = 1,#original.k do
      if not equal(original.k[ki],restored.k[ki]) then
        return bad(pi, "constant "..ki)
      end
    end
    if #original.u ~= #restored.u then return bad(pi, "upvalues count") end
    for ui = 1,#original.u do
      for j = 1,2 do
        if original.u[ui][j] ~= restored.u[ui][j] then
          return bad(pi, "upvalue "..ui)
        end
      end
    end
    if original.sm then
      lazy = lazy + 1
      if original.B ~= restored.B or original.cap ~= restored.cap or
         original.total ~= restored.total or #original.blocks ~= #restored.blocks then
        return bad(pi, "lazy blocks")
      end
      for i=1,#original.blocks do
        if original.blocks[i] ~= restored.blocks[i] or
           original.chain[i] ~= restored.chain[i] then
          return bad(pi, "block "..i)
        end
      end
      instructions=instructions+original.total
    else
      if #original.c ~= #restored.c then return bad(pi, "instructions count") end
      for i=1,#original.c do
        local before,after=original.c[i],restored.c[i]
        if type(plan.slots[before[1]]) ~= "number" then
          return bad(pi, "unmapped opcode key "..i)
        end
        for j=1,5 do
          if not equal(before[j],after[j]) then
            return bad(pi, "instruction "..i.." operand "..j)
          end
        end
      end
      instructions=instructions+#original.c
    end
  end
  return {protos=#decoded, instructions=instructions, lazyProtos=lazy,
    authenticatedBytes=#payload.blob, validated=true}
end

-- --------------------------------------------------------------------- emit
-- Convenience wrapper for later layers: randomize -> pack -> emit packed
-- runtime. Returns the same (source, stats) pair as VMGen.generate.
function Bytecode.generate(compiled, opts)
  opts = opts or {}
  local plan = VMGen.randomize(compiled, opts)
  local payload = Bytecode.pack(plan, opts)
  return VMGen.emit(plan, { payload = payload })
end

Bytecode._internals = {
  xor8 = xor8, mul32 = mul32, fnv1a = fnv1a, le32 = le32,
  sipRaw = sipRaw, sip32 = sip32, tagOf = tagOf,
  xor32 = xor32, add32 = add32, rot32 = rot32, chachaBlock = chachaBlock,
  containerState = containerState, chachaCrypt = chachaCrypt,
  sessionKey = sessionKey,
  encrypt = encrypt, decrypt = decrypt,
  uvar = uvar, zigzag = zigzag, unzigzag = unzigzag,
  encodeValue = encodeValue, encodeProtos = encodeProtos,
  decodeProtos = decodeProtos, encodeField = encodeField,
}

return Bytecode
