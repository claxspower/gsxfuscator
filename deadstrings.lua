-- deadstrings.lua -- exactly 2,879 distinct, inert Lua string literals
-- per *delivered* artifact. This is separate from the VM encrypted decoy pool.
-- Lua 5.1-5.4 and Luau compatible, no host APIs or runtime allocations.
-- Dead strings cost source size and parse time; they are not an integrity proof.
local DeadStrings = {}
DeadStrings.COUNT = 2879

local ALPHABET = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-"
local HEX = "0123456789abcdef"
local function rngFor(seed)
  local x = math.floor(math.abs(tonumber(seed) or 0)) % 4294967296
  return function(limit)
    x = (x * 1664525 + 1013904223) % 4294967296
    return math.floor(x / 65536) % limit + 1
  end
end

local function token(rng, index)
  local kind = (index + rng(4)) % 4
  local n = 23 + rng(16)
  local t = {}
  local alphabet = kind == 1 and HEX or ALPHABET
  for j = 1, n do
    local k = rng(#alphabet)
    t[j] = alphabet:sub(k, k)
  end
  if kind == 0 then
    return "entry_" .. table.concat(t)
  elseif kind == 1 then
    return "0x" .. table.concat(t)
  elseif kind == 2 then
    return "lookup/" .. table.concat(t)
  end
  return "data:" .. table.concat(t)
end

-- All dead data are emitted as one seeded, mixed sequence.  The count is a
-- hard limit for generated *literal values*, not a claim of confidentiality.
DeadStrings.CODEC_COUNTS = {base64 = 2374, base32 = 2374, base85 = 2373}
DeadStrings.CODEC_COUNT = 7121
DeadStrings.MAX_TOTAL = 10000

-- DeadCodecs: 1,936 valid, separately identifiable inert encoded literals.
-- 646 Base64 / 645 RFC 4648 Base32 / 645 RFC 1924 Base85.  These are *not*
-- the protected program's payload and are not a cryptographic control.
-- Every encoding is based on 20 bytes, with its index embedded to guarantee
-- uniqueness within a family. Pure Lua 5.1 arithmetic; no bit32 dependency.
local B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
local B32 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ234567'
local B85 = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!#$%&()*+-;<=>?@^_`{|}~'

local function byteString(rng, i)
  -- Prefix with stable distinct indices even when the PRNG cycles.
  local raw = {
    string.char(math.floor(i / 16777216) % 256),
    string.char(math.floor(i / 65536) % 256),
    string.char(math.floor(i / 256) % 256),
    string.char(i % 256),
  }
  for j = 5, 20 do raw[j] = string.char(rng(256) - 1) end
  return table.concat(raw)
end

local function digit(alphabet, value)
  return alphabet:sub(value + 1, value + 1)
end

local function base64(raw)
  local out = {}
  for i = 1, #raw, 3 do
    local a, b, c = raw:byte(i, i + 2)
    local n = a * 65536 + (b or 0) * 256 + (c or 0)
    out[#out+1] = digit(B64, math.floor(n / 262144) % 64)
    out[#out+1] = digit(B64, math.floor(n / 4096) % 64)
    out[#out+1] = b and digit(B64, math.floor(n / 64) % 64) or '='
    out[#out+1] = c and digit(B64, n % 64) or '='
  end
  return table.concat(out)
end

local function base32(raw)
  local out = {}
  -- All payloads are 20 bytes (four complete 40-bit blocks).
  for i = 1, #raw, 5 do
    local n = 0
    for j = i, i + 4 do n = n * 256 + raw:byte(j) end
    local part = {}
    for j = 8, 1, -1 do
      part[j] = digit(B32, n % 32)
      n = math.floor(n / 32)
    end
    out[#out+1] = table.concat(part)
  end
  return table.concat(out)
end

local function base85(raw)
  local out = {}
  -- RFC 1924's 85-character alphabet, used by common b85 decoders.
  for i = 1, #raw, 4 do
    local n = 0
    for j = i, i + 3 do n = n * 256 + raw:byte(j) end
    local part = {}
    for j = 5, 1, -1 do
      part[j] = digit(B85, n % 85)
      n = math.floor(n / 85)
    end
    out[#out+1] = table.concat(part)
  end
  return table.concat(out)
end

-- Lua-only, pure deterministic opaque guards prevent the exact string
-- "if false then" from trivially identifying every decoy.  They are NOT a
-- security boundary; an optimizing deobfuscator can still eliminate them.
local function mixedPrelude(seed)
  local rng = rngFor((tonumber(seed) or 0) + 975311)
  local kinds, total = {}, DeadStrings.COUNT + DeadStrings.CODEC_COUNT
  assert(total <= DeadStrings.MAX_TOTAL and total == 10000, 'dead data budget')
  for i=1,DeadStrings.COUNT do kinds[#kinds+1] = 0 end
  for i=1,DeadStrings.CODEC_COUNTS.base64 do kinds[#kinds+1] = 1 end
  for i=1,DeadStrings.CODEC_COUNTS.base32 do kinds[#kinds+1] = 2 end
  for i=1,DeadStrings.CODEC_COUNTS.base85 do kinds[#kinds+1] = 3 end
  for i=#kinds,2,-1 do
    local j = rng(i)
    kinds[i], kinds[j] = kinds[j], kinds[i]
  end
  local function ident(prefix)
    local chars={}
    for j=1,9 do chars[j]=string.char(96+rng(26)) end
    return prefix..table.concat(chars)
  end
  local guards={}
  local source={}
  -- All guard values are provably false for finite numeric values without
  -- using mutable globals or host/executor APIs.  Compute each once.
  for j=1,4 do
    guards[j]=ident('_gxq')
    source[#source+1] = 'local '..guards[j]..'=(function(x) return x~=x end)('..
      tostring(rng(2000000000))..');'
  end
  local group, seen, indexed = {}, {}, {0,0,0,0}
  local groupCount = 0
  local function flush()
    if #group == 0 then return end
    groupCount = groupCount+1
    local g=guards[(groupCount-1)%#guards+1]
    source[#source+1]='if '..g..' then local '..ident('_gxd')..'={'..
      table.concat(group,',')..'} end;'
    group={}
  end
  for k=1,total do
    local kind=kinds[k]
    indexed[kind+1]=indexed[kind+1]+1
    local rawText
    if kind==0 then
      repeat rawText=token(rng,k) until not seen[rawText]
    else
      -- Each encoded family has an independent ordinal; preserving the
      -- ordinal inside the 20 byte decoded data permits exact validation.
      local bytes=byteString(rng,indexed[kind+1])
      if kind==1 then rawText=base64(bytes)
      elseif kind==2 then rawText=base32(bytes)
      else rawText=base85(bytes) end
    end
    assert(not seen[rawText], 'duplicate dead literal')
    seen[rawText]=true
    group[#group+1] = string.format('%q',rawText)
    -- An irregular group size keeps the carrier shape from being uniform.
    if #group >= 93+rng(41) then flush() end
  end
  flush()
  assert(indexed[1]==DeadStrings.COUNT and
    indexed[2]==DeadStrings.CODEC_COUNTS.base64 and
    indexed[3]==DeadStrings.CODEC_COUNTS.base32 and
    indexed[4]==DeadStrings.CODEC_COUNTS.base85, 'dead data counter')
  return table.concat(source)
end

-- Do not emit warnings on an unmodified program. A normal executor is not
-- evidence of instrumentation, and user-visible incident messages belong
-- exclusively to the VM9/SEAL2/SEAL4 verified-failure handlers.
function DeadStrings.inject(code,seed)
  if type(code)~='string' or code=='' then return code end
  local prefix=mixedPrelude(seed)
  if code:sub(1,48)=='--[[ This, File Protected By GsXFuscator V0.6 ]]' then
    local mark=code:find(']=]',1,true)
    if not mark then error('deadstrings: malformed branded artifact',2) end
    local at=mark+2
    return code:sub(1,at)..prefix..code:sub(at+1)
  end
  return prefix..code
end

return DeadStrings
