-- selfmod.lua -- layer 10: self-modifying, block-chained bytecode storage.
--
-- Pipeline position:
--   compiler -> vmgen.randomize (plan) -> selfmod.apply -> bytecode.pack
--   -> vmgen.emit (payload)
--
-- Layer 9 already hides the whole prototype stream behind one encrypted blob.
-- This layer removes the plain instruction list from memory as well: each
-- prototype's code is split into blocks, each block is stored as
--   4-byte LE state .. keystream-XOR( FNV-1a32(payload) .. varint stream )
-- and the runtime decodes only the blocks it is about to execute. Leaving a
-- block re-encrypts it in place with a fresh state and keystream offset, so the
-- stored bytes change while the chunk runs.
--
-- The window is the whole prototype up to MAX_BLOCKS * BLOCK instructions.
-- Anything below that limit stays resident after its first pass, which is the
-- only shape that keeps a game loop at frame rate: a called prototype walks
-- its whole body, so a smaller window re-decodes (and re-checksums) its own
-- blocks on every call. A 256-word window over a flattened ~430-word function
-- cost 113 s for 20k calls against 6 s resident; a hot per-frame handler with a
-- larger body would stall the client the same way. Above the ceiling the window
-- slides and only cold, generated-once code pays the re-decode. Every block key
-- mixes a chain value computed from the previous block's build-time ciphertext,
-- which binds the blocks in order.
--
-- The decoder in src/vmgen.lua mirrors `decodeBlock` and `crypt` exactly.
local Bytecode = require("src.bytecode")

local Selfmod = {}

local I = Bytecode._internals
local floor = math.floor
local ceil = math.ceil
local char = string.char
local byte = string.byte
local sub = string.sub
local concat = table.concat

local fnv1a, xor8, le32 = I.fnv1a, I.xor8, I.le32
local uvar, zigzag, encodeField = I.uvar, I.zigzag, I.encodeField

Selfmod.BLOCK = 8
Selfmod.MAX_BLOCKS = 1024
Selfmod.WINDOW_FLOOR = 8192

-- ------------------------------------------------------------------- crypto
-- Stream constants are shared verbatim with the emitted runtime. The 32-bit
-- block state is mixed through two 16-bit halves so every product stays under
-- 2^53 on 5.1/5.2 and under 2^63 on 5.3/5.4.
local function streamState(master, pi, bi, state, chain)
  return (master + pi * 2654435761 + bi * 2246822519 + (state % 65536) +
    floor(state / 65536) * 40961 + chain) % 4294967296
end

local function crypt(data, master, pi, bi, state, chain)
  local st = streamState(master, pi, bi, state, chain)
  local out = {}
  local n = #data
  local i = 1
  while i + 3 <= n do
    local b0, b1, b2, b3 = byte(data, i, i + 3)
    st = (st * 1664525 + 1013904223) % 4294967296
    local k0 = floor(st / 16777216) % 256
    st = (st * 1664525 + 1013904223) % 4294967296
    local k1 = floor(st / 16777216) % 256
    st = (st * 1664525 + 1013904223) % 4294967296
    local k2 = floor(st / 16777216) % 256
    st = (st * 1664525 + 1013904223) % 4294967296
    local k3 = floor(st / 16777216) % 256
    out[#out + 1] = char(xor8(b0, k0), xor8(b1, k1), xor8(b2, k2), xor8(b3, k3))
    i = i + 4
  end
  while i <= n do
    st = (st * 1664525 + 1013904223) % 4294967296
    out[#out + 1] = char(xor8(byte(data, i), floor(st / 16777216) % 256))
    i = i + 1
  end
  return concat(out)
end

local function encodeInstr(ins)
  return uvar(ins[1]) .. uvar(zigzag(ins[2] or 0)) ..
    uvar(zigzag(ins[3] or 0)) .. uvar(zigzag(ins[4] or 0)) ..
    encodeField(ins[5] or 0)
end

local function encodeSlice(code, from, count)
  local parts = {}
  for i = from, from + count - 1 do parts[#parts + 1] = encodeInstr(code[i]) end
  local payload = concat(parts)
  return le32(fnv1a(payload)) .. payload
end

local function unzigzag(v)
  if v % 2 == 1 then return -floor((v + 1) / 2) end
  return floor(v / 2)
end

-- Mirrors the emitted block loader's parser. Block layout:
--   4-byte LE state .. keystream-XOR(FNV-1a32(payload) .. payload)
local function decodeBlock(master, pi, bi, blk, chain, total, B)
  if type(blk) ~= "string" or #blk < 9 then
    return nil, "block: truncated"
  end
  local state = byte(blk, 1) + byte(blk, 2) * 256 +
    byte(blk, 3) * 65536 + byte(blk, 4) * 16777216
  local plain = crypt(sub(blk, 5), master, pi, bi, state, chain)
  local chk = byte(plain, 1) + byte(plain, 2) * 256 +
    byte(plain, 3) * 65536 + byte(plain, 4) * 16777216
  local payload = sub(plain, 5)
  if fnv1a(payload) ~= chk then return nil, "block: checksum mismatch" end
  local pos = 1
  local function rd()
    local v, m = 0, 1
    while true do
      local b = byte(payload, pos)
      pos = pos + 1
      v = v + (b % 128) * m
      if b < 128 then return v end
      m = m * 128
    end
  end
  local function rf()
    local tag = byte(payload, pos)
    pos = pos + 1
    if tag == 0 then return unzigzag(rd()) end
    if tag == 3 then
      local ln = rd()
      local s = tonumber(sub(payload, pos, pos + ln - 1))
      pos = pos + ln
      return s
    end
    if tag == 5 then return math.huge end
    if tag == 6 then return -math.huge end
    if tag == 7 then return 0 / 0 end
    error("block: bad field tag " .. tostring(tag), 0)
  end
  local need = B
  local last = total - (bi - 1) * B
  if last < need then need = last end
  local out = {}
  for i = 1, need do
    out[i] = { rd(), unzigzag(rd()), unzigzag(rd()), unzigzag(rd()), rf() }
  end
  return out, plain
end

-- --------------------------------------------------------------------- apply
function Selfmod.apply(plan, opts)
  opts = opts or {}
  if type(plan) ~= "table" or type(plan.protos) ~= "table" then
    error("selfmod: vmgen plan expected", 0)
  end
  local B = floor(opts.blockSize or Selfmod.BLOCK)
  if B < 1 then B = Selfmod.BLOCK end
  local maxBlocks = floor(opts.maxBlocks or Selfmod.MAX_BLOCKS)
  if maxBlocks < 1 then maxBlocks = 1 end
  local seed = floor(tonumber(opts.seed) or tonumber(plan.seed) or 0) %
    4294967296
  if seed < 0 then seed = seed + 4294967296 end
  local master = opts.key
  if master == nil then master = Bytecode.deriveKey(seed) end
  master = floor(tonumber(master) or 0) % 4294967296
  if master < 0 then master = master + 4294967296 end

  local stats = {
    master = master, blockSize = B, protos = 0, blocks = 0,
    instructions = 0, bytes = 0, liveCap = 0, maxBlocks = 0,
  }
  for pi = 1, #plan.protos do
    local P = plan.protos[pi]
    local code = P.c
    local total = #code
    if total > 0 then
      local nb = ceil(total / B)
      -- Whole-body residency below the ceiling; a sliding window above it.
      local cap = total
      if cap > maxBlocks * B then cap = maxBlocks * B end
      local blocks, chain = {}, {}
      local prev = le32(master) .. char(pi % 256)
      for bi = 1, nb do
        local from = (bi - 1) * B + 1
        local count = total - from + 1
        if count > B then count = B end
        local plain = encodeSlice(code, from, count)
        local chVal = fnv1a(prev .. char(pi % 256, bi % 256))
        local state = (seed + pi * 7919 + bi * 104729) % 4294967296
        state = (state * 1664525 + 1013904223) % 4294967296
        local tail = crypt(plain, master, pi, bi, state, chVal)
        blocks[bi] = le32(state) .. tail
        chain[bi] = chVal
        prev = blocks[bi]
        stats.bytes = stats.bytes + #blocks[bi]
      end
      P.sm = true
      P.B = B
      P.cap = cap
      P.total = total
      P.blocks = blocks
      P.chain = chain
      P.c = {}
      stats.protos = stats.protos + 1
      stats.blocks = stats.blocks + nb
      stats.instructions = stats.instructions + total
      if cap > stats.liveCap then stats.liveCap = cap end
      if nb > stats.maxBlocks then stats.maxBlocks = nb end
    end
  end
  return stats
end

-- -------------------------------------------------------------------- replay
-- Test aid: replays the emitted loader's decode/evict/re-encrypt cycle on a
-- copy of the blocks and reports how much it mutated and how many instructions
-- were decoded at once. The plan itself is not modified.
function Selfmod.replay(plan, opts)
  opts = opts or {}
  local master = opts.key or Bytecode.deriveKey(opts.seed or plan.seed or 0)
  master = floor(tonumber(master) or 0) % 4294967296
  if master < 0 then master = master + 4294967296 end
  local out = {
    visits = 0, decodes = 0, mutations = 0, maxLive = 0,
    changed = 0, sampleOld = nil, sampleNew = nil, error = nil,
  }
  for pi = 1, #plan.protos do
    local P = plan.protos[pi]
    if P.sm then
      local B, total, cap = P.B, P.total, P.cap
      local blocks = {}
      for i = 1, #P.blocks do blocks[i] = P.blocks[i] end
      local raw, queue, seed = {}, {}, master
      for pc = 1, total do
        local bi = floor((pc - 1) / B) + 1
        out.visits = out.visits + 1
        if not raw[bi] then
          local need = B
          local last = total - (bi - 1) * B
          if last < need then need = last end
          local liveCount = 0
          for i = 1, #P.blocks do
            if raw[i] then
              local cnt = B
              local lt = total - (i - 1) * B
              if lt < cnt then cnt = lt end
              liveCount = liveCount + cnt
            end
          end
          while liveCount + need > cap and #queue > 0 do
            local old = table.remove(queue, 1)
            local cnt = B
            local lt = total - (old - 1) * B
            if lt < cnt then cnt = lt end
            seed = (seed * 1664525 + 1013904223) % 4294967296
            local state = seed
            local nextBlock = le32(state) .. crypt(raw[old], master, pi, old,
              state, P.chain[old])
            if nextBlock ~= blocks[old] then
              out.changed = out.changed + 1
              if not out.sampleOld then
                out.sampleOld = blocks[old]
                out.sampleNew = nextBlock
              end
            end
            blocks[old] = nextBlock
            raw[old] = nil
            liveCount = liveCount - cnt
            out.mutations = out.mutations + 1
          end
          local list, plain = decodeBlock(master, pi, bi, blocks[bi],
            P.chain[bi], total, B)
          if not list then
            out.error = plain
            return out
          end
          raw[bi] = plain
          queue[#queue + 1] = bi
          out.decodes = out.decodes + 1
          liveCount = liveCount + need
          if liveCount > out.maxLive then out.maxLive = liveCount end
        end
      end
    end
  end
  return out
end

Selfmod._internals = {
  crypt = crypt, encodeInstr = encodeInstr, encodeSlice = encodeSlice,
  decodeBlock = decodeBlock, unzigzag = unzigzag,
}

return Selfmod
