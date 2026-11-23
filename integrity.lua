-- integrity.lua -- layer 12: self-checking runtime.
--
-- Pipeline position:
--   vmgen.emit(plan, { payload = ..., integrity = cfg })
--
-- M9 already validates its own 16-byte header once at unpack time. This layer
-- adds an independent check that does not share M9's hash, state or constants,
-- so patching the payload and recomputing M9's header checksum still trips the
-- runtime:
--
--   load    the whole packed blob is hashed again (different salt) before any
--           instruction runs
--   tick    every ~`period` dispatches one checkpoint of a six-step chain runs:
--           a rotating canary is re-hashed (SipHash, one canary per cycle of
--           checkpoints), re-measured, the running chain value must match its
--           build-time value, and two sampled handler keys must still hold the
--           exact function the runtime registered
--   audit   on the first cycle's last checkpoint every handler entry is
--           compared against the backup table and the entry count is checked,
--           so a pruned decoy or a swapped handler is caught at least once
--
-- Every failed check raises the same Lua error. Checker functions are local
-- to the generated chunk.
--
-- All arithmetic stays below 2^53 (16-bit split multiply), so the emitted
-- code behaves identically on 5.1/5.2/5.3/5.4 and Luau.
local Release = require("src.release")
local Integrity = {}

local floor = math.floor
local ceil = math.ceil
local concat = table.concat

Integrity.OFFSET = 2166136261
Integrity.PRIME = 16777619
Integrity.PRIME_LO = 403
Integrity.PRIME_HI = 256
Integrity.DEFAULTS = { period = 4096, canaryLen = 16, slice = 24 }
Integrity.CANARIES = 3
Integrity.CHECKPOINTS = 6

local ALPHABET =
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

local function makeRng(seed)
  local state = floor(tonumber(seed) or 0) % 4294967296
  if state < 0 then state = state + 4294967296 end
  return function(n)
    state = (state * 1664525 + 1013904223) % 4294967296
    return floor(state / 65536) % n + 1
  end
end

-- Bulk hash: add the byte, then multiply by the FNV prime with a 16-bit split
-- so no intermediate exceeds 2^53. Still used for payloads past BULK_LIMIT,
-- where a SipHash pass over the whole blob would cost more than it is worth.
function Integrity.hash(s, salt)
  local h = (Integrity.OFFSET + floor(tonumber(salt) or 0)) % 4294967296
  for i = 1, #s do
    h = (h + s:byte(i)) % 4294967296
    local lo = h % 65536
    local hi = (h - lo) / 65536
    h = (lo * Integrity.PRIME_LO +
      ((lo * Integrity.PRIME_HI + hi * Integrity.PRIME_LO) % 65536) *
      65536) % 4294967296
  end
  return h
end

-- SipHash-2-4 (the implementation lives in layer 9) for the short keyed
-- material: the runtime canary, and the blob itself while it is small.
-- The require is lazy because bytecode.lua -> vmgen.lua -> this module is the
-- load path, so a top-level require would close a cycle.
local function sipHash(s, k0, k1)
  return require("src.bytecode")._internals.sip32(s, k0, k1)
end
Integrity.sipHash = sipHash
Integrity.BULK_LIMIT = 131072

-- 32-bit multiply that never leaves 2^53. Fengari's lua_Integer is 32-bit, so
-- a raw `salt * 2246822519` wraps there while native 5.3/5.4 keeps the exact
-- product; the split keeps the canary key identical on every host.
local function mul32(a, b)
  local a0 = a % 65536
  local a1 = (a - a0) / 65536
  local b0 = b % 65536
  local b1 = (b - b0) / 65536
  return ((a0 + 0.0) * b0 + ((a0 * b1 + a1 * b0) % 65536) * 65536) % 4294967296
end

-- A 32-bit constant written as (a+b)%2^32 with both halves random. The runtime
-- rebuilds the key from the sum, so the key material never sits in the source
-- as one recognizable number.
local function splitNum(v, rng)
  v = floor(v) % 4294967296
  local a = rng(2147483646)
  local b = (v - a) % 4294967296
  return "(" .. a .. "+" .. b .. ")%4294967296"
end

local function joinList(t)
  local parts = {}
  for i = 1, #t do parts[i] = tostring(t[i]) end
  return concat(parts, ",")
end

function Integrity.plan(opts)
  opts = opts or {}
  local seed = floor(tonumber(opts.seed) or 0) % 4294967296
  if seed < 0 then seed = seed + 4294967296 end
  local rng = makeRng(seed + 0x1D3A)
  local period = floor(tonumber(opts.period) or (4096 + rng(2048)))
  local count = floor(tonumber(opts.canaries) or Integrity.CANARIES)
  if count < 1 then count = 1 end

  local canaries, lens, parts = {}, {}, {}
  for ci = 1, count do
    local len = floor(tonumber(opts.canaryLen) or (11 + rng(9)))
    if len < 10 then len = 10 end
    local chars = {}
    for i = 1, len do
      local idx = rng(#ALPHABET)
      chars[i] = ALPHABET:sub(idx, idx)
    end
    local canary = concat(chars)
    local cut = 3 + rng(len - 7)
    if cut < 4 then cut = 4 end
    if cut > len - 4 then cut = len - 4 end
    canaries[ci] = canary
    lens[ci] = len
    parts[ci] = { canary:sub(1, cut), canary:sub(cut + 1) }
  end

  local salt = rng(2147483646)
  local k0 = salt
  local k1 = (mul32(salt, 2246822519) + 3266489917) % 4294967296

  local digests = {}
  for ci = 1, count do
    digests[ci] = sipHash(canaries[ci], k0, k1)
  end

  local ckCount = floor(tonumber(opts.checkpoints) or Integrity.CHECKPOINTS)
  if ckCount < count then ckCount = count end
  if ckCount < 2 then ckCount = 2 end

  local chain0 = rng(2147483646)

  -- Handler samples. With a handler-key list from vmgen two distinct, unused
  -- real keys are picked per checkpoint; standalone calls fall back to random
  -- numbers and disable the full audit (total = 0).
  local keys = opts.keys
  if type(keys) ~= "table" or #keys == 0 then keys = nil end
  local total = floor(tonumber(opts.total) or 0)
  if not keys then total = 0 end
  local probeA, probeB, probeC, used = {}, {}, {}, {}
  local function pick()
    for _ = 1, 512 do
      local k
      if keys then
        k = floor(tonumber(keys[rng(#keys)]) or 0)
      else
        k = rng(4093)
      end
      if k > 0 and not used[k] then
        used[k] = true
        return k
      end
    end
    return nil
  end
  for i = 1, ckCount do
    probeA[i] = pick() or 1
    probeB[i] = pick() or 2
    probeC[i] = pick() or 3
  end

  -- The one-shot audit is followed by a rotating slice: every tick verifies a
  -- block of handler entries against the backup, wrapping once the whole table
  -- has been walked. A table swapped back to a clean-looking copy after the
  -- initial audit is therefore caught on the next pass, and the per-tick cost
  -- stays bounded (a table replace anywhere in the window is still caught by
  -- the two sampled keys and by the dispatch-time identity compare).
  local sliceSize = floor(tonumber(opts.slice) or Integrity.DEFAULTS.slice)
  if sliceSize < 4 then sliceSize = 4 end
  local slices = 1
  if total > 0 then
    slices = ceil(total / sliceSize)
    if slices < 1 then slices = 1 end
  end

  -- Build-time mirror of the runtime chain. Every tick folds the digest twice,
  -- the canary length and the step index into the running value, so a patched
  -- digest breaks the chain at that step even if the digest comparison itself
  -- was rewritten to accept it.
  local chain, checkpoints = chain0, {}
  for i = 1, ckCount do
    local ci = (i - 1) % count + 1
    chain = (chain * 1664525 + 2 * digests[ci] + lens[ci] +
      i * 2654435761 + 1013904223) % 4294967296
    checkpoints[i] = chain
  end

  return {
    seed = seed,
    period = period,
    count = count,
    checkpointCount = ckCount,
    canary = canaries[1],
    canaryLen = lens[1],
    canaries = canaries,
    canaryLens = lens,
    canaryParts = parts,
    salt = salt,
    k0 = k0,
    k1 = k1,
    k0expr = splitNum(k0, rng),
    k1expr = splitNum(k1, rng),
    saltExpr = splitNum(salt, rng),
    expect = digests[1],
    digests = digests,
    chain0 = chain0,
    checkpoints = checkpoints,
    probe = probeA[1],
    probeA = probeA,
    probeB = probeB,
    probeC = probeC,
    total = total,
    sliceSize = sliceSize,
    slices = slices,
    -- Anchor every handler, not only the checkpoint samples.  This closes the
    -- coupled H/HB edit gap for entries that the rotating samples miss.
    pinCount = total > 0 and total or 0,
  }
end

-- Standalone checkers and the VM report the same integrity error.
Integrity.FAIL = string.format("error(%q,0)", Release.integrityError)

-- State table layout (count = number of canaries):
--   1..count        canary strings, each built as "partA".."partB" at load
--   count+1..2count expected SipHash digests
--   2count+1..3count expected lengths
--   3count+1        running chain value
--   3count+2        rotating checkpoint index (0..checkpointCount-1)
--   3count+3        audit-done flag
--   3count+4        expected handler count (0 disables the audit)
--   3count+5        base period
--   3count+6        handler key A per checkpoint
--   3count+7        handler key B per checkpoint
--   3count+8        expected chain value per checkpoint
--   3count+9        rotating audit slice cursor
--   3count+10       slice size
--   3count+11       slice count
--   3count+12       handler key C per checkpoint
function Integrity.prologue(names, cfg, sipName)
  local E = names.E
  -- Hardcoded-globals handles from vmgen: the loop and the hash run on the
  -- captured library values, never on a late-bound global lookup.
  local SB = names.B1 or (names.G1 and (names.G1 .. ".byte")) or
    (E .. ".string.byte")
  local IT = names.G4 or (E .. ".type")
  local count = cfg.count or Integrity.CANARIES

  local canaryParts = {}
  for ci = 1, count do
    local p = cfg.canaryParts[ci]
    canaryParts[ci] = '"' .. p[1] .. '".."' .. p[2] .. '"'
  end

  local state = "{" .. concat(canaryParts, ",") ..
    "," .. joinList(cfg.digests) ..
    "," .. joinList(cfg.canaryLens) ..
    "," .. cfg.chain0 .. ",0,0," .. cfg.total .. "," .. cfg.period ..
    ",{" .. joinList(cfg.probeA) .. "},{" .. joinList(cfg.probeB) .. "},{" ..
    joinList(cfg.checkpoints) .. "},0," .. (cfg.sliceSize or 24) .. "," ..
    (cfg.slices or 1) .. ",{" .. joinList(cfg.probeC) .. "}}"

  local firstTick = (cfg.period + cfg.chain0 % 1021) % 4294967296

  local lines = {
    "local " .. names.UB .. "=" .. SB,
    "local " .. names.IT .. "=" .. IT,
    "local " .. names.IF .. "=function(s) return " .. sipName .. "(s," ..
      cfg.k0expr .. "," .. cfg.k1expr .. ") end",
    "local " .. names.IB .. "=function(s) local h=(2166136261+" ..
      cfg.saltExpr .. ")%4294967296 " ..
      "for i=1,#s do h=(h+" .. names.UB .. "(s,i))%4294967296 " ..
      "local a0=h%65536 local a1=(h-a0)/65536 " ..
      "h=(a0*" .. Integrity.PRIME_LO .. "+((a0*" .. Integrity.PRIME_HI ..
      "+a1*" .. Integrity.PRIME_LO .. ")%65536)*65536)%4294967296 " ..
      "end return h end",
    "local " .. names.IZ .. "=" .. state,
    "local " .. names.II .. "=0",
    "local " .. names.IP .. "=" .. firstTick,
  }
  if cfg.protoLens and names.IG and names.IGM then
    lines[#lines + 1] = "local " .. names.IG .. "={" ..
      joinList(cfg.protoLens) .. "}"
    lines[#lines + 1] = "local " .. names.IGM .. "={" ..
      joinList(cfg.protoModes) .. "}"
  end
  return lines
end

-- Emitted as the first statement of the dispatch loop. The hot path is still
-- one add and one compare; everything else runs once per tick. `cfg.pre` lets
-- the anti-debug layer advance its late-hook latch on the same schedule, and
-- `cfg.lateFlag` makes a confirmed late hook a failure of this check.
function Integrity.loop(names, cfg)
  local IT, H, HB = names.IT, names.H, names.HB
  local FAIL = cfg.fail or Integrity.FAIL
  local IZ = names.IZ
  local II, IP = names.II, names.IP
  local count = cfg.count or Integrity.CANARIES
  local cc = cfg.checkpointCount or Integrity.CHECKPOINTS
  local base = 3 * count
  local IC = base + 1
  local IX = base + 2
  local IA = base + 3
  local ITOT = base + 4
  local IPER = base + 5
  local IPA = base + 6
  local IPB = base + 7
  local ICK = base + 8
  local ISL = base + 9
  local IPC = base + 12
  local PR = names.G6 or "pairs"

  local late = ""
  if cfg.lateFlag then late = " or " .. cfg.lateFlag .. ">=2" end
  -- Independent references captured before execution. This catches coupled
  -- edits to both the live handler table and its backup on each checkpoint.
  local pinned = ""
  if names.IPIN and (cfg.pinCount or 0) > 0 then
    pinned = " or " .. H .. "[pa]~=" .. names.IPIN .. "[pa] or " ..
      HB .. "[pa]~=" .. names.IPIN .. "[pa] or " ..
      H .. "[pb]~=" .. names.IPIN .. "[pb] or " ..
      HB .. "[pb]~=" .. names.IPIN .. "[pb] or " ..
      H .. "[pe]~=" .. names.IPIN .. "[pe] or " ..
      HB .. "[pe]~=" .. names.IPIN .. "[pe]"
  end

  local audit = ""
  if cfg.total and cfg.total > 0 then
    -- Initial and periodic full-domain audits. A metatable does not prevent
    -- rawset or overwrites of existing numeric keys in standard Lua: compare
    -- BOTH table cardinalities with the independent reference set as well.
    local pinnedAudit = (cfg.pinCount or 0) > 0 and names.IPIN
    local pinCheck = pinnedAudit and (" or v~=" .. names.IPIN .. "[k]") or ""
    audit = "if " .. IZ .. "[" .. ITOT .. "]>0 and (" .. IZ .. "[" .. IA ..
      "]==0 or iq==" .. cc .. ") then " .. IZ .. "[" .. IA ..
      "]=1 local cq=0 local ch=0 " ..
      "for k,v in " .. PR .. "(" .. HB .. ") do cq=cq+1 if " .. H ..
      "[k]~=v" .. pinCheck .. " then bd=true end end " ..
      "for k,v in " .. PR .. "(" .. H .. ") do ch=ch+1 if " .. HB ..
      "[k]~=v" .. pinCheck .. " then bd=true end end " ..
      "if cq~=" .. IZ .. "[" .. ITOT .. "] or ch~=" .. IZ ..
      "[" .. ITOT .. "] then bd=true end "
    if pinnedAudit then
      audit = audit .. "local cp=0 for k,v in " .. PR .. "(" ..
        names.IPIN .. ") do cp=cp+1 if " .. H .. "[k]~=v or " ..
        HB .. "[k]~=v then bd=true end end " ..
        "if cp~=" .. IZ .. "[" .. ITOT .. "] then bd=true end "
    end
    audit = audit .. "end "
  end

  local pre = ""
  if cfg.pre and cfg.pre ~= "" then pre = cfg.pre .. " " end
  -- Extra failure predicate supplied by the caller (vmgen wires the post-load
  -- primitive snapshot here). Evaluated only on a tick, and only as another
  -- `or` term, so the per-instruction cost is unchanged.
  local extra = ""
  if cfg.extra and cfg.extra ~= "" then extra = " or (" .. cfg.extra .. ")" end
  -- Read-only seal: after the load-time guard the prototype list and both
  -- handler tables hide their metatable behind `__metatable=false`. A harness
  -- that strips the seal to inject a handler or a constant pool trips this.
  if cfg.mtFlag and names.G7 and names.P and names.H and names.HB then
    extra = extra .. " or (" .. cfg.mtFlag .. "==1 and (" .. names.G7 .. "(" ..
      names.P .. ")~=false or " .. names.G7 .. "(" ..
      names.H .. ")~=false or " .. names.G7 .. "(" .. names.HB .. ")~=false" ..
      ((cfg.pinCount or 0) > 0 and names.IPIN and
        (" or " .. names.G7 .. "(" .. names.IPIN .. ")~=false") or "") .. "))"
  end

  -- Rotating handler audit: one fixed-size slice per tick, wrapping over the
  -- whole table. The key ring is built once at load from the backup copy, so
  -- the emitted slice carries no key list of its own. A table that was
  -- restored to a plausible copy after the one-shot audit is caught on the
  -- next pass, and a pruned or padded table is caught by the length compare.
  local ring, proto = "", ""
  if (cfg.total or 0) > 0 and names.IE then
    local T = cfg.total
    local SL = cfg.sliceSize or 24
    local NS = cfg.slices or 1
    ring = "local si=" .. IZ .. "[" .. ISL .. "]+1 if si>" .. NS ..
      " then si=1 end " .. IZ .. "[" .. ISL .. "]=si local st=(si-1)*" ..
      SL .. " for z=1," .. SL .. " do local k=" .. names.IE ..
      "[(st+z-1)%" .. T .. "+1] if " .. H .. "[k]~=" .. HB ..
      "[k]" .. ((cfg.pinCount or 0) > 0 and names.IPIN and
        (" or " .. H .. "[k]~=" .. names.IPIN .. "[k] or " ..
          HB .. "[k]~=" .. names.IPIN .. "[k]") or "") ..
      " then bd=true end end "
  end
  -- Each prototype has a nonzero build-time instruction total.  Packed
  -- selfmod prototypes expose the total via Q.t while Q.c is an evictable,
  -- sparse instruction window.  Non-selfmod prototypes use the dense #Q.c.
  -- Audit all prototypes on the first checkpoint, and rotate one per later
  -- checkpoint.  A missing/invalid Q entry fails closed, not via a nil crash.
  if cfg.protoLens and cfg.protoModes and cfg.protoCount and
      names.IG and names.IGM and names.P and names.PCC then
    local N = cfg.protoCount
    local P, IG, IGM = names.P, names.IG, names.IGM
    local check = "local pp=" .. P .. "[qz] local ex=" .. IG .. "[qz] " ..
      "if " .. IT .. "(pp)~=\"table\" or " .. IT .. "(ex)~=\"number\" or ex<1 " ..
      "then bd=true elseif " .. IGM .. "[qz]==1 then " ..
      "if pp.t~=ex or " .. IT .. "(pp." .. names.PCC .. ")~=\"table\" " ..
      "then bd=true end else if " .. IT .. "(pp." .. names.PCC ..
      ")~=\"table\" or #pp." .. names.PCC ..
      "~=ex then bd=true end end "
    if cfg.protoMetadata and names.PMH then
      check = check .. " if not " .. names.PMH .. "(qz) then bd=true end "
    end
    proto = "if #" .. P .. "~=" .. N .. " then bd=true end " ..
      "if iq==1 then local pn=0 for k,v in " .. PR .. "(" .. P ..
      ") do pn=pn+1 end if pn~=" .. N .. " then bd=true end " ..
      "for qz=1," .. N ..
      " do " .. check .. "end else local qz=(iq-1)%" .. N ..
      "+1 " .. check .. " end "
  end

  -- SipHash is the one expensive step of a tick (~15x the FNV mirror). The
  -- first `count` checkpoints of every cycle hash their canary once each (the
  -- mapping iq->ci visits every canary in that window); the rest fold the
  -- stored digest, which is what the build-time mirror used anyway, so the
  -- chain stays identical and a mutated canary still trips within one cycle.
  local canaries = cfg.count or Integrity.CANARIES
  return II .. "=" .. II .. "+1 if " .. II .. ">=" .. IP .. " then " ..
    II .. "=0 " .. pre ..
    "local iq=" .. IZ .. "[" .. IX .. "]%" .. cc .. "+1 " .. IZ ..
    "[" .. IX .. "]=iq " ..
    "local ci=(iq-1)%" .. count .. "+1 " ..
    "local dv=" .. IZ .. "[" .. count .. "+ci] " ..
    "if iq<=" .. canaries .. " then dv=" .. names.IF .. "(" .. IZ ..
    "[ci]) end " ..
    IZ .. "[" .. IC .. "]=(" .. IZ .. "[" .. IC .. "]*1664525+dv+" ..
    IZ .. "[" .. count .. "+ci]+" .. IZ .. "[" .. (2 * count) .. "+ci]+" ..
    "iq*2654435761+1013904223)%4294967296 " ..
    "local pa=" .. IZ .. "[" .. IPA .. "][iq] local pb=" ..
    IZ .. "[" .. IPB .. "][iq] local pe=" .. IZ .. "[" .. IPC .. "][iq] " ..
    "local bd=dv~=" .. IZ .. "[" .. count .. "+ci] or #" .. IZ .. "[ci]~=" ..
    IZ .. "[" .. (2 * count) .. "+ci] or " .. IZ .. "[" .. IC .. "]~=" ..
    IZ .. "[" .. ICK .. "][iq] " ..
    "or " .. IT .. "(" .. H .. "[pa])~=\"function\" or " .. IT .. "(" .. H ..
    "[pb])~=\"function\" or " .. IT .. "(" .. H .. "[pe])~=\"function\" or " ..
    H .. "[pa]~=" .. HB .. "[pa] or " .. H ..
    "[pb]~=" .. HB .. "[pb] or " .. H .. "[pe]~=" .. HB .. "[pe]" ..
    pinned .. late .. extra .. " " ..
    ring .. proto ..
    audit ..
    "if bd then " .. FAIL .. " end " ..
    "if iq==" .. cc .. " then " .. IZ .. "[" .. IC .. "]=" ..
    (cfg.chain0 or 0) .. " end " ..
    IP .. "=" .. IZ .. "[" .. IPER .. "]+" .. IZ .. "[" .. IC .. "]%1021 end"end

-- Independent blob check used by the packed loader: `blob` is the final byte
-- string exactly as it is embedded, so this catches header tamper that M9's
-- own header checksum would not.
function Integrity.blobCheck(names, cfg, blob)
  local FAIL = cfg.fail or Integrity.FAIL
  local fn, expect
  if #blob <= Integrity.BULK_LIMIT then
    fn, expect = names.IF, sipHash(blob, cfg.k0, cfg.k1)
  else
    fn, expect = names.IB, Integrity.hash(blob, cfg.salt)
  end
  return "if " .. fn .. "(" .. names.D .. ")~=" .. expect .. " then " ..
    FAIL .. " end"
end

return Integrity
