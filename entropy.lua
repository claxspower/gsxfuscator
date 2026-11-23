-- entropy.lua -- best-effort per-build, 32-bit entropy source for Lua 5.1+.
-- A seed diversifies generated output; it is NOT a secret or crypto key.
-- Use OS randomness if available, otherwise monotonic clock/counter fallback.
local Entropy = {}
local counter = 0
local MOD = 4294967296

local function osSeed()
  if type(io) ~= "table" or type(io.open) ~= "function" then return nil end
  local ok, bytes = pcall(function()
    local f = io.open("/dev/urandom", "rb")
    if not f then return nil end
    local data = f:read(4)
    f:close()
    return data
  end)
  if not ok or type(bytes) ~= "string" or #bytes ~= 4 then return nil end
  local a, b, c, d = string.byte(bytes, 1, 4)
  return (a + b * 256 + c * 65536 + d * 16777216) % MOD
end

function Entropy.seed()
  counter = (counter + 1) % MOD
  local seed = osSeed()
  if seed ~= nil then return seed end
  local t = type(os) == "table" and type(os.time) == "function"
    and os.time() or 0
  local c = type(os) == "table" and type(os.clock) == "function"
    and os.clock() or 0
  local r = type(math.random) == "function"
    and math.floor(math.random() * MOD) or 0
  -- The fallback prevents identical seeds on consecutive calls in a single
  -- process but makes NO unpredictability or uniqueness guarantee.
  return (t * 7919 + math.floor(c * 1000000) * 104729 + r +
    counter * 2654435761) % MOD
end

return Entropy
