-- envlog.lua -- classifies the host using the existing environment checks.
local Envlog = {}

Envlog.KEYWORDS = {
  "dumped", "dump by", "deobf", "unluac", "luadec", "decompil",
  "decrypt", "lua.deobfuscate", "dex utility", "dexplorer",
  "dex env", "environment log",
}
Envlog.WEB_KEYS = { "window", "document", "navigator", "WebAssembly", "js" }
Envlog.BOT_KEYS = { "process", "globalThis" }
Envlog.ROBLOX_KEYS = { "game", "Instance", "typeof", "workspace" }
Envlog.SCAN = 256

function Envlog.plan(opts)
  opts = opts or {}
  local seed = tonumber(opts.seed) or 0
  return {
    keywords = Envlog.KEYWORDS,
    web = Envlog.WEB_KEYS,
    bot = Envlog.BOT_KEYS,
    roblox = Envlog.ROBLOX_KEYS,
    scan = math.floor(tonumber(opts.scan) or Envlog.SCAN),
    -- Deterministic per build, different on every seed; the hex blobs in the
    -- emitted file are meaningless without it.
    key = (seed * 1103515245 + 12345) % 255 + 1,
  }
end

local function codes(text)
  local out = {}
  for i = 1, #text do out[i] = string.byte(text, i) end
  return table.concat(out, ",")
end

-- Decode the runtime keys used by the existing environment checks.
function Envlog.prologue(names, cfg)
  local E = names.E
  local TY = names.G4 or "type"
  local PC = names.G3 or "pcall"
  local ADT = names.ADT or "ADT"
  local ADE = names.ADE or "0"
  local DM = names.DM
  local KEY = math.floor(tonumber(cfg.key) or 1) % 255
  if KEY < 1 then KEY = 1 end
  local function hex(text)
    local out = {}
    for i = 1, #text do
      out[i] = string.format("%02x", (string.byte(text, i) + KEY) % 256)
    end
    return table.concat(out)
  end
  local function K(text) return "__d(" .. string.format("%q", hex(text)) .. ")" end
  local D = names.ADB or (E .. "[" .. K("debug") .. "]")
  -- The layer 11 snapshot keeps getinfo (Plain Lua) only, so the Luau
  -- fallback reads debug.info from the live table instead.
  local DE = E .. "[" .. K("debug") .. "]"
  local GI = names.AGI or (D .. "[" .. K("getinfo") .. "]")
  local S = names.ADS or (E .. "[" .. K("string") .. "]")
  local ADX = names.ADX or "function() return 1 end"
  local scan = math.floor(tonumber(cfg.scan) or Envlog.SCAN)

  local function presence(keys)
    local parts = {}
    for i = 1, #keys do
      local v = "E[" .. K(keys[i]) .. "]"
      parts[i] = "(" .. TY .. "(" .. v .. ")==\"table\" or " .. TY .. "(" ..
        v .. ")==\"function\" or " .. TY .. "(" .. v .. ")==\"userdata\")"
    end
    return "(" .. table.concat(parts, " or ") .. ")"
  end
  local function defined(keys)
    local parts = {}
    for i = 1, #keys do
      parts[i] = "E[" .. K(keys[i]) .. "]~=nil"
    end
    return "(" .. table.concat(parts, " or ") .. ")"
  end
  local kwParts = {}
  for i = 1, #cfg.keywords do kwParts[i] = K(cfg.keywords[i]) end

  -- Load-time pass. EL packs banner (x8) | web (x1) | bot (x2) | roblox (x4).
  -- BN holds the matched keyword index.
  -- Plain Lua reads the chunk name through getinfo(n, "S"); Luau has only
  -- debug.info(level, "s"), so that string form is the fallback there.
  -- Decoder shared by every literal below. It resolves string.char/gsub and
  -- tonumber from the live environment once per call, so the layer needs a
  -- single chunk-local name (`__d`, with underscores generated names never
  -- carry) and no extra register pressure. A host without string.gsub simply
  -- yields empty literals; the scan then has nothing to match.
  local dec =
    "local __d=function(h) local s=" .. E .. "[" .. DM .. "(" ..
      codes("string") .. ")] " ..
    "local c=s and s[" .. DM .. "(" .. codes("char") .. ")] " ..
    "local g=s and s[" .. DM .. "(" .. codes("gsub") .. ")] " ..
    "local t=" .. E .. "[" .. DM .. "(" .. codes("tonumber") .. ")] " ..
    "if not (c and g and t) then return \"\" end " ..
    "return (g(h,\"%x%x\",function(x) return c((t(x,16)-" .. KEY ..
      ")%256) end)) end"

  local lines = {
    dec,
    "local EL=0 local BN=0 " ..
      PC .. "(function() local E=" .. E .. " local TY=" .. TY ..
      " local D=" .. D .. " local S=" .. S ..
      " local SF=S and S[" .. K("find") .. "] local US=S and S[" ..
      K("sub") .. "] " ..
      "local WK=" .. presence(cfg.web) .. " and 1 or 0 " ..
      "local BK=" .. presence(cfg.bot) .. " and 1 or 0 " ..
      "local RB=" .. defined(cfg.roblox) .. " and 1 or 0 local tx=\"\" " ..
      "if D and TY(D[" .. GI .. "])==\"function\" then " ..
      "local ok,a=" .. PC .. "(D[" .. GI .. "]," .. ADX .. ",\"S\") " ..
      "if ok and TY(a)==\"table\" then local ss=a[" .. K("short_src") ..
      "] local sc=a[" .. K("source") .. "] " ..
      "if TY(ss)==\"string\" then tx=ss end " ..
      "if TY(sc)==\"string\" and TY(US)==\"function\" then tx=tx..\" \"..US(sc,1," ..
      scan .. ") end end " ..
      "elseif " .. DE .. " and TY(" .. DE .. "[" .. K("info") ..
      "])==\"function\" then " ..
      "local ok,ss=" .. PC .. "(" .. DE .. "[" .. K("info") .. "],2,\"s\") " ..
      "if ok and TY(ss)==\"string\" then tx=ss end end " ..
      "local SL=S and S[" .. K("lower") .. "] " ..
      "if TY(SL)==\"function\" and TY(tx)==\"string\" then tx=SL(tx) end " ..
      "if TY(SF)==\"function\" and #tx>0 then local KV={" ..
      table.concat(kwParts, ",") .. "} " ..
      "for i=1,#KV do if SF(tx,KV[i],1,true) then BN=i end end end " ..
      "EL=BN*8+WK+BK*2+RB*4 end)",
  }
  lines[#lines + 1] =
    "local HF=EL%8 if EL-HF>=8 or " ..
    "(HF%4~=0 and HF<4 and " .. ADE .. "==0) then " .. ADT .. "=1 end"
  return lines
end

return Envlog
