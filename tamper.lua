-- tamper.lua -- game-side tamper surface for VM artifacts.
--
--   Tamper.emit(names) -> source
--
-- Roblox runs the program on real userdata with real value types; every devirt
-- harness, offline replay runner and API mock has to re-implement that surface
-- and gets some of it wrong. These probes compare cheap, deterministic
-- invariants of the live client (value semantics, instance method results,
-- GUID shape, service identity) and count only the ones that answer *wrong*.
--
-- Missing or raising API is skipped, never counted: stripped executors lose
-- features all the time and must stay quiet. A probe counts only when the
-- surface it needs exists and still produces an impossible answer. Only a
-- live DataModel is probed (`typeof(game)=="Instance"`), so the browser verify
-- sandbox and desktop Lua hosts run this block as a no-op.
--
-- Confirmed failures raise a Lua error.
local Release = require("src.release")
local Tamper = {}

local function codes(s)
  local t = {}
  for i = 1, #s do t[i] = string.byte(s, i) end
  return table.concat(t, ",")
end

Tamper.THRESHOLD = 3

function Tamper.emit(n, opts)
  opts = opts or {}
  local E, PC, TY, DM = n.E, n.G3, n.G4, n.DM
  local kill = opts.kill or string.format("error(%q,0)", Release.integrityError)
  local function L(s) return DM .. "(" .. codes(s) .. ")" end
  local out = {}
  local function a(s) out[#out + 1] = s end

  a("do")
  a("local _ty=" .. E .. "[" .. L("typeof") .. "]")
  a("if " .. TY .. "(_ty)==\"function\" then")
  a("local _to,_tg=" .. PC .. "(_ty," .. E .. "[" .. L("game") .. "])")
  a("if _to and _tg==\"Instance\" then")
  a("local _tt,_tn=0,0")
  a("local function _tq(_tf)_tn=_tn+1 local _ok,_v=" .. PC .. "(_tf)if _ok and _v~=true then _tt=_tt+1 end end")

  -- DataModel identity: a mock can expose a table named game but cannot make
  -- typeof answer Instance without also faking the value model the remaining
  -- probes contradict.
  a("_tq(function()local _g=" .. E .. "[" .. L("game") .. "]local _w=" .. E .. "[" ..
    L("workspace") .. "]return _ty(_g)==\"Instance\" and _ty(_w)==\"Instance\" and _g.ClassName==\"DataModel\" and _w.ClassName==\"Workspace\" end)")

  -- Value types: positions are exact for integral input, the unit vector of a
  -- basis vector is itself, Color3 equality is componentwise.
  a("_tq(function()local _c=" .. E .. "[" .. L("CFrame") .. "]local _n=_c[\"new\"]if " ..
    TY .. "(_n)~=\"function\"then return true end local _f=_n(5,2,1)if _ty" ..
    "(_f)~=\"CFrame\"then return false end local _p=_f.Position return _ty" ..
    "(_p)==\"Vector3\" and _p.X==5 and _p.Y==2 and _p.Z==1 end)")

  a("_tq(function()local _n=" .. E .. "[" .. L("Vector3") .. "][\"new\"]if " .. TY ..
    "(_n)~=\"function\"then return true end local _u=_n(1,0,0).Unit return _ty" ..
    "(_u)==\"Vector3\" and _u.X==1 and _u.Y==0 and _u.Z==0 end)")

  a("_tq(function()local _c=" .. E .. "[" .. L("Color3") .. "]if " .. TY ..
    "(_c[\"new\"])~=\"function\" or " .. TY .. "(_c[\"fromRGB\"])~=\"function\"then return true end local _a=_c[\"new\"](1,0,0)return _ty" ..
    "(_a)==\"Color3\" and _a.R==1 and _a.G==0 and _a.B==0 and _a==_c[\"fromRGB\"](255,0,0) end)")

  -- TweenInfo.Time is single precision, so compare with a band, not equality.
  a("_tq(function()local _n=" .. E .. "[" .. L("TweenInfo") .. "][\"new\"]if " .. TY ..
    "(_n)~=\"function\"then return true end local _v=_n(0.1)if _ty" ..
    "(_v)~=\"TweenInfo\"then return false end local _t=_v.Time return " .. TY ..
    "(_t)==\"number\" and _t>0.05 and _t<0.2 end)")

  -- Instance semantics: class answer, inheritance answer, unparented destroy.
  a("_tq(function()local _n=" .. E .. "[" .. L("Instance") .. "][\"new\"]if " .. TY ..
    "(_n)~=\"function\"then return true end local _p=_n(" .. L("Part") .. ")if _ty" ..
    "(_p)~=\"Instance\"then return false end local _ok=_p.ClassName==\"Part\" and _p:IsA(" ..
    L("BasePart") .. ")==true and _p:IsA(" .. L("Model") .. ")==false if " .. TY ..
    "(_p.Destroy)~=\"function\"then return _ok end _p:Destroy()return _ok and _p.Parent==nil end)")

  a("_tq(function()local _n=" .. E .. "[" .. L("Instance") .. "][\"new\"]if " .. TY ..
    "(_n)~=\"function\"then return true end local _f=_n(" .. L("Folder") .. ")if _ty" ..
    "(_f)~=\"Instance\"then return false end if " .. TY .. "(_f.SetAttribute)~=\"function\"then return _f.ClassName==\"Folder\" end _f:SetAttribute(" ..
    L("x") .. ",123)local _v=_f:GetAttribute(" .. L("x") .. ")local _ok=_f.ClassName==\"Folder\"and _v==123 " ..
    PC .. "(function()_f:Destroy()end)return _ok end)")

  a("_tq(function()local _e=" .. E .. "[" .. L("Enum") .. "]local _u=_e and _e.UserCFrame if _u==nil then return true end local _i=_u.Head if _i==nil then return true end return _ty" ..
    "(_i)==\"EnumItem\" and _i.Name==\"Head\" end)")

  a("_tq(function()local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
    "(_g.GetService)~=\"function\"then return true end local _ho,_h=" .. PC ..
    "(_g.GetService,_g," .. L("HttpService") .. ")if not _ho then return true end if _h==nil then return true end if " ..
    TY .. "(_h.GenerateGUID)~=\"function\"then return false end local _a=_h:GenerateGUID(false)local _b=_h:GenerateGUID(false)if " ..
    TY .. "(_a)~=\"string\" or #_a~=36 then return false end local _s=" .. E .. "[" ..
    L("string") .. "]return _a~=_b and _s.sub(_a,9,9)==\"-\" and _s.sub(_a,14,14)==\"-\" and _s.sub(_a,19,19)==\"-\" and _s.sub(_a,24,24)==\"-\" end)")

  a("_tq(function()local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
    "(_g.GetService)~=\"function\"then return true end local _o,_v=" .. PC ..
    "(function()return _g:GetService(" .. L("GuiService") .. "):GetGuiInset()end)if not " ..
    "_o then return true end return _ty" .. "(_v)==\"Vector2\" and " .. TY ..
    "(_v.X)==\"number\" end)")

  a("_tq(function()local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
    "(_g.GetService)~=\"function\"then return true end local _o,_v=" .. PC ..
    "(function()return _g:GetService(" .. L("UserInputService") .. "):GetLastInputType()end)if not _o then return true end return _ty" ..
    "(_v)==\"EnumItem\" end)")

  a("_tq(function()local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
    "(_g.GetService)~=\"function\"then return true end local _o,_v=" .. PC ..
    "(function()return _g:GetService(" .. L("Lighting") .. "):GetMinutesAfterMidnight()end)if not _o then return true end return " ..
    TY .. "(_v)==\"number\" end)")

  a("_tq(function()local _n=" .. E .. "[" .. L("RaycastParams") .. "][\"new\"]if " .. TY ..
    "(_n)~=\"function\"then return true end local _r=_n()if _ty" ..
    "(_r)~=\"RaycastParams\"then return false end _r.CollisionGroup=" .. L("Default") ..
    " return _r.CollisionGroup==\"Default\" end)")

  a("_tq(function()local _n=" .. E .. "[" .. L("OverlapParams") .. "][\"new\"]if " .. TY ..
    "(_n)~=\"function\"then return true end return _ty(_n())==\"OverlapParams\" end)")

  a("_tq(function()local _n=" .. E .. "[" .. L("Vector3int16") .. "][\"new\"]if " .. TY ..
    "(_n)~=\"function\"then return true end return _ty(_n(0,0,0))==\"Vector3int16\" end)")

  a("_tq(function()local _g=" .. E .. "[" .. L("game") .. "]local _n=" .. E ..
    "[" .. L("Instance") .. "][\"new\"]local _ti=" .. E .. "[" .. L("TweenInfo") ..
    "][\"new\"]if " .. TY .. "(_n)~=\"function\" or " .. TY .. "(_ti)~=\"function\" or " .. TY ..
    "(_g.GetService)~=\"function\"then return true end local _p=_n(" .. L("Part") ..
    ")local _o,_t=" .. PC .. "(function()local _s=_g:GetService(" .. L("TweenService") ..
    ")return _s:Create(_p,_ti(0.1),{[" .. L("Transparency") .. "]=1})end)if not _o or _ty" ..
    "(_t)~=\"Instance\"then " .. PC .. "(function()_p:Destroy()end)return false end local _ok=_t:IsA(" ..
    L("Tween") .. ")==true " .. PC .. "(function()_t:Destroy()end)" .. PC ..
    "(function()_p:Destroy()end)return _ok end)")

  a("_tq(function()local _p=" .. E .. "[" .. L("Players") .. "]if _ty" ..
    "(_p)~=\"Instance\"then return true end local _g=" .. E .. "[" .. L("game") ..
    "]if " .. TY .. "(_g.GetService)~=\"function\"then return true end return " ..
    "_g:GetService(" .. L("Players") .. ")==_p end)")

  a("_tq(function()local _w=" .. E .. "[" .. L("workspace") .. "]if _ty" ..
    "(_w)~=\"Instance\"then return true end local _o,_v=" .. PC ..
    "(function()return _w:GetServerTimeNow()end)if not _o then return true end return " ..
    TY .. "(_v)==\"number\" end)")

  -- Second band: service identity, DataModel root shape, real IDs, the local
  -- player and the flags of the two services a mock most often stubs. Each one
  -- is still skipped when the surface is missing; a contradiction counts once.
  local extra = {
    "local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
      "(_g.GetService)~=\"function\"then return true end local _o,_r=" .. PC ..
      "(_g.GetService,_g," .. L("Workspace") .. ")if not _o then return true end return _r==" ..
      E .. "[" .. L("workspace") .. "] end",
    "local _g=" .. E .. "[" .. L("game") .. "]return _ty(_g)==\"Instance\" and _g.ClassName==\"DataModel\" and _g.Parent==nil end",
    "local _g=" .. E .. "[" .. L("game") .. "]return " .. TY .. "(_g.PlaceId)==\"number\" and " ..
      TY .. "(_g.GameId)==\"number\" and " .. TY .. "(_g.JobId)==\"string\" end",
    "local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
      "(_g.GetService)~=\"function\"then return true end local _o,_p=" .. PC ..
      "(_g.GetService,_g," .. L("Players") .. ")if not _o or _ty(_p)~=\"Instance\"then return true end local _l=_p.LocalPlayer if _l==nil then return true end return _ty(_l)==\"Instance\" and " ..
      TY .. "(_l.UserId)==\"number\" end",
    "local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
      "(_g.GetService)~=\"function\"then return true end local _o,_r=" .. PC ..
      "(_g.GetService,_g," .. L("RunService") .. ")if not _o or _ty(_r)~=\"Instance\"then return true end local _o2,_c=" ..
      PC .. "(function()return _r:IsClient()end)local _o3,_s=" .. PC ..
      "(function()return _r:IsStudio()end)if not _o2 or not _o3 then return true end return " ..
      TY .. "(_c)==\"boolean\" and " .. TY .. "(_s)==\"boolean\" end",
    "local _w=" .. E .. "[" .. L("workspace") .. "]if _ty" ..
      "(_w)~=\"Instance\"then return true end return " .. TY .. "(_w.Gravity)==\"number\" end",
    "local _w=" .. E .. "[" .. L("workspace") .. "]if _ty" ..
      "(_w)~=\"Instance\"then return true end local _c=_w.CurrentCamera if _c==nil then return true end return _ty(_c)==\"Instance\" and _c.ClassName==\"Camera\" and _ty(_c.CFrame)==\"CFrame\" end",
    "local _u=" .. E .. "[" .. L("UDim2") .. "][\"new\"]if " .. TY ..
      "(_u)~=\"function\"then return true end local _v=_u(0.25,0,0.5,0)return _ty(_v)==\"UDim2\" and _v.X.Scale==0.25 and _v.Y.Scale==0.5 and _v.X.Offset==0 end",
    "local _n=" .. E .. "[" .. L("Vector2") .. "][\"new\"]if " .. TY ..
      "(_n)~=\"function\"then return true end local _m=_n(3,4).Magnitude return " ..
      TY .. "(_m)==\"number\" and _m>4.999 and _m<5.001 end",
    "local _e=" .. E .. "[" .. L("Enum") .. "]local _k=_e and _e.KeyCode if _k==nil then return true end local _a=_k.A if _a==nil then return true end return _ty(_a)==\"EnumItem\" and _a.Name==\"A\" and " ..
      TY .. "(_a.Value)==\"number\" end",
    "local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
      "(_g.GetService)~=\"function\"then return true end local _o,_u=" .. PC ..
      "(_g.GetService,_g," .. L("UserInputService") .. ")if not _o or _ty(_u)~=\"Instance\"then return true end return " ..
      TY .. "(_u.TouchEnabled)==\"boolean\" and " .. TY .. "(_u.KeyboardEnabled)==\"boolean\" end",
    "local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
      "(_g.GetService)~=\"function\"then return true end local _o,_r=" .. PC ..
      "(_g.GetService,_g," .. L("ReplicatedStorage") .. ")if not _o or _ty(_r)~=\"Instance\"then return true end return _r.Parent==_g end",
    -- Value-type duality: a real Vector3 answers "userdata" to type() and
    -- "Vector3" to typeof(), and arithmetic stays in the same value model.
    -- Table-based emulations pass the constructor but fail the duality or the
    -- arithmetic.
    "local _n=" .. E .. "[" .. L("Vector3") .. "][\"new\"]if " .. TY ..
      "(_n)~=\"function\"then return true end local _a,_b=_n(2,3,4),_n(1,1,1)if " ..
      TY .. "(_a)~=\"userdata\" or _ty(_a)~=\"Vector3\"then return false end local _c=_a+_b local _d=_a*2 return " ..
      TY .. "(_c)~=\"userdata\" and _c.X==3 and _c.Y==4 and _c.Z==5 and _d.X==4 and _d.Y==6 and _d.Z==8 end",
    -- CFrame composition: (1,2,3)*(1,1,1) must land on (2,3,4).
    "local _n=" .. E .. "[" .. L("CFrame") .. "][\"new\"]if " .. TY ..
      "(_n)~=\"function\"then return true end local _f=_n(1,2,3)*_n(1,1,1)local _p=_f.Position return " ..
      TY .. "(_f)==\"userdata\" and _ty(_p)==\"Vector3\" and _p.X==2 and _p.Y==3 and _p.Z==4 end",
    "local _n=" .. E .. "[" .. L("UDim") .. "][\"new\"]if " .. TY ..
      "(_n)~=\"function\"then return true end local _v=_n(1,2)return " ..
      TY .. "(_v)==\"userdata\" and _ty(_v)==\"UDim\" and _v.Scale==1 and _v.Offset==2 end",
    "local _n=" .. E .. "[" .. L("Rect") .. "][\"new\"]if " .. TY ..
      "(_n)~=\"function\"then return true end local _v=_n(0,0,10,20)return " ..
      TY .. "(_v)==\"userdata\" and _ty(_v)==\"Rect\" and _v.Width==10 and _v.Height==20 end",
    "local _n=" .. E .. "[" .. L("NumberRange") .. "][\"new\"]if " .. TY ..
      "(_n)~=\"function\"then return true end local _a,_b=_n(2,5),_n(7)if " ..
      TY .. "(_a)~=\"userdata\" or _ty(_a)~=\"NumberRange\"then return false end return _a.Min==2 and _a.Max==5 and _b.Min==7 and _b.Max==7 end",
    -- Instance property round trip: writes must read back in the same value
    -- model a live client provides.
    "local _n=" .. E .. "[" .. L("Instance") .. "][\"new\"]local _v=" .. E ..
      "[" .. L("Vector3") .. "]if " .. TY .. "(_n)~=\"function\" or " .. TY ..
      "(_v)~=\"table\" or " .. TY .. "(_v[\"new\"])~=\"function\"then return true end local _p=_n(" ..
      L("Part") .. ")if " .. TY .. "(_p)~=\"userdata\"then return false end local _o=" .. PC ..
      "(function()_p.Size=_v[\"new\"](2,3,4)_p.Anchored=true _p.Transparency=0.5 end)if not _o then return false end local _ok=_p.Size.X==2 and _p.Size.Y==3 and _p.Size.Z==4 and _p.Anchored==true and _p.Transparency==0.5 " ..
      PC .. "(function()_p:Destroy()end)return _ok end",
    -- JSON round trip on the real serializer: array output is stable text.
    "local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
      "(_g.GetService)~=\"function\"then return true end local _o,_h=" .. PC ..
      "(_g.GetService,_g," .. L("HttpService") .. ")if not _o or _h==nil or " .. TY ..
      "(_h[" .. L("JSONEncode") .. "])~=\"function\" or " .. TY .. "(_h[" ..
      L("JSONDecode") .. "])~=\"function\"then return true end local _s,_d=" ..
      PC .. "(function()return _h[" .. L("JSONEncode") .. "](_h,{1,2,3}),_h[" ..
      L("JSONDecode") .. "](_h,\"[4,5]\")end)if not _s then return false end if _s~=\"[1,2,3]\"then return false end return " ..
      TY .. "(_d)==\"table\" and _d[2]==5 end",
    "local _g=" .. E .. "[" .. L("game") .. "]if " .. TY ..
      "(_g.GetService)~=\"function\"then return true end local _o,_d=" .. PC ..
      "(_g.GetService,_g," .. L("Debris") .. ")if not _o or _d==nil then return true end return _ty" ..
      "(_d)==\"Instance\" and _d.ClassName==\"Debris\" end",
    -- IsA inheritance on the two root instances: a mock that fakes ClassName
    -- strings still has to answer IsA consistently.
    "local _g=" .. E .. "[" .. L("game") .. "]local _w=" .. E .. "[" .. L("workspace") ..
      "]local _o,_a=" .. PC .. "(function()return _g:IsA(" .. L("DataModel") ..
      "),_w:IsA(" .. L("Workspace") .. ")end)if not _o then return true end return _ty(_g)==\"Instance\" and _a==true end",
    -- Third band: the pure-Lua core a replay harness has to re-implement, plus
    -- the remaining leaf instance classes. Exact integer math, real varargs,
    -- stable string ops; each entry still skips a stripped surface instead of
    -- counting it.
    "local _m=" .. E .. "[" .. L("math") .. "]if " .. TY ..
      "(_m)~=\"table\" or " .. TY .. "(_m.floor)~=\"function\"then return true end return " ..
      "_m.floor(-0.5)==-1 and _m.ceil(-0.5)==0 and _m.abs(-3)==3 and _m.max(1,2)==2 and " ..
      "_m.min(1,2)==1 and _m.huge>0 end",
    "local _s=" .. E .. "[" .. L("string") .. "]if " .. TY ..
      "(_s)~=\"table\" or " .. TY .. "(_s.format)~=\"function\" or " .. TY ..
      "(_s.rep)~=\"function\"then return true end return " ..
      "_s.format(\"%d-%s\",7,\"x\")==\"7-x\" and _s.rep(\"ab\",3)==\"ababab\" and _s.rep(\"x\",0)==\"\" end",
    "local _sl=" .. E .. "[" .. L("select") .. "]if " .. TY ..
      "(_sl)~=\"function\"then return true end return _sl(\"#\",1,2,3)==3 and _sl(2,\"a\",\"b\",\"c\")==\"b\" end",
    "local _t=" .. E .. "[" .. L("table") .. "]if " .. TY ..
      "(_t)~=\"table\" or " .. TY .. "(_t.concat)~=\"function\"then return true end return " ..
      "_t.concat({1,2,3})==\"123\" and _t.concat({},\",\")==\"\" end",
    "local _ts=" .. E .. "[" .. L("tostring") .. "]local _tn=" .. E .. "[" .. L("tonumber") ..
      "]if " .. TY .. "(_ts)~=\"function\" or " .. TY .. "(_tn)~=\"function\"then return true end return " ..
      "_ts(nil)==\"nil\" and _ts(true)==\"true\" and _tn(\"0x10\")==16 and _tn(\"  42  \")==42 end",
    "local _n=" .. E .. "[" .. L("next") .. "]local _ip=" .. E .. "[" .. L("ipairs") ..
      "]if " .. TY .. "(_n)~=\"function\" or " .. TY .. "(_ip)~=\"function\"then return true end " ..
      "local _s=0 for _,_v in _ip({1,2,3})do _s=_s+_v end return _n({})==nil and _s==6 end",
    "local _s=" .. E .. "[" .. L("string") .. "]if " .. TY ..
      "(_s)~=\"table\" or " .. TY .. "(_s.gsub)~=\"function\"then return true end return " ..
      "_s.gsub(\"aaa\",\"a\",\"b\")==\"bbb\" end",
    "local _r=" .. E .. "[" .. L("rawequal") .. "]if " .. TY ..
      "(_r)~=\"function\"then return true end local _g=" .. E .. "[" .. L("game") ..
      "]if _g==nil then return true end return _r(_g,_g)==true end",
    "local _u=" .. E .. "[" .. L("utf8") .. "]if _u==nil then return true end if " .. TY ..
      "(_u)~=\"table\" or " .. TY .. "(_u.char)~=\"function\"then return true end return " ..
      "_u.char(72,105)==\"Hi\" end",
    "local _t=" .. E .. "[" .. L("task") .. "]if _t==nil then return true end if " .. TY ..
      "(_t)~=\"table\"then return false end return " .. TY .. "(_t.spawn)==\"function\" and " ..
      TY .. "(_t.defer)==\"function\" end",
    "local _b=" .. E .. "[" .. L("BrickColor") .. "]if _b==nil then return true end if " .. TY ..
      "(_b.new)~=\"function\"then return true end local _o,_v=" .. PC .. "(function()return _b.new(" ..
      L("Really red") .. ")end)if not _o or _ty(_v)~=\"BrickColor\"then return false end return " ..
      "_v.Name==\"Really red\" end",
    "local _n=" .. E .. "[" .. L("Instance") .. "][\"new\"]if " .. TY ..
      "(_n)~=\"function\"then return true end local _f=_n(" .. L("Folder") ..
      ")if _ty(_f)~=\"Instance\" or " .. TY .. "(_f.Clone)~=\"function\"then " ..
      PC .. "(function()_f.Destroy(_f)end)return true end local _o,_c=" .. PC ..
      "(function()return _f:Clone()end) local _ok=_o and _ty(_c)==\"Instance\" and _c.ClassName==\"Folder\" and " ..
      "_c~=_f " .. PC .. "(function()_f:Destroy()end)return _ok end",
    "local _p=" .. E .. "[" .. L("PhysicalProperties") .. "]if _p==nil then return true end if " .. TY ..
      "(_p.new)~=\"function\"then return true end local _o,_v=" .. PC .. "(function()return _p.new(0.7,0.3,0.5)end) " ..
      "return _o and _ty(_v)==\"PhysicalProperties\" end",
    "local _c=" .. E .. "[" .. L("ColorSequence") .. "]local _c3=" .. E .. "[" .. L("Color3") ..
      "]if _c==nil then return true end if " .. TY .. "(_c.new)~=\"function\" or " .. TY ..
      "(_c3)~=\"table\" or " .. TY .. "(_c3.new)~=\"function\"then return true end local _o,_v=" ..
      PC .. "(function()return _c.new(_c3.new(1,0,0))end)return _o and _ty(_v)==\"ColorSequence\" end",
    "local _e=" .. E .. "[" .. L("Enum") .. "]local _f=_e and _e.Font if _f==nil then return true end if " .. TY ..
      "(_f.GetEnumItems)~=\"function\"then return true end local _o,_v=" .. PC ..
      "(function()return _f:GetEnumItems()end)return _o and " .. TY .. "(_v)==\"table\" and #_v>0 end",
  }
  for i = 1, #extra do
    a("_tq(function()" .. extra[i] .. ")")
  end

  -- Probe-count latch: the count is fixed at build time, so a stripped or
  -- short-circuited probe call is itself a tamper answer (weight three, the
  -- full threshold). A clean client always registers every probe.
  local probeCount = 0
  for _ in table.concat(out, " "):gmatch("_tq%(function") do
    probeCount = probeCount + 1
  end
  a("if _tn~=" .. probeCount .. " then _tt=_tt+3 end")
  Tamper.probeCount = probeCount

  a("if _tt>=" .. Tamper.THRESHOLD .. " then " .. kill .. " end")

  a("end")
  a("end")
  a("end")
  return table.concat(out, " ")
end

return Tamper
