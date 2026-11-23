-- tamper.lua -- game-side probe block for the compact engine.
--
-- The strong engine ships its own probe set (v2/src/tamper.lua). Snippets take
-- the compact engine and used to ship nothing, so a throwaway build had no
-- game-side anti-tamper at all. This module emits the same contract in a small
-- form: inert unless the host is a live DataModel, probes only count answers
-- that are impossible on a real client, and a missing API is always skipped.
--
--   Tamper.emit() -> source inside the generated VM.
local Tamper = {}

Tamper.THRESHOLD = 3

local function probeBodies()
  return {
    -- DataModel and workspace shape.
    'local g=_cg local w=_cw return _ty(g)=="Instance" and _ty(w)=="Instance" and g.ClassName=="DataModel" and w.ClassName=="Workspace"',
    'local g=_cg return _ty(g)=="Instance" and g.Parent==nil',
    -- Value types.
    'local c=CFrame if _ct(c)~="table" then return true end local n=c.new if _ct(n)~="function" then return true end local f=n(5,2,1) if _ty(f)~="CFrame" then return false end local p=f.Position return _ty(p)=="Vector3" and p.X==5 and p.Y==2 and p.Z==1',
    'local v=Vector3 if _ct(v)~="table" then return true end local n=v.new if _ct(n)~="function" then return true end local u=n(1,0,0).Unit return _ty(u)=="Vector3" and u.X==1 and u.Y==0 and u.Z==0',
    'local u=UDim2 if _ct(u)~="table" then return true end local n=u.new if _ct(n)~="function" then return true end local d=n(0.25,0,0.5,0) return _ty(d)=="UDim2" and d.X.Scale==0.25 and d.Y.Scale==0.5 and d.X.Offset==0',
    'local v=Vector2 if _ct(v)~="table" then return true end local n=v.new if _ct(n)~="function" then return true end local m=n(3,4).Magnitude return _ct(m)=="number" and m>4.999 and m<5.001',
    -- Instance semantics.
    'local I=Instance if _ct(I)~="table" then return true end local n=I.new if _ct(n)~="function" then return true end local p=n("Part") if _ty(p)~="Instance" then return false end local ok=p.ClassName=="Part" and p:IsA("BasePart")==true and p:IsA("Model")==false if _ct(p.Destroy)=="function" then p:Destroy() end return ok',
    -- Live identifiers.
    'local g=_cg return _ct(g.PlaceId)=="number" and _ct(g.GameId)=="number" and _ct(g.JobId)=="string"',
    'local g=_cg if _ct(g.GetService)~="function" then return true end local o,h=_cp(g.GetService,g,"HttpService") if not o or h==nil or _ct(h.GenerateGUID)~="function" then return true end local a=h:GenerateGUID(false) local b=h:GenerateGUID(false) if _ty(a)~="string" or #a~=36 then return false end return a~=b and string.sub(a,9,9)=="-" and string.sub(a,14,14)=="-" and string.sub(a,19,19)=="-" and string.sub(a,24,24)=="-"',
    -- Service identity and client flags.
    'local g=_cg if _ct(g.GetService)~="function" then return true end local o,r=_cp(g.GetService,g,"Workspace") if not o then return true end return r==_cw',
    'local w=_cw if _ty(w)~="Instance" then return true end return _ct(w.Gravity)=="number"',
    'local g=_cg if _ct(g.GetService)~="function" then return true end local o,r=_cp(g.GetService,g,"RunService") if not o or _ty(r)~="Instance" then return true end local o2,c=_cp(function()return r:IsClient()end) local o3,s=_cp(function()return r:IsStudio()end) if not o2 or not o3 then return true end return _ct(c)=="boolean" and _ct(s)=="boolean"',
    'local g=_cg if _ct(g.GetService)~="function" then return true end local o,u=_cp(g.GetService,g,"UserInputService") if not o or _ty(u)~="Instance" then return true end return _ct(u.TouchEnabled)=="boolean" and _ct(u.KeyboardEnabled)=="boolean"',
    'local g=_cg if _ct(g.GetService)~="function" then return true end local o,p=_cp(g.GetService,g,"Players") if not o or _ty(p)~="Instance" then return true end local l=p.LocalPlayer if l==nil then return true end return _ty(l)=="Instance" and _ct(l.UserId)=="number"',
    'local g=_cg if _ct(g.GetService)~="function" then return true end local o,r=_cp(g.GetService,g,"ReplicatedStorage") if not o or _ty(r)~="Instance" then return true end return r.Parent==g',
  }
end

function Tamper.emit()
  local out = {}
  local function a(s) out[#out + 1] = s end

  a("do")
  a("local _cp=pcall local _ct=type local _ty=typeof local _cg=game local _cw=workspace")
  a('if _ct(_cp)=="function" and _ct(_ty)=="function" and _ty(_cg)=="Instance" then')
  a("local _cn=0")
  a("local function _cf(f)local o,v=_cp(f)if o and v~=true then _cn=_cn+1 end end")
  local probes = probeBodies()
  for i = 1, #probes do
    a("_cf(function()" .. probes[i] .. " end)")
  end
  a("if _cn>=" .. Tamper.THRESHOLD .. " then integrityFailure() end")
  a("end")
  a("end")
  return table.concat(out, "\n")
end

return Tamper
