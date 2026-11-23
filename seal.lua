-- SEAL4 / V1.0: shuffled mixed API/payload pool around existing SEAL2 + VM9.
-- The two layers are intentionally separate: SEAL3 makes simple signature
-- extraction harder; SEAL2 remains the backward-compatible compression and
-- redundant block-integrity layer. Neither is a cryptographic trust boundary.
local Legacy = require('src.seal2')
local Entropy = require('src.entropy')
local Release = require('src.release')
local ClaxAlert = require('src.clax_alert')
local Seal = { MAX_BYTES = Legacy.MAX_BYTES, BLOCK = Legacy.BLOCK }
local floor, char, byte = math.floor, string.char, string.byte
local MOD = 4294967296
local function rngFor(seed)
  local n = floor(tonumber(seed) or 0) % MOD
  return function(lim)
    n = (n * 1664525 + 1013904223) % MOD
    return floor(n / 65536) % lim
  end
end
local function adler(s)
  local a,b=1,0
  for i=1,#s do
    a=(a+byte(s,i))%65521
    b=(b+a)%65521
  end
  return b*65536+a
end
local function b64(s, alphabet)
  local out, i = {},1
  while i+2<=#s do
    local v=byte(s,i)*65536+byte(s,i+1)*256+byte(s,i+2)
    out[#out+1]=alphabet[floor(v/262144)%64+1]..alphabet[floor(v/4096)%64+1]..
      alphabet[floor(v/64)%64+1]..alphabet[v%64+1]
    i=i+3
  end
  if i==#s then
    local v=byte(s,i)
    out[#out+1]=alphabet[floor(v/4)+1]..alphabet[v%4*16+1]
  elseif i+1==#s then
    local v=byte(s,i)*256+byte(s,i+1)
    out[#out+1]=alphabet[floor(v/1024)+1]..alphabet[floor(v/16)%64+1]..alphabet[v%16*4+1]
  end
  return table.concat(out)
end
-- Three reversible transport transforms: XOR stream, position-dependent
-- index shift with feedback, and reversal. Keys travel inside the artifact:
-- this is obfuscation, not authenticated encryption.
local function xorByte(a,b)
  local v,p=0,1
  for _=1,8 do
    if a%2~=b%2 then v=v+p end
    a=floor(a/2) b=floor(b/2) p=p*2
  end
  return v
end
local function enc(s, seed)
  local state,prev=seed,0
  local result={}
  for i=1,#s do
    state=(state*1664525+1013904223+i)%MOD
    local x=xorByte(byte(s,i),floor(state/65536)%256)
    local v=(x+i%251+prev)%256
    result[i]=char(v)
    prev=v
  end
  return string.reverse(table.concat(result))
end

local function ident(rng)
  local a={'a','b','c','d','e','f','g','h','j','k','m','n','p','q','r','s','t','u','v','w','x','y','z'}
  local o={'_'}
  for i=1,10 do o[#o+1]=a[rng(#a)+1] end
  return table.concat(o)
end
-- [CLAIR-GAP] Arithmetic expression encoding for API/member names.
local function byteExpr(n, rng)
  local k=rng(70)+2
  local form=rng(5)
  if form==0 then return '('..n..'+'..k..'-'..k..')' end
  if form==1 then return '('..(n+k)..'-'..k..')' end
  if form==2 then return '(('..n..'*'..k..')/'..k..')' end
  if form==3 then return '('..(n*k+k)..'-'..k..')/'..k end
  return '('..(n-k)..'+'..k..')'
end
local function exprName(name, rng)
  local pieces={}
  for i=1,#name do pieces[#pieces+1]=byteExpr(byte(name,i),rng) end
  return 'gp('..table.concat(pieces,',')..')'
end
local function permutation(rng,n)
  local p={} for i=1,n do p[i]=i end
  for i=n,2,-1 do local j=rng(i)+1 p[i],p[j]=p[j],p[i] end
  return p
end
-- [CLAIR-GAP] One shuffled pool for API references, encoded API names and
-- individual payload rows; order is a separate list of randomized indices.
-- Runtime keys and payload are recoverable by a host that executes this code.
local STUB=[=[
]=] .. ClaxAlert.emit('_bad') .. [=[
-- [CLAIR-GAP] kb preserves false-valued properties and metatable fallback.
local function kb(c,d)
 if type(c)=='table' and type(rawget)=='function' then
  local value=rawget(c,d)
  if value~=nil then return value end
 end
 return c[d]
end
local _S,_T,_M=__pool[@@S@@],__pool[@@T@@],__pool[@@M@@]
local _F=kb(_M,__pool[@@FLOOR@@])
-- [V1.0.2] Resolve member functions once per artifact, not once per byte.
local _BYTE=kb(_S,__pool[@@BYTE@@])
local _CHAR=kb(_S,__pool[@@CHAR@@])
local _REVERSE=kb(_S,__pool[@@REVERSE@@])
local _CONCAT=kb(_T,__pool[@@CONCAT@@])
-- Transport integrity must be tied to decoded data, not to how a host formats
-- errors or exposes debugging facilities. Roblox/Luau, profilers, and ordinary
-- instrumentation can change pcall/xpcall, gethook, getinfo and clock behavior.
-- Those observations are not evidence that the embedded payload changed.
if type(_S)~='table' or type(_BYTE)~='function' or
 type(_CHAR)~='function' or type(_REVERSE)~='function' or
 type(_T)~='table' or type(_CONCAT)~='function' or
 type(_F)~='function' then
 error('runtime primitives unavailable',0)
end
-- Do not install/remove debug hooks here: a host debugger or profiler may
-- own a hook, and forcibly clearing it can break the host. Inner VM's opcode,
-- frame and packed-payload integrity checks stay independent and enabled.
if type(__alpha)~='table' or #__alpha~=64 or type(__pool)~='table' or type(__order)~='table' then _bad() end
-- [DEX-HARDEN] Authenticate fragment ordering metadata against build-time checksum.
-- This catches accidental/replay modifications, not adversarial edits to the entire loader.
local _orderProof,_seenOrder=0,{}
if #__order~=__pieces then _bad() end
for i=1,#__order do
 local key=__order[i]
 if type(key)~='number' or key~=_F(key) or _seenOrder[key] or type(__pool[key])~='table' then _bad() end
 _seenOrder[key]=true
 _orderProof=(_orderProof*65599+key+i*17)%1000000007
end
if _orderProof~=__orderProof then _bad() end
_seenOrder=nil
local _map={}
for i=1,64 do
 local c=__alpha[i]-__shift
 if type(c)~='number' or c<33 or c>126 or c~=_F(c) or _map[c]~=nil then _bad() end
 _map[c]=i-1
end
@@DECODE_IMPLEMENTATION@@
local _load=loadstring or load
if type(_load)~='function' then error('dynamic loader unavailable; choose Direct VM for restricted hosts',0) end
-- Decoder is compiled from pieces at runtime; the actual VM is loaded only
-- after every fragment has passed its length and checksum checks.
-- The complete per-fragment inverse is assembled and compiled at runtime.
-- The nibble XOR table avoids version-specific bitwise operators (Lua 5.1).
-- Populate the nibble-XOR lookup using a runtime-clock-selected permutation.
-- The same slot must be passed into its lookups while the fragments decode.
-- This is analysis friction, not a secret key; it cannot prevent host tracing.
local _pieces={
 'return (function(slot) local xt={} for a=0,15 do for b=0,15 do',
 ' local x,y,v,p=a,b,0,1 for i=1,4 do if x%2~=y%2 then v=v+p end',
 ' x=math.floor(x/2) y=math.floor(y/2) p=p*2 end',
 ' local aa=(a+slot)%16 local bb=(b+slot*3)%16',
 ' if not xt[aa] then xt[aa]={} end xt[aa][bb]=v end end',
 ' return function(cipher,seed,by,ch,cat,rev,fl) local out,prev,state={},0,seed @@FAST_INIT@@',
 ' cipher=rev(cipher) for i=1,#cipher do state=(state*1664525+1013904223+i)%4294967296',
 ' local q=by(cipher,i) local z=(q-i%251-prev)%256 local k=fl(state/65536)%256',
 ' local value=xt[(fl(z/16)+slot)%16][(fl(k/16)+slot*3)%16]*16',
 '  +xt[(z%16+slot)%16][(k%16+slot*3)%16]',
 ' out[i]=ch(value) prev=q @@FAST_UPDATE@@ end return cat(out)@@FAST_RETURN@@ end end)'
}
local _dchunk,_compileErr=_load(_T.concat(_pieces))
if not _dchunk then _bad() end
local _makeRecover=_dchunk()
if type(_makeRecover)~='function' then _bad() end
local _recover=_makeRecover(_clockSlot)
if type(_recover)~='function' then _bad() end
local _join={}
local _a,_b=1,0
@@FRAGMENT_MACHINE@@
-- This check depends on the *actual decoded bytes* and runtime clock slot;
-- unlike n(n+1)%%2 it fails when any fragment's integrity is broken.
local _got=(_b*65536+_a+_clockSlot*65537+#_join*257)%4294967296
local _want=((__whole-__wholeMask)%4294967296+_clockSlot*65537+__pieces*257)%4294967296
if #_join~=__pieces or _got~=_want then _bad() end
local _finish=_clock and _clock() or nil
local _wallFinish=_wall and _wall() or nil
if _wallFinish and (_wallFinish~=_wallFinish or (_wallStart and _wallFinish+2<_wallStart)) then _bad() end
if _finish and (_finish~=_finish or (_start and _finish+0.001<_start)) then _bad() end
local _source=_T.concat(_join)
-- [CLAIR-GAP] Release short-lived decoder and pool references after decoding;
-- GC timing and copies in host memory cannot be guaranteed.
__pool=nil __order=nil __alpha=nil _map=nil _pieces=nil
_dchunk=nil _makeRecover=nil _recover=nil _join=nil
local _fun,_err
if type(loadstring)=='function' then _fun,_err=loadstring(_source) else _fun,_err=load(_source,'=GsX','t',_ENV) end
if type(_fun)~='function' then error(_err or 'runtime load failed',0) end
if type(setfenv)=='function' then
 local _env=type(getfenv)=='function' and getfenv(1) or _G
 local ok=pcall(setfenv,_fun,_env)
 if not ok then error('runtime environment attach failed',0) end
end
_source=nil
_clockSlot=nil _clockSeed=nil _clockFn=nil
__shift=nil __max=nil __pieces=nil __whole=nil __wholeMask=nil
-- [CLAIR-GAP] Coroutine wrapper is opt-in: it changes coroutine.running(),
-- yielding and diagnostic behavior; it does not prevent host-side dumps.
if @@CORO@@ and type(coroutine)=='table' and type(coroutine.wrap)=='function' then
 local runner=coroutine.wrap(_fun)
 _fun=nil
 return runner(...)
end
return _fun(...)
]=]

local DECODE_REFERENCE=[=[
local function _decode(s,n)
 if type(s)~='string' or #s%4==1 or #s>_F((n+2)/3)*4 or n<0 then _bad() end
 local o,v,bits={},0,0
 for i=1,#s do
  local x=_map[_S.byte(s,i)] if x==nil then _bad() end
  v=v*64+x bits=bits+6
  if bits>=8 then
   bits=bits-8
   o[#o+1]=_S.char(_F(v/2^bits)%256)
   v=v%2^bits
  end
 end
 if v~=0 or #o~=n then _bad() end
 return _T.concat(o)
end
]=]
local DECODE_FAST=[=[
local function _decode(s,n)
 if type(s)~='string' or n<0 then _bad() end
 -- [FAST-LOAD] Four base64 characters decode to three bytes in one char()
 -- call; keep strict alphabet, tail-bit and decoded-length validation.
 local count=#s
 if count%4==1 or count>_F((n+2)/3)*4 then _bad() end
 local out,at={},0
 local groups=_F(count/4)*4
 for i=1,groups,4 do
  local a,b,c,d=_map[_BYTE(s,i)],_map[_BYTE(s,i+1)],_map[_BYTE(s,i+2)],_map[_BYTE(s,i+3)]
  if a==nil or b==nil or c==nil or d==nil then _bad() end
  local v=a*262144+b*4096+c*64+d
  at=at+1
  out[at]=_CHAR(_F(v/65536)%256,_F(v/256)%256,v%256)
 end
 local remain=count-groups
 if remain==2 then
  local a,b=_map[_BYTE(s,groups+1)],_map[_BYTE(s,groups+2)]
  if a==nil or b==nil then _bad() end
  local v=a*64+b
  if v%16~=0 then _bad() end
  at=at+1 out[at]=_CHAR(_F(v/16))
 elseif remain==3 then
  local a,b,c=_map[_BYTE(s,groups+1)],_map[_BYTE(s,groups+2)],_map[_BYTE(s,groups+3)]
  if a==nil or b==nil or c==nil then _bad() end
  local v=a*4096+b*64+c
  if v%4~=0 then _bad() end
  at=at+1 out[at]=_CHAR(_F(v/1024),_F(v/4)%256)
 elseif remain~=0 then _bad() end
 local result=_CONCAT(out)
 if #result~=n then _bad() end
 return result
end
]=]

-- [STATE-MACHINE] Transform the sealed fragment pipeline into a seeded,
-- shuffled five-stage dispatcher. Work is performed by real states (fetch,
-- unpack, decrypt, authenticate, append), not decoy branches. This is invoked
-- once per payload fragment, never once per source/VM instruction. Keep every
-- checksum tied to actual decoded bytes and fail closed on illegal states.
local function fragmentMachine(rng,fastLoad)
  local keys={}
  for i=1,6 do keys[i]=117+i*47+rng(37) end
  local order={1,2,3,4,5}
  for i=#order,2,-1 do
    local j=rng(i)+1
    order[i],order[j]=order[j],order[i]
  end
  local stage={
    'if _idx>#__order then _phase='..keys[6]..' else ' ..
      '_row=__pool[__order[_idx]] ' ..
      'if type(_row)~= "table" or type(_row[1])~= "string" then _bad() end ' ..
      '_seed=(_row[2]-_row[3])%4294967296 _n=_row[4]-_row[5] ' ..
      'if _n<1 or _n>__max or _n~=_F(_n) then _bad() end ' ..
      '_phase='..keys[2]..' end',
    '_cipher=_decode(_row[1],_n) _phase='..keys[3],
    (fastLoad and '_plain,_psa,_psb=' or '_plain=')..
      '_recover(_cipher,_seed,_BYTE,_CHAR,_CONCAT,_REVERSE,_F) ' ..
      'if #_plain~=_n then _bad() end _phase='..keys[4],
    (fastLoad and (
      'if (_psb*65536+_psa)~=(_row[6]-_row[7])%4294967296 then _bad() end ' ..
      '-- [FAST-LOAD] Adler-32 block composition avoids rescanning plaintext.\n' ..
      '_b=(_b+_n*(_a-1)+_psb)%65521 _a=(_a+_psa-1)%65521 ' ..
      '_phase='..keys[5]) or (
      'local sa,sb=1,0 for j=1,_n do ' ..
      'local value=_BYTE(_plain,j) ' ..
      'sa=(sa+value)%65521 sb=(sb+sa)%65521 ' ..
      '_a=(_a+value)%65521 _b=(_b+_a)%65521 end ' ..
      'if (sb*65536+sa)~=(_row[6]-_row[7])%4294967296 then _bad() end ' ..
      '_phase='..keys[5])),
    '_join[#_join+1]=_plain _row=nil _cipher=nil _plain=nil ' ..
      '_idx=_idx+1 _phase='..keys[1],
  }
  local out={
    'local _idx,_phase,_budget=1,'..keys[1]..',#__order*5+1',
    'local _row,_seed,_n,_cipher,_plain,_psa,_psb',
    'while _phase~='..keys[6]..' do',
    'if _budget<=0 then _bad() end _budget=_budget-1',
  }
  for i,at in ipairs(order) do
    out[#out+1]=(i==1 and 'if ' or 'elseif ')..'_phase=='..keys[at]..' then '..stage[at]
  end
  out[#out+1]='else _bad() end end'
  return table.concat(out,'\n')
end

function Seal.wrap(text,seed,opts)
  opts=opts or {}
  if type(text)~='string' or text=='' then return text end
  if #text > (opts.maxBytes or Seal.MAX_BYTES) then return nil,'seal: input too large' end
  local seedval=seed or Entropy.seed()
  local innerOpts={}
  for k,v in pairs(opts) do innerOpts[k]=v end
  innerOpts.omitBanner=true
  -- Hidden, per-build watermark: an ordinary comment *inside* both seals.
  -- Recoverable for provenance, not a digital signature or robust DRM.
  local watermark=opts.watermark
  if watermark~=nil and (type(watermark)~='string' or #watermark>128 or
      watermark:find('[^%w%._%-]')) then
    return nil,'seal3: watermark must contain 0..128 ASCII letters, digits, dot, _ or -'
  end
  if watermark==nil then
    watermark=string.format('b%08x-%08x',floor(seedval)%MOD,adler(text))
  end
  local marked='--[[gsx-watermark:'..watermark..']]\n'..text
  local inner,err=Legacy.wrap(marked,seedval,innerOpts)
  if not inner then return nil,err end
  local rng=rngFor((floor(seedval)*1103515245+12345)%MOD)
  local cs={}
  for c=33,126 do
    if c~=34 and c~=92 and c~=93 then cs[#cs+1]=c end
  end
  for i=#cs,2,-1 do local j=rng(i)+1 cs[i],cs[j]=cs[j],cs[i] end
  local symbols={}
  for i=1,64 do symbols[i]=char(cs[i]) end
  local shift=rng(21)+3
  local alpha={}
  for i=1,64 do alpha[i]=tostring(cs[i]+shift) end
  local segments={}
  local pos=1
  local step=opts.fragmentSize or 8192
  if type(step)~='number' or step~=floor(step) or step<128 or step>16384 then
    return nil,'seal3: fragmentSize must be 128..16384'
  end
  while pos<=#inner do
    local take=step - rng(math.max(1,floor(step/3)))
    if take<128 then take=128 end
    local src=inner:sub(pos,pos+take-1)
    pos=pos+#src
    local iv=rng(65536)*65536+rng(65536)
    local nonce=rng(65536)*65536+rng(65536)
    local salt=rng(65536)*65536+rng(65536)
    local lenmask=101+rng(900)
    local checkmask=rng(65536)*65536+rng(65536)
    segments[#segments+1]={
      key=ident(rng), data=b64(enc(src,iv),symbols),
      v=(iv+nonce)%MOD, m=nonce,
      n=#src+lenmask, nm=lenmask,
      sum=(adler(src)+checkmask)%MOD, sm=checkmask,
    }
  end
  -- [CLAIR-GAP] One table holds all encoded fragments, API objects and
  -- encoded API member names. Each item gets a different shuffled index.
  -- Avoid creating many lexical locals (PUC Lua limit: 200 active locals).
  local apiNames={'byte','char','reverse','concat','floor','pcall','type','rawget'}
  local labels={'S','T','M','ORDER','ALPHA'}
  for i=1,#apiNames do labels[#labels+1]=apiNames[i]:upper() end
  local indexPerm=permutation(rng,#segments+#labels)
  -- Sparse numeric slots prevent index position from revealing data category.
  local slotBase=70+rng(310)
  local slotStride=9+rng(25)
  for i=1,#indexPerm do
    indexPerm[i]=slotBase+indexPerm[i]*slotStride
  end
  local slots={}
  -- [V1.0.2] Fragment order and alphabet share the shuffled pool with APIs.
  local order={}
  for i=1,#segments do order[i]=tostring(indexPerm[i]) end
  local stream={}
  for i=1,#segments do
    local x=segments[i]
    stream[#stream+1]={slot=indexPerm[i],code='{'..string.format('%q',x.data)..','..
      x.v..','..x.m..','..x.n..','..x.nm..','..x.sum..','..x.sm..'}'}
  end
  for i=1,#labels do
    local name=labels[i]
    slots[name]=indexPerm[#segments+i]
    local code
    if name=='S' then code='string'
    elseif name=='T' then code='table'
    elseif name=='M' then code='math'
    elseif name=='ORDER' then code='{'..table.concat(order,',')..'}'
    elseif name=='ALPHA' then code='{'..table.concat(alpha,',')..'}'
    else code=exprName(name:lower(),rng) end
    stream[#stream+1]={slot=slots[name],code=code}
  end
  for i=#stream,2,-1 do
    local j=rng(i)+1
    stream[i],stream[j]=stream[j],stream[i]
  end
  local shards={'local __pool={}\n','local gp=string.char\n'}
  for i=1,#stream do
    local x=stream[i]
    shards[#shards+1]='__pool['..x.slot..']='..x.code..'\n'
  end
  shards[#shards+1]='local __order=__pool['..slots.ORDER..']\n'
  local orderProof=0
  for i=1,#order do
    local key=indexPerm[i]
    orderProof=(orderProof*65599+key+i*17)%1000000007
  end
  local wholeMask=rng(65536)*65536+rng(65536)
  local whole=(adler(inner)+wholeMask)%MOD
  -- Build the runtime clock permutation for the real fragment decoder.
  -- No transparent n(n+1)%%2 dead branch, and no silently accepted clock=0.
  local dead='local _clockFn=type(os)=="table" and type(os.clock)=="function" and os.clock\n'..
    'if not _clockFn then error("runtime clock unavailable",0) end\n'..
    'local _clockSeed=_clockFn()\n'..
    'if type(_clockSeed)~="number" or _clockSeed~=_clockSeed or _clockSeed==math.huge or _clockSeed==-math.huge then error("runtime clock invalid",0) end\n'..
    'local _clockSlot=math.floor(_clockSeed*1000)%7\n'
  local header='return (function(...)\n'..dead..table.concat(shards)..
    'local __alpha=__pool['..slots.ALPHA..']\n'..
    'local __shift='..shift..'\n'..
    'local __max='..step..' local __pieces='..#segments..'\n'..
    'local __whole='..whole..' local __wholeMask='..wholeMask..'\n'..
    'local __orderProof='..orderProof..'\n'
  local fastLoad=opts.fastLoad~=false
  local body=STUB:gsub('__token__',ident(rng))
  -- [FAST-LOAD] Decode and hash each byte in one pass; retain the reference
  -- implementation when explicitly disabled for compatibility comparisons.
  body=body:gsub('@@DECODE_IMPLEMENTATION@@',function()
    return fastLoad and DECODE_FAST or DECODE_REFERENCE
  end)
  body=body:gsub('@@FAST_INIT@@',fastLoad and 'local sa,sb=1,0' or '')
  body=body:gsub('@@FAST_UPDATE@@',fastLoad and
    'sa=(sa+value)%%65521 sb=(sb+sa)%%65521' or '')
  body=body:gsub('@@FAST_RETURN@@',fastLoad and ',sa,sb' or '')
  -- Real multi-stage control-flow flattening of the SEAL4 fragment loader.
  body=body:gsub('@@FRAGMENT_MACHINE@@',function() return fragmentMachine(rng,fastLoad) end)
  local placeholder={S='S',T='T',M='M',FLOOR='FLOOR',BYTE='BYTE',CHAR='CHAR',
    REVERSE='REVERSE',CONCAT='CONCAT'}
  for tag,label in pairs(placeholder) do
    body=body:gsub('@@'..tag..'@@',tostring(slots[label]))
  end
  body=body:gsub('@@CORO@@',opts.coroutineWrapper==true and 'true' or 'false')
  -- [V1.0.2] Avoid repeated rawget and table indexing in decode loops.
  body=body:gsub('_S%.byte', '_BYTE')
  body=body:gsub('_S%.char', '_CHAR')
  body=body:gsub('_S%.reverse', '_REVERSE')
  body=body:gsub('_T%.concat', '_CONCAT')
  -- Diversify transport identifiers without touching ordinary VM source.
  local tags={'__alpha','__shift','__pool','__order','__orderProof','__max','__pieces','__wholeMask','__whole'}
  for i=1,#tags do
    local token=tags[i] local repl=ident(rng)
    header=header:gsub(token..'([^%w_])',repl..'%1')
    body=body:gsub(token..'([^%w_])',repl..'%1')
  end
  local result=header..body..'\nend)(...)\n'
  local compact,compactErr=require('src.minify').compact(result)
  if not compact then return nil,compactErr end
  return Release.brand(compact)
end

function Seal.isWrapped(text)
  return type(text)=='string' and ((text:find('return (function',1,true)~=nil or text:find('return(function',1,true)~=nil) and
    text:find('runtime verification failed',1,true)~=nil or Legacy.isWrapped(text))
end
Seal.legacy=Legacy
return Seal
