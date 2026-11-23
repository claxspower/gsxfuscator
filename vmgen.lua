-- vmgen.lua -- layer 8: randomized opcode space + O(1) handler-table runtime.
--
-- Pipeline position:
--   compiler -> vmgen -> bytecode (M9)
--
-- The compiler emits instructions whose `op` is a name. This module can:
--
--   randomize(compiled, opts) -> plan
--     Uses four keys per opcode with key-specific layouts and integer masks.
--
--   emit(plan, opts) -> source, stats
--     Emits a self-contained Lua 5.1-subset chunk. Dispatch is exactly one
--     table lookup per instruction:
--
--       local npc = H[I[1]](I, R, K, U, S, pc)
--
--     There is no comparison chain over opcodes and no `elseif` anywhere in
--     the generated text. Every handler has the same signature; the decoy
--     handlers are never referenced by emitted code but are indistinguishable
--     in the table. Handler order, key assignment, runtime identifier names
--     and decoy bodies are derived from the build seed.
--
--   generate(compiled, opts) -> source, stats
--     randomize + emit.
--
-- The emitted chunk executes prototype 1 with the host varargs and returns
-- its results, which is the shape M12 wraps into the final file. M9 replaces
-- the plaintext prototype table with a packed, encrypted payload.
--
-- Runtime registers are 1-based and follow the compiler's ISA exactly. The
-- frame table `S` carries the moving top (`S.top`), the current prototype,
-- its packed arguments and the tail-return slot.
local Compiler = require("src.compiler")
local Antidebug = require("src.antidebug")
local Integrity = require("src.integrity")
local Strings = require("src.strings")
local Envlog = require("src.envlog")
local Tamper = require("src.tamper")
local ClaxAlert = require("src.clax_alert")
local Release = require("src.release")

local VMGen = {}

VMGen.DEFAULT_DECOYS = 448
VMGen.MAX_DECOYS = 1024
VMGen.DEFAULT_SEED = 0x0B1F9E
VMGen.KEY_RANGE = 65535
-- Twenty-four keys per opcode: every opcode owns twenty-four independent
-- dispatch slots with their own key, slot layout, operand mask and a body
-- salted with a key-unique token, so no two entries share a normalised text.
-- The compiler picks one key per emitted instruction, so a single dumped
-- instruction says nothing about how the next one is encoded, and an analyser
-- that learns one slot has learned 1/1920 of the table. Cost is a longer
-- handler table at load, not a slower dispatch: the runtime still does one
-- index and one call.
VMGen.ENCODINGS_PER_OPCODE = 24
VMGen.OPCODES = #Compiler.OPS

-- ------------------------------------------------------------------ handlers
-- Placeholders: $E env, $P prototypes, $X frame entry, $F closure factory,
-- $SU unpack, $PK pack, $MM math, $ERR error, $BW/$BN/$SHL/$SHR bit helpers.
local HANDLERS = {
  MOVE = "R[a]=R[b]",
  LOADK = "R[a]=K[d]",
  LOADNIL = "R[a]=nil",
  LOADBOOL = "R[a]=(b~=0)",
  LOADINT = "R[a]=d",
  LOADNILN = "for j=0,d-1 do R[a+j]=nil end",
  GETUPVAL = "R[a]=U[b][1]",
  SETUPVAL = "U[b][1]=R[a]",
  NEWCELL = "if b==0 then R[a]={} else R[a]={R[b]} end",
  GETCELL = "R[a]=R[b][1]",
  SETCELL = "R[a][1]=R[b]",
  GETGLOBAL = "R[a]=$E[K[d]]",
  SETGLOBAL = "$E[K[d]]=R[a]",
  NEWTABLE = "R[a]={}",
  GETTABLE = "R[a]=R[b][R[c]]",
  SETTABLE = "R[a][R[b]]=R[c]",
  GETFIELD = "R[a]=R[b][K[d]]",
  SETFIELD = "R[a][K[d]]=R[b]",
  SELF = "local t=R[b] R[a+1]=t R[a]=t[K[d]]",
  SETLIST = "local n=(d<0)and(S.top-c)or d if n<0 then n=0 end " ..
    "for j=1,n do R[a][b+j-1]=R[c+j-1] end if d<0 then S.top=c end",
  GETIDXI = "R[a]=R[b][d]",
  SETIDXI = "R[a][d]=R[b]",
  ADD = "R[a]=R[b]+R[c]",
  SUB = "R[a]=R[b]-R[c]",
  MUL = "R[a]=R[b]*R[c]",
  DIV = "R[a]=R[b]/R[c]",
  MOD = "R[a]=R[b]%R[c]",
  POW = "R[a]=R[b]^R[c]",
  IDIV = "R[a]=$MM.floor(R[b]/R[c])",
  UNM = "R[a]=-R[b]",
  CONCAT = "R[a]=R[b]..R[c]",
  BAND = "R[a]=$BW(R[b],R[c],1)",
  BOR = "R[a]=$BW(R[b],R[c],2)",
  BXOR = "R[a]=$BW(R[b],R[c],3)",
  BNOT = "R[a]=$BN(R[b])",
  SHL = "R[a]=$SHL(R[b],R[c])",
  SHR = "R[a]=$SHR(R[b],R[c])",
  LEN = "R[a]=#R[b]",
  NOT = "R[a]=not R[b]",
  BOOL = "local v=R[b] local z=(v~=nil and v~=false) " ..
    "if c~=0 then z=not z end R[a]=z",
  EQ = "R[a]=(R[b]==R[c])",
  NE = "R[a]=(R[b]~=R[c])",
  LT = "R[a]=(R[b]<R[c])",
  LE = "R[a]=(R[b]<=R[c])",
  GT = "R[a]=(R[b]>R[c])",
  GE = "R[a]=(R[b]>=R[c])",
  TEST = "if ((R[b]~=nil and R[b]~=false)==(a~=0)) then return pc+2 end " ..
    "return pc+1",
  TESTSET = "if ((R[b]~=nil and R[b]~=false)==(a~=0)) then R[c]=R[b] " ..
    "return pc+2 end return pc+1",
  TESTNIL = "if R[b]==nil then return pc+2 end return pc+1",
  JMP = "return pc+1+d",
  JMPF = "if not R[a] then return pc+1+d end return pc+1",
  JMPT = "if R[a] then return pc+1+d end return pc+1",
  FORPREP = "R[a]=R[a]-R[a+2] return pc+1+d",
  FORLOOP = "local st=R[a+2] if st==0 then $ERR($DM(39,102,111,114,39,32," ..
    "115,116,101,112,32,105,115,32,122,101,114,111)) end " ..
    "local v=R[a]+st R[a]=v R[a+3]=v local lm=R[a+1] " ..
    "if st>0 and v<=lm then return pc+1+d end " ..
    "if st<0 and v>=lm then return pc+1+d end return pc+1",
  TFORCALL = "local z=$PK(R[a](R[a+1],R[a+2])) " ..
    "for j=1,b do R[a+2+j]=z[j] end S.top=a+3+b",
  TFORLOOP = "if R[a+3]~=nil then R[a+2]=R[a+3] return pc+1+d end " ..
    "return pc+1",
  CLOSE = "return pc+1",
  NOP = "return pc+1",
  SETTOP = "S.top=a return pc+1",
  CALL = "local n if b<0 then n=S.top-(a+1) else n=b end " ..
    "if n<0 then n=0 end local z " ..
    "if n==0 then z=$PK(R[a]()) end " ..
    "if n==1 then z=$PK(R[a](R[a+1])) end " ..
    "if n==2 then z=$PK(R[a](R[a+1],R[a+2])) end " ..
    "if n>2 then local G={} for j=1,n do G[j]=R[a+j] end " ..
    "z=$PK(R[a]($SU(G,1,n))) end " ..
    "local q=(d>0)and d or a " ..
    "if c<0 then for j=1,z.n do R[q+j-1]=z[j] end S.top=q+z.n end " ..
    "if c>0 then for j=1,c do R[q+j-1]=z[j] end end",
  -- Return the callee register to the interpreter. Making the call inside
  -- this handler would keep both the handler and its caller's frame alive.
  TAILCALL = "if b>=0 then S.top=a+1+b end S.ret=a return nil",
  RETURN = "local n=b if b<0 then n=S.top-a end " ..
    "if n<=0 then S.ret={n=0} return false end " ..
    "if n==1 then S.ret={n=1,R[a]} return false end " ..
    "local t={n=n} for j=1,n do t[j]=R[a+j-1] end S.ret=t return false",
  CLOSURE = "local Q=$P[b] local V={} for j=1,#Q.u do local e=Q.u[j] " ..
    "if e[1]==1 then V[j]=R[e[2]] else V[j]=U[e[2]] end end R[a]=$F(b,V)",
  VARARG = "local n=(S.p.v and b) or 0 if b<0 then " ..
    "n=(S.p.v and (S.an-S.p.a)) or 0 if n<0 then n=0 end " ..
    "S.top=a+n end for j=1,n do R[a+j-1]=S.ar[S.p.a+j] end",
  ADDK = "R[a]=R[b]+K[d]",
  SUBK = "R[a]=R[b]-K[d]",
  MULK = "R[a]=R[b]*K[d]",
  DIVK = "R[a]=R[b]/K[d]",
  MODK = "R[a]=R[b]%K[d]",
  POWK = "R[a]=R[b]^K[d]",
  IDIVK = "R[a]=$MM.floor(R[b]/K[d])",
  ADDI = "R[a]=R[b]+d",
  SUBI = "R[a]=R[b]-d",
  MULI = "R[a]=R[b]*d",
  DIVI = "R[a]=R[b]/d",
  MODI = "R[a]=R[b]%d",
  EQK = "R[a]=(R[b]==K[d])",
  NEK = "R[a]=(R[b]~=K[d])",
  LTK = "R[a]=(R[b]<K[d])",
  LEK = "R[a]=(R[b]<=K[d])",
}

VMGen.HANDLERS = HANDLERS

-- Per-build polymorphic handler variants. Each list holds semantically identical
-- implementations (same operators and operand order, so metamethod dispatch is
-- unchanged); emit picks one at random so two builds of the same source shape
-- their hot handlers differently. Depth on top of the randomized opcode space.
local VARIANTS = {
  MOVE = { "R[a]=R[b]", "local u=R[b] R[a]=u",
    "local u=R[b],R[b] R[a]=u", "do local u=R[b] R[a]=u end",
    "if b~=a then R[a]=R[b] end", "local u=R R[a]=u[b]",
    "R[a]=(R[b])" },
  LOADK = { "R[a]=K[d]", "local u=K[d] R[a]=u",
    "local u=K[d],K[d] R[a]=u", "do local u=K[d] R[a]=u end",
    "local u=K R[a]=u[d]", "R[a]=(K[d])" },
  LOADNIL = { "R[a]=nil", "do R[a]=nil end",
    "local u=nil R[a]=u", "if a>0 then R[a]=nil end",
    "local u=R[a] u=nil R[a]=u" },
  LOADBOOL = { "R[a]=(b~=0)", "local u=b R[a]=(u~=0)",
    "do local u=b R[a]=(u~=0) end",
    "if b~=0 then R[a]=true else R[a]=false end",
    "local u=(b~=0) R[a]=u" },
  LOADINT = { "R[a]=d", "local u=d R[a]=u", "do local u=d R[a]=u end",
    "R[a]=(d)", "local u=I[5] R[a]=u" },
  LOADNILN = { "for j=0,d-1 do R[a+j]=nil end",
    "for j=1,d do R[a+j-1]=nil end",
    "local p=a for j=0,d-1 do R[p+j]=nil end",
    "local n=d if n>0 then for j=0,n-1 do R[a+j]=nil end end",
    "do local p=a for j=0,d-1 do R[p+j]=nil end end" },
  ADD = { "R[a]=R[b]+R[c]", "local u=R[b] local v=R[c] R[a]=u+v",
    "local u,v=R[b],R[c] R[a]=u+v",
    "local u=R[b] local v=R[c] local w=u+v R[a]=w",
    "do local u=R[b] local v=R[c] R[a]=u+v end" },
  SUB = { "R[a]=R[b]-R[c]", "local u=R[b] local v=R[c] R[a]=u-v",
    "local u,v=R[b],R[c] R[a]=u-v",
    "local u=R[b] local v=R[c] local w=u-v R[a]=w" },
  MUL = { "R[a]=R[b]*R[c]", "local u=R[b] local v=R[c] R[a]=u*v",
    "local u,v=R[b],R[c] R[a]=u*v",
    "local u=R[b] local v=R[c] local w=u*v R[a]=w" },
  DIV = { "R[a]=R[b]/R[c]", "local u=R[b] local v=R[c] R[a]=u/v",
    "local u,v=R[b],R[c] R[a]=u/v",
    "local u=R[b] local v=R[c] local w=u/v R[a]=w" },
  MOD = { "R[a]=R[b]%R[c]", "local u=R[b] local v=R[c] R[a]=u%v",
    "local u,v=R[b],R[c] R[a]=u%v",
    "local u=R[b] local v=R[c] local w=u%v R[a]=w" },
  POW = { "R[a]=R[b]^R[c]", "local u=R[b] local v=R[c] R[a]=u^v",
    "local u,v=R[b],R[c] R[a]=u^v",
    "local u=R[b] local v=R[c] local w=u^v R[a]=w" },
  IDIV = { "R[a]=$MM.floor(R[b]/R[c])", "local u=R[b] local v=R[c] R[a]=$MM.floor(u/v)",
    "local u=R[b] local v=R[c] local w=u/v R[a]=$MM.floor(w)" },
  UNM = { "R[a]=-R[b]", "local u=R[b] R[a]=-u", "do local u=R[b] R[a]=-u end" },
  CONCAT = { "R[a]=R[b]..R[c]", "local u=R[b] local v=R[c] R[a]=u..v",
    "local u=R[b] local v=R[c] local w=u..v R[a]=w" },
  BAND = { "R[a]=$BW(R[b],R[c],1)", "local u=R[b] local v=R[c] R[a]=$BW(u,v,1)",
    "local u=R[b] R[a]=$BW(u,R[c],1)" },
  BOR = { "R[a]=$BW(R[b],R[c],2)", "local u=R[b] local v=R[c] R[a]=$BW(u,v,2)",
    "local u=R[b] R[a]=$BW(u,R[c],2)" },
  BXOR = { "R[a]=$BW(R[b],R[c],3)", "local u=R[b] local v=R[c] R[a]=$BW(u,v,3)",
    "local u=R[b] R[a]=$BW(u,R[c],3)" },
  BNOT = { "R[a]=$BN(R[b])", "local u=R[b] R[a]=$BN(u)",
    "do local u=R[b] R[a]=$BN(u) end" },
  SHL = { "R[a]=$SHL(R[b],R[c])", "local u=R[b] local v=R[c] R[a]=$SHL(u,v)",
    "local u=R[b] R[a]=$SHL(u,R[c])" },
  SHR = { "R[a]=$SHR(R[b],R[c])", "local u=R[b] local v=R[c] R[a]=$SHR(u,v)",
    "local u=R[b] R[a]=$SHR(u,R[c])" },
  ADDK = { "R[a]=R[b]+K[d]", "local u=R[b] local v=K[d] R[a]=u+v",
    "local u=K[d] R[a]=R[b]+u",
    "local u=R[b] local v=(K[d]) R[a]=u+v" },
  SUBK = { "R[a]=R[b]-K[d]", "local u=R[b] local v=K[d] R[a]=u-v",
    "local u=K[d] R[a]=R[b]-u",
    "local u=R[b] local v=(K[d]) R[a]=u-v" },
  MULK = { "R[a]=R[b]*K[d]", "local u=R[b] local v=K[d] R[a]=u*v",
    "local u=K[d] R[a]=R[b]*u",
    "local u=R[b] local v=(K[d]) R[a]=u*v" },
  DIVK = { "R[a]=R[b]/K[d]", "local u=R[b] local v=K[d] R[a]=u/v",
    "local u=R[b] local v=(K[d]) R[a]=u/v" },
  MODK = { "R[a]=R[b]%K[d]", "local u=R[b] local v=K[d] R[a]=u%v",
    "local u=R[b] local v=(K[d]) R[a]=u%v" },
  POWK = { "R[a]=R[b]^K[d]", "local u=R[b] local v=K[d] R[a]=u^v",
    "local u=R[b] local v=(K[d]) R[a]=u^v" },
  IDIVK = { "R[a]=$MM.floor(R[b]/K[d])", "local u=R[b] local v=K[d] R[a]=$MM.floor(u/v)",
    "local u=R[b] local v=K[d] local w=u/v R[a]=$MM.floor(w)" },
  ADDI = { "R[a]=R[b]+d", "local u=R[b] R[a]=u+d",
    "do local u=R[b] R[a]=u+d end" },
  SUBI = { "R[a]=R[b]-d", "local u=R[b] R[a]=u-d",
    "do local u=R[b] R[a]=u-d end" },
  MULI = { "R[a]=R[b]*d", "local u=R[b] R[a]=u*d",
    "do local u=R[b] R[a]=u*d end" },
  DIVI = { "R[a]=R[b]/d", "local u=R[b] R[a]=u/d",
    "do local u=R[b] R[a]=u/d end" },
  MODI = { "R[a]=R[b]%d", "local u=R[b] R[a]=u%d",
    "do local u=R[b] R[a]=u%d end" },
  NOT = { "R[a]=not R[b]", "R[a]=(R[b]==nil or R[b]==false)",
    "do local u=R[b] R[a]=(u==nil or u==false) end" },
  LEN = { "R[a]=#R[b]", "local u=R[b] R[a]=#u", "do local u=R[b] R[a]=#u end" },
  BOOL = { "local v=R[b] local z=(v~=nil and v~=false) if c~=0 then z=not z end R[a]=z",
    "local v=R[b] R[a]=(((v~=nil and v~=false))~=(c~=0))",
    "local v=R[b] local z=(v~=nil and v~=false) R[a]=((c==0)==z)" },
  EQ = { "R[a]=(R[b]==R[c])", "local u=R[b] local v=R[c] R[a]=(u==v)",
    "do local u=R[b] local v=R[c] R[a]=(u==v) end" },
  NE = { "R[a]=(R[b]~=R[c])", "local u=R[b] local v=R[c] R[a]=(u~=v)",
    "do local u=R[b] local v=R[c] R[a]=(u~=v) end" },
  LT = { "R[a]=(R[b]<R[c])", "local u=R[b] local v=R[c] R[a]=(u<v)",
    "do local u=R[b] local v=R[c] R[a]=(u<v) end" },
  LE = { "R[a]=(R[b]<=R[c])", "local u=R[b] local v=R[c] R[a]=(u<=v)",
    "do local u=R[b] local v=R[c] R[a]=(u<=v) end" },
  GT = { "R[a]=(R[b]>R[c])", "local u=R[b] local v=R[c] R[a]=(u>v)",
    "do local u=R[b] local v=R[c] R[a]=(u>v) end" },
  GE = { "R[a]=(R[b]>=R[c])", "local u=R[b] local v=R[c] R[a]=(u>=v)",
    "do local u=R[b] local v=R[c] R[a]=(u>=v) end" },
  EQK = { "R[a]=(R[b]==K[d])", "local u=R[b] local v=K[d] R[a]=(u==v)",
    "do local u=R[b] local v=K[d] R[a]=(u==v) end" },
  NEK = { "R[a]=(R[b]~=K[d])", "local u=R[b] local v=K[d] R[a]=(u~=v)",
    "do local u=R[b] local v=K[d] R[a]=(u~=v) end" },
  LTK = { "R[a]=(R[b]<K[d])", "local u=R[b] local v=K[d] R[a]=(u<v)",
    "do local u=R[b] local v=K[d] R[a]=(u<v) end" },
  LEK = { "R[a]=(R[b]<=K[d])", "local u=R[b] local v=K[d] R[a]=(u<=v)",
    "do local u=R[b] local v=K[d] R[a]=(u<=v) end" },
  GETUPVAL = { "R[a]=U[b][1]", "local u=U[b] R[a]=u[1]",
    "do local u=U[b] R[a]=u[1] end" },
  SETUPVAL = { "U[b][1]=R[a]", "local u=U[b] u[1]=R[a]",
    "do local u=U[b] u[1]=R[a] end" },
  NEWCELL = { "if b==0 then R[a]={} else R[a]={R[b]} end",
    "if b==0 then R[a]=({}) else R[a]={R[b]} end",
    "if b==0 then R[a]=({}) else R[a]=({R[b]}) end" },
  GETCELL = { "R[a]=R[b][1]", "local u=R[b] R[a]=u[1]",
    "do local u=R[b] R[a]=u[1] end" },
  SETCELL = { "R[a][1]=R[b]", "local u=R[a] u[1]=R[b]",
    "do local t=R[a] t[1]=R[b] end" },
  GETGLOBAL = { "R[a]=$E[K[d]]", "local u=K[d] R[a]=$E[u]",
    "local u=(K[d]) R[a]=$E[u]" },
  SETGLOBAL = { "$E[K[d]]=R[a]", "local k=K[d] $E[k]=R[a]",
    "local k=(K[d]) local v=R[a] $E[k]=v" },
  NEWTABLE = { "R[a]={}", "local t={} R[a]=t", "R[a]=({})" },
  GETTABLE = { "R[a]=R[b][R[c]]", "local u=R[b] local v=R[c] R[a]=u[v]",
    "local u,v=R[b],R[c] R[a]=u[v]",
    "local u=R[b] local v=R[c] local w=u[v] R[a]=w" },
  SETTABLE = { "R[a][R[b]]=R[c]", "local t=R[a] local k=R[b] local v=R[c] t[k]=v",
    "local t,k,v=R[a],R[b],R[c] t[k]=v", "local t=R[a] t[R[b]]=R[c]" },
  GETFIELD = { "R[a]=R[b][K[d]]", "local u=R[b] local v=K[d] R[a]=u[v]",
    "local u,v=R[b],K[d] R[a]=u[v]",
    "local u=R[b] local v=u[K[d]] R[a]=v" },
  SETFIELD = { "R[a][K[d]]=R[b]", "local t=R[a] local k=K[d] t[k]=R[b]",
    "local t,k,v=R[a],K[d],R[b] t[k]=v",
    "local t=R[a] local k=K[d] local v=R[b] R[a][k]=v" },
  SELF = { "local t=R[b] R[a+1]=t R[a]=t[K[d]]",
    "local t=R[b] R[a+1]=t local f=t[K[d]] R[a]=f",
    "do local t=R[b] local f=t[K[d]] R[a+1]=t R[a]=f end" },
  GETIDXI = { "R[a]=R[b][d]", "local u=R[b] R[a]=u[d]",
    "do local u=R[b] R[a]=u[d] end" },
  SETIDXI = { "R[a][d]=R[b]", "local u=R[a] u[d]=R[b]",
    "do local u=R[a] u[d]=R[b] end" },
}
VMGen.VARIANTS = VARIANTS

-- Second variant pack: the base table above covers every opcode with three to
-- four shapes already, and this pack widens the hot ones further. With ten
-- encodings per opcode an instruction of the same kind can appear ten times in
-- one proto, so ten different bodies now exist for the ops a game script
-- actually spends frames in. Bodies keep the exact operator, operand order and
-- metamethod call order; only temporaries, nesting and statement grouping move.
local EXTRA_VARIANTS = {
  MOVE = { "do local z=R[b] R[a]=z end", "local z=R[a] z=R[b] R[a]=z" },
  LOADK = { "do local z=K[d] R[a]=z end", "local z=K local u=z[d] R[a]=u" },
  LOADNIL = { "local z=nil R[a]=z", "do local z R[a]=z end" },
  LOADBOOL = { "local z=b R[a]=(z~=0)",
    "R[a]=(b==0)and false or(b~=0)" },
  LOADINT = { "do R[a]=d end", "local z=d R[a]=z" },
  LOADNILN = { "local z=d while z>0 do R[a+z-1]=nil z=z-1 end",
    "do for j=0,d-1 do R[a+j]=nil end end" },
  ADD = { "do local u=R[b] local v=R[c] R[a]=u+v end",
    "local u=R[b] R[a]=u+R[c]" },
  SUB = { "do local u=R[b] local v=R[c] R[a]=u-v end",
    "local u=R[b] R[a]=u-R[c]" },
  MUL = { "do local u=R[b] local v=R[c] R[a]=u*v end",
    "local u=R[b] R[a]=u*R[c]" },
  DIV = { "do local u=R[b] local v=R[c] R[a]=u/v end",
    "local u=R[b] R[a]=u/R[c]" },
  MOD = { "do local u=R[b] local v=R[c] R[a]=u%v end",
    "local u=R[b] R[a]=u%R[c]" },
  POW = { "do local u=R[b] local v=R[c] R[a]=u^v end",
    "local u=R[b] R[a]=u^R[c]" },
  IDIV = { "local u=R[b] local v=R[c] R[a]=$MM.floor(u/v)",
    "do local w=R[b]/R[c] R[a]=$MM.floor(w) end" },
  UNM = { "if true then R[a]=-R[b] end", "local u=R[b] R[a]=-(u)" },
  CONCAT = { "local u=R[b] R[a]=u..R[c]", "do local z=R[b]..R[c] R[a]=z end" },
  BAND = { "local u=R[b] R[a]=$BW(u,R[c],1)",
    "do local u=R[b] local v=R[c] R[a]=$BW(u,v,1) end" },
  BOR = { "local u=R[b] R[a]=$BW(u,R[c],2)",
    "do local u=R[b] local v=R[c] R[a]=$BW(u,v,2) end" },
  BXOR = { "local u=R[b] R[a]=$BW(u,R[c],3)",
    "do local u=R[b] local v=R[c] R[a]=$BW(u,v,3) end" },
  BNOT = { "local u=R[b] R[a]=$BN(u)", "do local u=R[b] R[a]=$BN(u) end" },
  SHL = { "local u=R[b] R[a]=$SHL(u,R[c])",
    "do local u=R[b] local v=R[c] R[a]=$SHL(u,v) end" },
  SHR = { "local u=R[b] R[a]=$SHR(u,R[c])",
    "do local u=R[b] local v=R[c] R[a]=$SHR(u,v) end" },
  NOT = { "local u=R[b] R[a]=(not u)", "do R[a]=not R[b] end" },
  LEN = { "R[a]=(#R[b])", "do local u=R[b] R[a]=#u end" },
  BOOL = { "local v=R[b] local z=(v~=nil and v~=false) " ..
    "if c==0 then R[a]=z else R[a]=not z end",
    "local v=R[b] local z=(v==nil or v==false) R[a]=((c~=0)==z)" },
  EQ = { "R[a]=((R[b])==(R[c]))", "if true then R[a]=(R[b]==R[c]) end" },
  NE = { "R[a]=((R[b])~=(R[c]))", "if true then R[a]=(R[b]~=R[c]) end" },
  LT = { "R[a]=((R[b])<(R[c]))", "if true then R[a]=(R[b]<R[c]) end" },
  LE = { "R[a]=((R[b])<=(R[c]))", "if true then R[a]=(R[b]<=R[c]) end" },
  GT = { "R[a]=((R[b])>(R[c]))", "if true then R[a]=(R[b]>R[c]) end" },
  GE = { "R[a]=((R[b])>=(R[c]))", "if true then R[a]=(R[b]>=R[c]) end" },
  EQK = { "R[a]=((R[b])==(K[d]))", "if true then R[a]=(R[b]==K[d]) end" },
  NEK = { "R[a]=((R[b])~=(K[d]))", "if true then R[a]=(R[b]~=K[d]) end" },
  LTK = { "R[a]=((R[b])<(K[d]))", "if true then R[a]=(R[b]<K[d]) end" },
  LEK = { "R[a]=((R[b])<=(K[d]))", "if true then R[a]=(R[b]<=K[d]) end" },
  ADDK = { "do local u=R[b] R[a]=u+K[d] end", "local u=R[b] R[a]=u+K[d]" },
  SUBK = { "do local u=R[b] R[a]=u-K[d] end", "local u=R[b] R[a]=u-K[d]" },
  MULK = { "do local u=R[b] R[a]=u*K[d] end", "local u=R[b] R[a]=u*K[d]" },
  DIVK = { "do local u=R[b] R[a]=u/K[d] end", "local u=R[b] R[a]=u/K[d]" },
  MODK = { "do local u=R[b] R[a]=u%K[d] end", "local u=R[b] R[a]=u%K[d]" },
  POWK = { "do local u=R[b] R[a]=u^K[d] end", "local u=R[b] R[a]=u^K[d]" },
  IDIVK = { "do local u=R[b]/K[d] R[a]=$MM.floor(u) end" },
  ADDI = { "R[a]=(R[b])+d", "local u=R[b] R[a]=u+d" },
  SUBI = { "R[a]=(R[b])-d", "local u=R[b] R[a]=u-d" },
  MULI = { "R[a]=(R[b])*d", "local u=R[b] R[a]=u*d" },
  DIVI = { "R[a]=(R[b])/d", "local u=R[b] R[a]=u/d" },
  MODI = { "R[a]=(R[b])%d", "local u=R[b] R[a]=u%d" },
  GETUPVAL = { "local z=U[b] R[a]=z[1]", "R[a]=(U[b])[1]",
    "do local z=U[b][1] R[a]=z end" },
  SETUPVAL = { "local z=U[b] z[1]=R[a]", "do local z=R[a] U[b][1]=z end" },
  NEWCELL = { "local z={} if b~=0 then z[1]=R[b] end R[a]=z",
    "if b==0 then R[a]=({}) else R[a]=({R[b]}) end" },
  GETCELL = { "local z=R[b] R[a]=z[1]", "R[a]=(R[b])[1]" },
  SETCELL = { "local z=R[b] R[a][1]=z", "do R[a][1]=R[b] end" },
  GETGLOBAL = { "local z=$E local u=K[d] R[a]=z[u]",
    "do R[a]=$E[K[d]] end" },
  SETGLOBAL = { "local z=$E local u=K[d] z[u]=R[a]",
    "do local z=R[a] $E[K[d]]=z end" },
  NEWTABLE = { "local z={} do R[a]=z end", "R[a]={}" },
  GETTABLE = { "local z=R[b] R[a]=z[R[c]]",
    "do local z=R[b][R[c]] R[a]=z end" },
  SETTABLE = { "local z=R[a] local w=R[b] z[w]=R[c]",
    "do R[a][R[b]]=R[c] end" },
  GETFIELD = { "local z=R[b] R[a]=z[K[d]]",
    "do local z=R[b][K[d]] R[a]=z end" },
  SETFIELD = { "local z=R[a] local w=K[d] z[w]=R[b]",
    "do R[a][K[d]]=R[b] end" },
  SELF = { "local z=R[b] R[a+1]=z R[a]=z[K[d]]",
    "do local z=R[b] R[a+1]=z R[a]=z[K[d]] end" },
  GETIDXI = { "local z=R[b] R[a]=z[d]", "R[a]=(R[b])[d]" },
  SETIDXI = { "local z=R[b] R[a][d]=z", "do R[a][d]=R[b] end" },
  SETLIST = {
    "local n=d if n<0 then n=S.top-c end if n<0 then n=0 end " ..
      "for j=1,n do R[a][b+j-1]=R[c+j-1] end if d<0 then S.top=c end",
    "local n=(d>=0)and d or(S.top-c) if n<0 then n=0 end " ..
      "local t=R[a] local q=b local st=c " ..
      "for j=1,n do t[q+j-1]=R[st+j-1] end if d<0 then S.top=c end",
    "do local n=(d<0)and(S.top-c)or d if n<0 then n=0 end " ..
      "for j=1,n do R[a][b+j-1]=R[c+j-1] end end if d<0 then S.top=c end",
  },
}
for name, extra in pairs(EXTRA_VARIANTS) do
  local list = VARIANTS[name]
  if not list then
    list = { HANDLERS[name] }
    VARIANTS[name] = list
  end
  for i = 1, #extra do list[#list + 1] = extra[i] end
end

-- Third pack: one more distinct shape for the ops a frame loop spends its time
-- in, plus polymorphic control-flow bodies. With eighteen encodings a hot
-- opcode repeats its body at most twice per prototype, so the shapes now
-- outnumber the slots. Same rule as above: only temporaries, nesting and
-- statement grouping move, never the operator or the metamethod order.
local EXTRA_VARIANTS2 = {
  MOVE = { "local z=R[b] do R[a]=z end" },
  LOADK = { "local z=K do R[a]=z[d] end" },
  GETTABLE = { "local z=R[b] local w=R[c] do R[a]=z[w] end" },
  SETTABLE = { "local z=R[a] do z[R[b]]=R[c] end" },
  GETFIELD = { "local z=R[b] do R[a]=z[K[d]] end" },
  SETFIELD = { "local z=R[a] do z[K[d]]=R[b] end" },
  SELF = { "local z=R[b] do R[a+1]=z R[a]=z[K[d]] end" },
  GETGLOBAL = { "local z=$E do R[a]=z[K[d]] end" },
  SETGLOBAL = { "local z=$E do z[K[d]]=R[a] end" },
  ADD = { "local u,v=R[b],R[c] do R[a]=u+v end" },
  SUB = { "local u,v=R[b],R[c] do R[a]=u-v end" },
  MUL = { "local u,v=R[b],R[c] do R[a]=u*v end" },
  DIV = { "local u,v=R[b],R[c] do R[a]=u/v end" },
  LT = { "local u,v=R[b],R[c] do R[a]=(u<v) end" },
  LE = { "local u,v=R[b],R[c] do R[a]=(u<=v) end" },
  EQ = { "local u,v=R[b],R[c] do R[a]=(u==v) end" },
  JMP = { "do return pc+1+d end", "return pc+1+(d)" },
  JMPF = { "if R[a] then return pc+1 end return pc+1+d" },
  JMPT = { "if not R[a] then return pc+1 end return pc+1+d" },
  TEST = { "if ((R[b]==nil or R[b]==false)~=(a~=0)) then return pc+2 end " ..
    "return pc+1" },
  TESTSET = { "local z=(R[b]~=nil and R[b]~=false) if z==(a~=0) then " ..
    "R[c]=R[b] return pc+2 end return pc+1" },
}
for name, extra in pairs(EXTRA_VARIANTS2) do
  local list = VARIANTS[name]
  if not list then
    list = { HANDLERS[name] }
    VARIANTS[name] = list
  end
  for i = 1, #extra do list[#list + 1] = extra[i] end
end

local DECOYS = {
  "return pc+1",
  "local z=a*0 return pc+1+z",
  "if a==b then return pc+1 end return pc+1",
  "local z=0 for j=1,z do z=z+1 end return pc+1",
  "local z=(a+b)-(b+a) return pc+1+z",
  "local z=R[a] return pc+1",
  "local z=S.top+0 return pc+1",
  "local z=d*0 if z~=0 then return pc end return pc+1",
  "local z=0 if a>z then z=a-a end return pc+1+z",
  "local z=b-b return pc+1+z",
  "if c>d then return pc+1 end return pc+1",
  "local z=0 if b<0 then z=0 end return pc+1+z",
  "local z=a+b return pc+1+(z-z)",
  "local z=c+d return pc+1+(z-z)",
  "if b==c then return pc+1 end return pc+1",
  "local z=0 while z>0 do z=z-1 end return pc+1",
  "if d==d then local z=S.top+0 end return pc+1",
  "local z=a local u=R[a] return pc+1",
  "local z=-a+a return pc+1+z",
  "local z=0 repeat z=z+0 until z>=0 return pc+1",
  "if a~=a then return pc end return pc+1",
  "local z=b*1-b return pc+1+z",
  "if c==0 then return pc+1 end return pc+1",
  "local z=0 if d>0 then z=d-d end return pc+1+z",
  "return pc+1+(a-a)",
  "local z=0 for j=1,0 do z=1 end return pc+1+z",
  "if a~=b then return pc+1 end return pc+1",
  "local z=d if z<0 then z=0 end return pc+1+(z-z)",
  "if c==c then local z=S.top+0 end return pc+1",
  "local z=a+b-(b+a) return pc+1+z",
  "if b<=a and a<=b then return pc+1 end return pc+1",
  "local z=0 if R[a]~=nil then z=0 end return pc+1+z",
  "local z=d*0+b*0 return pc+1+z",
  "local u=b local v=c if u==v then return pc+1 end return pc+1",
  "local u=b local v=c if u~=v then return pc+1 end return pc+1",
  "local u=b local v=c if u<v then return pc+1 end return pc+1",
  "local u=b local v=c if u<=v then return pc+1 end return pc+1",
  "local u=R[a] if u==nil then return pc+1 end return pc+1",
  "local u=R[a] if u~=nil then return pc+1 end return pc+1",
  "local u=a local v=d if u==v then return pc+1 end return pc+1",
  "local u=a local v=d if u~=v then return pc+1 end return pc+1",
  "local u=R[a] if type(u)==\"table\" then return pc+1 end return pc+1",
  "local u=R[a] if type(u)==\"string\" then return pc+1 end return pc+1",
  "local u=R[a] if type(u)==\"number\" then return pc+1 end return pc+1",
  "local u=R[b] local v=R[c] local w=u v=w if v~=nil then return pc+1 end return pc+1",
  "local u=R[b] local v=R[c] local w=(u or v) if w==w then return pc+1 end return pc+1",
  "local u=R[b] local v=R[c] local w=(u and v) if w~=w then return pc+1 end return pc+1",
  "if R[a]==nil then if R[b]==nil then return pc+1 end end return pc+1",
  "if a<b then if c<d then return pc+1 end end return pc+1",
  "if a<=b then if c<=d then return pc+1 end end return pc+1",
  "local z=0 while z<0 do z=z+1 end return pc+1+z",
  "local z=0 while z~=z do z=z+1 end return pc+1+z",
  "local z=0 for j=1,-1 do z=z+1 end return pc+1+z",
  "local z=0 for j=1,1 do z=z+0 end return pc+1+z",
  "local z=a-b if z<0 then z=0 end return pc+1+z-z",
  "local z=c-d if z>0 then z=0 end return pc+1+z-z",
  "local z=(a*d)-(a*d) return pc+1+z",
  "local z=(b+c)-(c+b) return pc+1+z",
  "local z=K[d] if z==z then return pc+1 end return pc+1",
  "local z=K[d] if z~=nil then return pc+1 end return pc+1",
  "local z=b if z==c then return pc+1 end return pc+1",
  "local z=R[a] if z==R[a] then return pc+1 end return pc+1",
  "local z=#tostring(a) if z>0 then return pc+1 end return pc+1",
  "local z=tostring(a)..tostring(b) if #z>=0 then return pc+1 end return pc+1",
  "local z=0 pcall(function() z=0 end) return pc+1+z",
  "local z=0 if c>0 then z=c-c end return pc+1+z",
  "local z=0 if d>=0 then z=d-d end return pc+1+z",
  "local z=0 if R[a]==nil then z=a-a end return pc+1+z",
  "local z=0 if R[b]~=nil then z=b-b end return pc+1+z",
  "local z=0 if a>=b then z=a-b else z=b-a end return pc+1+(z-z)",
  "local z=0 if c>d then z=1 else z=0 end return pc+1+(z-z)",
  "local z=d local w=a if z==w then return pc+1 end return pc+1",
  "local z=0 for j=1,2 do z=z+0 end return pc+1+z",
  "local z=0 while z<1 do z=z+1 end return pc+1",
  "local z=(a or 0)*0 return pc+1+z",
  "local z=(b or 0)-(b or 0) return pc+1+z",
  "local u=R[a] local v=R[b] if (u==nil)~=(v==nil) then return pc+1 end return pc+1",
  "local z=0 if K[d]~=K[d] then z=0 end return pc+1+z",
  "local z=0 if a==a then z=0 end return pc+1+z",
  "local u=a local v=b if u==v then return pc+1 end return pc+1",
  "local z=0 if #tostring(a)>0 then z=0 end return pc+1+z",
  "local u=b local v=d local w=(u==v) if w then return pc+1 end return pc+1",
  "local z=0 for j=1,3 do z=z+0 end return pc+1+z",
  "local z=a*a-a*a return pc+1+z",
  "if b~=nil then if c~=nil then return pc+1 end end return pc+1",
  "local z=0 if R[a]==R[a] then z=0 end return pc+1+z",
  "local u=b local v=c local w=u<=v if w or not w then return pc+1 end return pc+1",
  -- Camouflage: the same shapes a real handler has (register/upvalue/frame
  -- writes), each behind a predicate that is false for every numeric operand.
  -- Corrupted bytecode that lands here still returns inert, but a dumped table
  -- no longer separates decoys from handlers by their body vocabulary.
  "if a~=a then R[a]=R[b] end return pc+1",
  "if b<b then R[a]=R[b] end return pc+1",
  "if c~=c then R[a]=R[b]+R[c] end return pc+1",
  "if d~=d then R[a]=nil end return pc+1",
  "if a~=a then S.top=b end return pc+1",
  "if b<b then U[a]=R[b] end return pc+1",
  "if c<c then K[d]=R[a] end return pc+1",
  "if d~=d then S.ar[a]=R[b] end return pc+1",
  "if a~=a then R[b]=K[c] S.top=a+1 end return pc+1",
  "if b<b then U[c][1]=R[a] end return pc+1",
  "if c~=c then R[a]=R[b] S.ret={n=0} end return pc+1",
  "if d~=d then S.p.k[d]=R[a] end return pc+1",
  -- Shape pool, second wave: same predicate families with different literal
  -- order, loop forms and temporaries, so two builds never repeat the same
  -- decoy multiset even when the literal list is unchanged.
  "local z=0 if a==b then z=a-b else z=b-a end return pc+1+(z-z)",
  "local z=0 if c<=d then z=d-c else z=c-d end return pc+1+(z-z)",
  "local z=0 if R[a]==nil then z=0 end return pc+1+z",
  "local z=0 if R[b]==nil then z=0 end return pc+1+z",
  "local u=a local v=c if u<v then return pc+1 end " ..
    "if u>v then return pc+1 end return pc+1",
  "local u=b local v=d if u<=v then return pc+1 end " ..
    "if u>=v then return pc+1 end return pc+1",
  "local z=0 repeat z=z+1 until z>0 return pc+1+(z-z)",
  "local z=0 while z<2 do z=z+1 end return pc+1+(z-z)",
  "local z=0 for j=1,4 do z=z*0 end return pc+1+z",
  "local z=K[d] if z==z then return pc+1 end return pc+1",
  "local z=#tostring(b) if z>=0 then return pc+1 end return pc+1",
  "local u=R[a] if u==u then return pc+1 end return pc+1",
  "local u=R[b] if u~=u then return pc+1 end return pc+1",
  "local z=0 if a~=b then z=0 else z=0 end return pc+1+z",
  "local z=0 if c~=d then z=0 else z=0 end return pc+1+z",
  "local z=(a*a)+(b*b) return pc+1+(z-z)",
  "local z=(d*d)-(d*d) return pc+1+z",
  "if a<b then if c<d then return pc+1 end end return pc+1",
  "if a>=b then if c>=d then return pc+1 end end return pc+1",
  "local z=b local w=c if z==w then return pc+1 end return pc+1",
  "local z=0 if R[a]~=nil then z=z+0 end return pc+1+z",
  "local z=0 if R[b]~=nil then z=z+0 end return pc+1+z",
  "local u,v=a,b if u==v then return pc+1 end return pc+1",
  "local u,v=c,d if u~=v then return pc+1 end return pc+1",
  "local z=0 for j=1,5 do z=z-z end return pc+1+z",
  "local z=0 pcall(function() z=z+0 end) return pc+1+z",
  "local z=0 if type(R[a])==\"nil\" then z=0 end return pc+1+z",
  "local z=0 if type(a)==\"number\" then z=0 end return pc+1+z",
  "local z=0 if #tostring(c)>=0 then z=0 end return pc+1+z",
  "local z=0 if d~=d then z=0 end return pc+1+z",
  "if a~=a then R[a]=R[b] R[b]=R[a] end return pc+1",
  "if c<c then R[a]=K[d] end return pc+1",
  "if b~=b then S.top=d end return pc+1",
  "if d<d then U[b][1]=R[a] end return pc+1",
  "if a~=a then R[a]=R[b] if b<0 then R[b]=nil end end return pc+1",
  "if b<b then S.ret={n=c} end return pc+1",
}

local DECOY_PREFIX = {
  "local _0=a*0 ",
  "local _0=b-b ",
  "local _0=c*0 ",
  "local _0=d-d ",
  "local _0=(a+b)-(a+b) ",
  "local _0=(a<b) and 0 or 0 ",
  "local _0=(c<=d) and 0 or 0 ",
  "local _0=#tostring(d)*0 ",
  "local _0=(a>=b) and 0 or 0 ",
  "local _0=(d>c) and 0 or 0 ",
  "local _0=(#tostring(a))*0 ",
  "local _0=(a or 0)-a ",
}

VMGen.DECOYS = DECOYS

-- Generated decoys. The literal pool below tops out at a fixed set of shapes;
-- the synthesizer composes a predicate that cannot hold for numeric operands
-- with a camouflage action drawn from the real handler vocabulary, so every
-- build ships decoy bodies no earlier build contained and the decoy set is not
-- enumerable from one sample. Every shape ends in an unconditional return, so
-- a corrupted instruction that lands here still advances or halts inertly.
local DECOY_NEVER = {
  "a~=a", "b<b", "c~=c", "d<d",
  "a<b and b<a", "c<d and d<c", "a>b and b>a",
  "a==a+1", "b==b-1", "(a-a)~=0", "(d-d)~=0",
  "a>0 and a<0", "b>0 and b<0", "c>0 and c<0", "d>0 and d<0",
  "a~=a and b~=b", "(c-c)>0", "(a+b)~=(b+a)",
  "pc<0", "a~=a or b<b",
}
local DECOY_ACT = {
  "R[a]=R[b]", "R[a]=nil", "S.top=b", "U[a]=R[b]", "K[d]=R[a]",
  "R[a]=R[b]+R[c]", "R[b]=K[c]", "U[c][1]=R[a]",
  "S.ret={n=0}", "S.ar[a]=R[b]", "R[a]=R[b] and R[c]",
  "S.p.k[d]=R[a]", "R[a]=R[b] R[b]=R[a]",
}
local DECOY_TAIL = {
  "return pc+1", "return pc+1", "return pc+1",
  "return pc+1+(a-a)", "return 1+pc", "return pc+1+0",
}
local function synthDecoy(rng)
  local g1 = DECOY_NEVER[rng(#DECOY_NEVER)]
  local g2 = DECOY_NEVER[rng(#DECOY_NEVER)]
  local act = DECOY_ACT[rng(#DECOY_ACT)]
  local tail = DECOY_TAIL[rng(#DECOY_TAIL)]
  local shape = rng(5)
  if shape == 1 then
    return "if " .. g1 .. " then " .. act .. " end " .. tail
  elseif shape == 2 then
    return "if " .. g1 .. " then if " .. g2 .. " then " .. act ..
      " end end " .. tail
  elseif shape == 3 then
    return "local z=0 if " .. g1 .. " then z=1 end " ..
      "if z~=0 then " .. act .. " end " .. tail
  elseif shape == 4 then
    return "do local u=R[a] if " .. g1 .. " then " .. act .. " end end " ..
      tail
  end
  return "local u=b local v=c if u~=v and " .. g1 .. " then " .. act ..
    " end if u==v and " .. g2 .. " then " .. act .. " end " .. tail
end

-- Semantically neutral statement wrappers. Every handler body already ends in
-- a return, so wrapping only changes the nesting shape a dump shows: two builds
-- of one opcode differ in statement structure, not just in temp names, and no
-- body is a single flat line a signature scanner can normalise away.
local WRAP_SHAPES = {
  function(b) return b end,
  function(b) return "do " .. b .. " end" end,
  function(b) return "if pc>0 then " .. b .. " end" end,
  function(b) return "if pc~=0 then " .. b .. " end" end,
  function(b) return "do if pc>=1 then " .. b .. " end end" end,
  function(b) return "if pc==pc then " .. b .. " end" end,
  function(b) return "repeat " .. b .. " until true" end,
  function(b) return "if 1 then " .. b .. " end" end,
  function(b) return "do do " .. b .. " end end" end,
}
local function wrapBody(body, rng)
  return WRAP_SHAPES[rng(#WRAP_SHAPES)](body)
end

-- Per-entry salt. Every handler body starts with a neutral declaration whose
-- local name embeds the entry's dispatch key, so two entries -- of the same
-- opcode or of different opcodes -- can never share a body text. A dumper that
-- clusters handlers by identical source therefore gets one cluster per entry
-- instead of one cluster per opcode, and the key in the name is the public key
-- already present in the handler table, so it leaks nothing the table did not.
-- The expressions only touch decoded operands and pc (all numeric), so a
-- salted body is semantically identical to the unsalted one.
local SALT_SHAPES = {
  function(k) return "local _k" .. k .. "v=a*0 " end,
  function(k) return "local _k" .. k .. "v=b-b " end,
  function(k) return "local _k" .. k .. "v=c*0 local _k" .. k .. "w=d-d " end,
  function(k) return "do local _k" .. k .. "v=d-d end " end,
  function(k) return "if pc<0 then local _k" .. k .. "v=a-a end " end,
  function(k) return "local _k" .. k .. "v=(d+a)-(a+d) " end,
  function(k) return "local _k" .. k .. "v=(b+c)-(c+b) " end,
}
local function saltBody(body, num, rng)
  return SALT_SHAPES[rng(#SALT_SHAPES)](num) .. body
end

-- ------------------------------------------------------------------- helpers
local function makeRng(seed)
  local state = math.floor(tonumber(seed) or 0) % 4294967296
  if state < 0 then state = state + 4294967296 end
  return function(n)
    state = (state * 1664525 + 1013904223) % 4294967296
    if n <= 65536 then return math.floor(state / 65536) % n + 1 end
    return state % n + 1
  end
end

local function shuffle(list, rng)
  for i = #list, 2, -1 do
    local j = rng(i)
    list[i], list[j] = list[j], list[i]
  end
end

local function quote(s)
  local out = { '"' }
  for i = 1, #s do
    local b = s:byte(i)
    if b == 34 then out[#out + 1] = '\\"'
    elseif b == 92 then out[#out + 1] = "\\\\"
    elseif b >= 32 and b < 127 then out[#out + 1] = s:sub(i, i)
    else out[#out + 1] = string.format("\\%03d", b) end
  end
  out[#out + 1] = '"'
  return table.concat(out)
end

-- Raw UTF-8 literal: printable ASCII stays, complete multi-byte sequences are
-- emitted as their original glyphs, so the transported blob reads as symbol
-- salad in the shipped file. Quotes, backslashes and control bytes stay
-- escaped; only whole code points ever reach this function (chunk boundaries
-- are glyph-aligned), so no truncated sequence can break the browser pipeline.
local function quoteRaw(s)
  local out = { '"' }
  for i = 1, #s do
    local b = s:byte(i)
    if b == 34 then out[#out + 1] = '\\"'
    elseif b == 92 then out[#out + 1] = "\\\\"
    elseif b == 10 then out[#out + 1] = "\\n"
    elseif b == 13 then out[#out + 1] = "\\r"
    elseif b == 9 then out[#out + 1] = "\\t"
    elseif b >= 32 then out[#out + 1] = s:sub(i, i)
    else out[#out + 1] = string.format("\\%03d", b) end
  end
  out[#out + 1] = '"'
  return table.concat(out)
end

-- Transport chunks contain only palette symbols (single-byte printable ASCII)
-- plus `=` pads: never a quote, a backslash or a control byte. They can be
-- quoted by wrapping, which skips a per-byte scan of the whole ~250 KB salad.
local function quoteSymbols(s)
  return '"' .. s .. '"'
end

-- The transport alphabet is every printable 7-bit ASCII glyph except `"`, `\`
-- and `=`: 91 symbols, against base64's 64. Every symbol is one byte, so the
-- artifact is pure ASCII: no executor, hub, clipboard or loader can mangle a
-- multi-byte glyph on the way in, and the file survives any re-encoding a
-- host applies to pasted text. `"` and `\` are excluded so a chunk can be
-- quoted by wrapping, and `=` is kept out of the pool because it is the pad
-- marker.
local SINGLE_POOL = {}
do
  for b = 33, 126 do
    if b ~= 34 and b ~= 61 and b ~= 92 then
      SINGLE_POOL[#SINGLE_POOL + 1] = string.char(b)
    end
  end
end

-- Per-build transport alphabet: all 91 symbols drawn in seed order. The
-- mapping is shipped (the decoder needs it) but changes every build, so a
-- classifier or precomputed table keyed on a previous alphabet is useless.
local function symbolAlphabet(rng)
  local pick = {}
  for i = 1, #SINGLE_POOL do pick[i] = SINGLE_POOL[i] end
  local out = {}
  for i = #SINGLE_POOL, 2, -1 do
    local j = rng(i)
    pick[i], pick[j] = pick[j], pick[i]
  end
  for i = 1, #SINGLE_POOL do out[i] = pick[i] end
  return out
end

-- Transport encoding for the payload blob. Three bytes become four base-91
-- digits: the same 4/3 expansion as base64, but drawn from 91 glyphs, so the
-- stream is not decodable by any off-the-shelf alphabet and a four-symbol
-- group spans a wider value range. Chunks are built group by group: a
-- boundary may never land inside one, which a plain byte slice would do.
local function saladEncode(s, chars, maxBytes)
  -- Each chunk is decoded on its own, so a boundary may never land inside a
  -- 4-symbol group. Symbols are appended straight into the open chunk; a group
  -- is measured first and the chunk flushed before it when it would overflow,
  -- so no intermediate per-group string is ever built.
  local parts, cur, curLen = {}, {}, 0
  local function flush()
    if curLen > 0 then
      parts[#parts + 1] = table.concat(cur)
      cur = {}
      curLen = 0
    end
  end
  local function put(a, b, c, d)
    local len = #a + #b + #c
    if d then len = len + #d end
    if curLen + len > maxBytes and curLen > 0 then flush() end
    cur[#cur + 1] = a
    cur[#cur + 1] = b
    cur[#cur + 1] = c
    if d then cur[#cur + 1] = d end
    curLen = curLen + len
  end
  local n = #s
  local i = 1
  while i + 2 <= n do
    local a, b, c = s:byte(i, i + 2)
    local v = a * 65536 + b * 256 + c
    put(chars[math.floor(v / 753571) + 1],
      chars[math.floor(v / 8281) % 91 + 1],
      chars[math.floor(v / 91) % 91 + 1],
      chars[v % 91 + 1])
    i = i + 3
  end
  local rest = n - i + 1
  if rest == 1 then
    local v = s:byte(i)
    put(chars[math.floor(v / 91) + 1], chars[v % 91 + 1], "==")
  elseif rest == 2 then
    local a, b = s:byte(i, i + 1)
    local v = a * 256 + b
    put(chars[math.floor(v / 8281) + 1],
      chars[math.floor(v / 91) % 91 + 1],
      chars[v % 91 + 1], "=")
  end
  flush()
  return parts
end

local function serializeNumber(v)
  if v ~= v then return "(0/0)" end
  if v == math.huge then return "(1/0)" end
  if v == -math.huge then return "(-1/0)" end
  if v == 0 and 1 / v < 0 then return "-0.0" end
  if math.type and math.type(v) == "integer" then
    -- The decimal spelling of the minimum integer parses as a negated float.
    if v == math.mininteger then return "(" .. tostring(v + 1) .. "-1)" end
    return tostring(v)
  end
  local text = string.format("%.17g", v)
  if math.type and math.type(v) == "float" and
     not text:find("[%.eE]") then
    text = text .. ".0"
  end
  return text
end

local function serializeValue(v)
  local t = type(v)
  if t == "string" then return quote(v) end
  if t == "number" then return serializeNumber(v) end
  if t == "boolean" then return tostring(v) end
  return "nil"
end

-- Per-prototype instruction keystream. Every instruction word carries
-- Each instruction adds a piecewise offset to the quadratic mixer. The
-- window length (23 + kb%74) and per-window shift (1 + kc%md) are derived
-- from the original four per-prototype coefficients. This avoids additional
-- integrity words and introduces discontinuities between instruction windows.
-- Since the coefficients ship with the runtime, this is NOT a cryptographic
-- trust boundary and will not stop someone who controls the host interpreter.
local function buildKeystream(seed, count)
  local rng = makeRng((seed or VMGen.DEFAULT_SEED) + 0x4B1D)
  local ks, parts = {}, {}
  for pi = 1, count do
    local ka = rng(2048) * 2 - 1
    local kc = rng(2048) * 2 - 1
    local kb = rng(4096) - 1
    local md = 3001 + rng(4000)
    ks[pi] = { ka, kc, kb, md }
    parts[pi] = "{" .. ka .. "," .. kc .. "," .. kb .. "," .. md .. "}"
  end
  return ks, parts
end

local function koff(pc, ks)
  -- The piecewise factor is derived from existing per-prototype coefficients,
  -- keeping the four-word mixer and hot-path integrity checksum unchanged.
  local window = 23 + ks[3] % 74
  local shift = 1 + ks[2] % ks[4]
  return (pc * pc * ks[2] + pc * ks[1] + ks[3] +
    math.floor((pc - 1) / window) * shift) % ks[4]
end

-- Reversible prototype/window dispatch-bank permutation. The mapping is
-- derived from the four existing keystream words and carries no secret.
-- It keeps the packed and direct transports semantically identical, while
-- removing the global "opcode slot N means handler N" invariant across
-- prototypes and instruction windows.
local function bankSlot(slot, pi, pc, ks, count)
  local windowIndex = math.floor((pc - 1) / (23 + ks[3] % 74))
  local rotation = (ks[1] * pi + ks[3] +
    windowIndex * (1 + ks[2] % count)) % count
  if (ks[2] + pi + windowIndex) % 2 == 0 then
    return (count - slot + rotation) % count + 1
  end
  return (slot - 1 + rotation) % count + 1
end

local function encodeProtos(protos, opkeys, layouts, operandMasks, rng)
  local out = {}
  local count = 0
  for pi = 1, #protos do
    local P = protos[pi]
    local code = {}
    for i = 1, #P.code do
      local I = P.code[i]
      local keys = opkeys[I.op]
      if not keys then
        error("vmgen: unknown opcode '" .. tostring(I.op) .. "'", 0)
      end
      local key = keys[rng(#keys)]
      local layout, mask = layouts[key], operandMasks[key]
      -- The first three numeric operand slots carry a second, instruction-
      -- position dependent mask. Even the same handler alias used twice gets
      -- a different on-wire operand encoding. The float immediate d remains
      -- exactly unchanged (including its -0.0 subtype).
      local pcBias = mask.pc and ((i * mask.pc.mul + mask.pc.salt +
        pi * mask.pc.protoMul) % mask.pc.mod) or 0
      -- All four operands, the jump/constant immediate included, are placed
      -- through the per-key permutation and sign/bias mask. A dumped word has
      -- no position that reliably means "this is the offset" any more.
      local word = { key, 0, 0, 0, 0 }
      local operands = { I.a or 0, I.b or 0, I.c or 0, I.d or 0 }
      for slot = 1, 4 do
        local sign, bias = mask.signs[slot], mask.biases[slot]
        if sign == 1 and bias == 0 then
          -- Identity slot (the immediate d): assign raw so a float subtype
          -- and negative zero survive untouched.
          word[layout[slot]] = operands[slot]
        else
          word[layout[slot]] = operands[slot] * sign + bias +
            (slot <= 3 and pcBias or 0)
        end
      end
      code[i] = word
      count = count + 1
    end
    out[pi] = {
      c = code,
      k = P.k or {},
      u = P.updesc or {},
      a = P.params or 0,
      v = P.vararg and true or false,
    }
  end
  return out, count
end

-- ------------------------------------------------------------------- stages
function VMGen.randomize(compiled, opts)
  local problems = Compiler.validate(compiled)
  if #problems > 0 then
    error("vmgen: validation failed: " .. table.concat(problems, "; "), 0)
  end
  if opts == nil then opts = {} end
  if type(opts) ~= "table" or getmetatable(opts) ~= nil then
    error("vmgen: options must be a plain table", 0)
  end
  local function finiteOption(name, default)
    local value = opts[name]
    if value == nil then return default end
    local kind = type(value)
    local n = (kind == "number" or kind == "string") and tonumber(value) or nil
    if n == nil or n ~= n or n == math.huge or n == -math.huge then
      error("vmgen: invalid " .. name .. ": finite number expected", 0)
    end
    return n
  end
  local decoyCount = math.floor(finiteOption("decoys", VMGen.DEFAULT_DECOYS))
  if decoyCount < 0 then decoyCount = 0 end
  if decoyCount > VMGen.MAX_DECOYS then decoyCount = VMGen.MAX_DECOYS end
  -- Alias handlers per opcode. Each alias is a whole generated function, so the
  -- handler table is the fixed cost of every build; the pipeline scales it with
  -- source size and callers may override it, but it never exceeds the catalog.
  local encCount = math.floor(finiteOption("encodings",
    VMGen.ENCODINGS_PER_OPCODE))
  if encCount < 1 then encCount = 1 end
  if encCount > VMGen.ENCODINGS_PER_OPCODE then
    encCount = VMGen.ENCODINGS_PER_OPCODE
  end

  -- Use the same canonical seed for instruction keys, emitted names and every
  -- later stage. Keeping the raw option here made equivalent RNG seeds emit
  -- different runtimes (and booleans failed only after randomization).
  local seed = math.floor(finiteOption("seed", VMGen.DEFAULT_SEED)) % 4294967296
  local rng = makeRng(seed)
  -- [SIZE-LIVE] Compact mode emits only executable ISA handlers reachable
  -- from the compiled prototypes. Every referenced opcode keeps the same
  -- randomized aliases, operand masks and dispatch-time integrity checks.
  -- Unreferenced opcode handlers add size and analysis surface, not VM safety.
  -- Standard mode retains the full ISA as a compatibility/decoy option.
  local activeOps = Compiler.OPS
  if opts.pruneHandlers == true then
    local live = {}
    for pi = 1, #compiled.protos do
      local instructions = compiled.protos[pi].code or {}
      for ci = 1, #instructions do
        local op = instructions[ci].op
        if op then live[op] = true end
      end
    end
    local selected = {}
    for oi = 1, #Compiler.OPS do
      local op = Compiler.OPS[oi]
      if live[op] then selected[#selected + 1] = op end
    end
    if #selected > 0 then activeOps = selected end
  end
  -- [VM9-ADAPTIVE] A flat alias budget gives obscure, rarely executed
  -- opcodes the same number of full Lua function bodies as hot arithmetic,
  -- call and table instructions. Reserve a real alias for every live opcode,
  -- then spend the remaining budget on the most frequently used semantics.
  -- No bytecode instruction is dropped; all existing slot/layout/operand
  -- checks and decoy auditing apply to the resulting heterogeneous table.
  local aliasCounts = {}
  local aliasesTotal = 0
  if opts.adaptiveAliases == true and encCount > 1 then
    local frequencies = {}
    for i = 1, #activeOps do
      frequencies[activeOps[i]] = 0
      aliasCounts[activeOps[i]] = 1
    end
    for pi = 1, #compiled.protos do
      for ci = 1, #(compiled.protos[pi].code or {}) do
        local op = compiled.protos[pi].code[ci].op
        if frequencies[op] ~= nil then
          frequencies[op] = frequencies[op] + 1
        end
      end
    end
    -- Compact: at most 1.5 full handler bodies per live opcode, versus
    -- the old 2. The extra aliases focus on hot semantics and each opcode
    -- can still receive up to six independent encodings. Deterministic
    -- tie-breaking avoids differences between Lua table iteration orders.
    local extraBudget = math.floor(#activeOps * 0.5)
    local aliasCap = math.min(VMGen.ENCODINGS_PER_OPCODE, 6)
    for _ = 1, extraBudget do
      local chosen, best = nil, -1
      for i = 1, #activeOps do
        local op = activeOps[i]
        local count, freq = aliasCounts[op], frequencies[op]
        if count < aliasCap and freq >= 2 then
          local value = freq / ((count + 1) * (count + 1))
          if value > best then
            best, chosen = value, op
          end
        end
      end
      if not chosen then break end
      aliasCounts[chosen] = aliasCounts[chosen] + 1
    end
  else
    for i = 1, #activeOps do aliasCounts[activeOps[i]] = encCount end
  end
  for i = 1, #activeOps do
    aliasesTotal = aliasesTotal + aliasCounts[activeOps[i]]
  end
  -- The handler table is a packed array: the hot lookup stays in the array
  -- part, which measured ~25% cheaper per dispatch than a sparse hash table on
  -- Luau. Bytecode still carries wide keys: every key is KEY_BASE + slot, so a
  -- plaintext dump shows a dense-looking block of large ids and the decoder
  -- turns one back into its slot with a single subtraction. Real encodings and
  -- decoys draw from one shuffled slot pool, so a dump still cannot separate
  -- them by key.
  local totalSlots = aliasesTotal + decoyCount
  if totalSlots < 1 then totalSlots = 1 end
  local keyBase = 35000 + rng(24000)
  local slotPool = {}
  for i = 1, totalSlots do slotPool[i] = i end
  shuffle(slotPool, rng)
  local slotNext = 1
  local slotOf = {}
  local function takeKey()
    local slot = slotPool[slotNext]
    slotNext = slotNext + 1
    local key = keyBase + slot
    slotOf[key] = slot
    return key
  end
  -- Every key gets its own ordering of the three register slots (2..4): a/b/c
  -- move between words, so a dumped alias of one opcode never shares a shape.
  -- The immediate d stays in slot 5: bytecode stores slots 2..4 as zigzag
  -- integers and slot 5 as a tagged field, so d cannot move without losing
  -- its float subtype. Its mask is sign-only (bias zero) because a bias on a
  -- float immediate would not subtract back exactly.
  local permutations = {
    { 2, 3, 4 }, { 2, 4, 3 }, { 3, 2, 4 },
    { 3, 4, 2 }, { 4, 2, 3 }, { 4, 3, 2 },
  }
  local opnum, opkeys, layouts, operandMasks, byKey = {}, {}, {}, {}, {}
  for i = 1, #activeOps do
    local name = activeOps[i]
    if not HANDLERS[name] then
      error("vmgen: missing handler for opcode '" .. name .. "'", 0)
    end
    shuffle(permutations, rng)
    local keys = {}
    local seenMask = {}
    for j = 1, aliasCounts[name] do
      local key = takeKey()
      -- Every slot of one opcode must carry a distinct sign/bias mask, or two
      -- encodings would decode identically and an alias count would lie. Draw
      -- until the triple is new for this opcode; the space (8 signs x 4095^3
      -- biases) makes this terminate in one or two draws.
      local mask, signature
      repeat
        mask = { signs = {}, biases = {} }
        for slot = 1, 3 do
          mask.signs[slot] = rng(2) == 1 and 1 or -1
          mask.biases[slot] = rng(4095)
        end
        -- Slot 4 is the immediate d: it stays in slot 5 with an identity mask
        -- because a float immediate (including -0.0) must round-trip exactly.
        mask.signs[4] = 1
        mask.biases[4] = 0
        -- Secondary per-instruction register mask. It is reversible in the
        -- VM and adds no external key: the goal is to defeat static alias-
        -- level operand templates, not claim cryptographic secrecy.
        -- Each multiplier is smaller than its prime modulus, so the
        -- prototype contribution cannot be annihilated modulo that value.
        if opts.pcOperandMask ~= false then
          -- Diversify the per-handler operand modulus rather than leaving an
          -- identical %127 normalization in every alias. All moduli are prime;
          -- 1 <= protoMul < mod means the prototype contribution cannot
          -- vanish modulo the selected prime (unlike former protoMul=127).
          local moduli = {127, 131, 137, 139, 149, 151, 157, 163,
            167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
            227, 229, 233, 239, 241, 251}
          local modulus = moduli[rng(#moduli)]
          mask.pc = { mul = 2 * rng(31) + 1, salt = rng(modulus) - 1,
            protoMul = 2 * rng(math.floor((modulus - 2) / 2)) + 1,
            mod = modulus }
        end
        signature = table.concat(mask.signs, ",") .. ":" ..
          table.concat(mask.biases, ",")
      until not seenMask[signature]
      seenMask[signature] = true
      -- Aliases draw from the six legal slot layouts round-robin after a fresh
      -- shuffle, so the immediate stays in slot 5 and every layout is
      -- represented before any repeats.
      local p = permutations[(j - 1) % #permutations + 1]
      keys[j] = key
      layouts[key] = { p[1], p[2], p[3], 5 }
      operandMasks[key] = mask
      byKey[key] = name
    end
    opnum[name], opkeys[name] = keys[1], keys
  end

  local decoys = {}
  for i = 1, decoyCount do decoys[i] = takeKey() end

  -- The keystream is drawn from its own stream (seed + 0x4B1D), inside
  -- encodeProtos' input, so changing the decoy count or the transport alphabet
  -- never reshuffles the instruction offsets.
  local keystream = buildKeystream(seed, #compiled.protos)
  local protos, instructionCount = encodeProtos(compiled.protos, opkeys, layouts,
    operandMasks, rng)

  -- Layer 11 support: string constants that are only ever read as values
  -- (LOADK) are safe to deviate at runtime; constants used as global or field
  -- names are not, because a corrupted name turns into a nil lookup.
  local safeStrings, poolRanges = {}, {}
  for pi = 1, #protos do
    local P = protos[pi]
    local loaded, keyed = {}, {}
    local nk = #P.k
    for i = 1, #P.c do
      local I = P.c[i]
      local name = byKey[I[1]]
      if name == "GETGLOBAL" or name == "SETGLOBAL" or
             name == "GETFIELD" or name == "SETFIELD" or name == "SELF" then
        keyed[I[5]] = true
      end
    end
    -- Deny-list, not allow-list: every string that is never used as a
    -- global or field name is a trap candidate. The layer 6 pool
    -- ciphertexts live in these tables, so a tripped session decrypts
    -- garbage instead of handing over URLs and API names.
    --
    -- A serialized pool is special-cased: rotating its header bytes (key
    -- length, plaintext length, blob length) breaks the decoder, so the
    -- deviation rotates only its per-entry ciphertext blobs. `poolRanges`
    -- carries those byte ranges; the pool index itself is dropped from the
    -- whole-string list.
    --
    -- Two kinds of entry stay clear of the rotation. Field names must, or a
    -- tripped run calls a nil member. Canary entries must too: they are
    -- decoys whose plaintext checksum is verified at load, and a rotated blob
    -- sets the decoder's tamper flag, after which every decoded value --
    -- field names included -- is shifted by one byte. A pool is always
    -- handled as a pool, even if no range survives, so its header is never
    -- rotated as a whole string.
    local fieldKeys = compiled.fieldKeys or {}
    local canaryKeys = compiled.canaryKeys or {}
    local function note(idx, s)
      local entries = Strings.poolBlobs(s)
      if not entries then return false end
      local ranges = {}
      for i = 1, #entries do
        local e = entries[i]
        if e.length > 0 and not fieldKeys[i] and not canaryKeys[i] then
          ranges[#ranges + 1] = e.start
          ranges[#ranges + 1] = e.stop
        end
      end
      if #ranges > 0 then
        poolRanges[pi] = poolRanges[pi] or {}
        local list = poolRanges[pi]
        list[#list + 1] = { index = idx, ranges = ranges }
      end
      return true
    end
    for idx = 1, nk do
      if type(P.k[idx]) == "string" and not keyed[idx] then
        loaded[idx] = true
      end
    end
    local list = {}
    for idx in pairs(loaded) do
      if not keyed[idx] and type(P.k[idx]) == "string" then
        list[#list + 1] = idx
      end
    end
    table.sort(list)
    local keep = {}
    for i = 1, #list do
      local idx = list[i]
      if not note(idx, P.k[idx]) then keep[#keep + 1] = idx end
    end
    safeStrings[pi] = keep
  end

  -- Handler keys are keyBase+slot, so the numbers stored in the code array
  -- never match the dense dispatch slots a dumper can read.
  return {
    seed = seed,
    activeOps = activeOps,
    decoyCount = decoyCount,
    encodings = encCount,
    adaptiveAliases = opts.adaptiveAliases == true,
    aliasCounts = aliasCounts,
    keyBase = keyBase,
    totalSlots = totalSlots,
    opnum = opnum,
    opkeys = opkeys,
    layouts = layouts,
    operandMasks = operandMasks,
    decoys = decoys,
    slots = slotOf,
    protos = protos,
    keystream = keystream,
    safeStrings = safeStrings,
    poolRanges = poolRanges,
    instructions = instructionCount,
    sourceInstructions = #compiled.protos,
  }
end

local NAME_KEYS = {
  "H", "P", "E", "X", "F", "W", "SU", "PK", "MM", "SEL", "ERR",
  "BW", "BN", "SHL", "SHR",
  -- Layer 9 decoder names.
  "SB", "SC", "SS", "SJ", "FL", "XT", "X8", "M32", "FN", "D", "SX", "RK",
  "ST", "K0", "POS", "RD", "ZZ", "DV", "LD", "TR", "KB", "O", "KS", "B", "HD",
  "MA", "MB", "UM", "K1", "DM",
  -- Layer 11 anti-debug names (ADH is the late-hook latch advanced by the
  -- integrity tick).
  "ADT", "ADB", "ADX", "ADS", "ADQ", "ADH",
  -- Layer 12 integrity names (IZ is the consolidated check state table).
  "IF", "IC", "IE", "IG", "II", "IP", "UB", "IT", "IZ",
  -- Header fields, appended last so earlier name slots stay stable.
  "CK", "PL", "KT",
  -- Per-build dispatch key transform.
  "OM", "OB",
  -- Layer 11 runtime-built library/field names.
  "ADG", "ADR", "AGH", "AGI", "AGW", "AGL", "AGF", "AGD",
  -- Layer 9 ChaCha20 decoder names.
  "XC", "XZ", "QT", "CB", "CW", "XB", "NB",
  -- SipHash round/entry points and the integrity bulk fallback.
  "SR", "SP", "IB",
  -- Executor-host flag for the existing probes.
  "ADE",
  -- Layer 11 debug-library integrity probes (upvalue + registry identity),
  -- plus the two extra debug entry points the fake-library probes read from
  -- the same capability snapshot.
  "ADU", "AGR", "ADLD", "ADTR", "ADSU",
  -- Hardcoded globals captured once at load. Every runtime helper reads the
  -- local copy, so swapping a library field after the chunk starts changes
  -- nothing inside the protected runtime. The function handles are copied by
  -- value too, not just the library tables, so a harness that swaps a field
  -- (e.g. `string.byte`) after load still cannot redirect integrity checks.
  "G1", "G2", "G3", "G4", "G9", "B1", "C1", "U1", "C2",
  -- Lazy constant pools (per-prototype sealed sections), blob transport.
  "G5", "KD", "BI", "BA", "B5", "B6", "KN", "LX",
  -- VM v2: per-build handler parameters, frame locals and proto field names.
  -- Every emitted handler and the dispatch loop body read these, so no two
  -- builds share a readable signature or a stable `S.top` / `p.c` anchor.
  "VI", "VR", "VK", "VU", "VS", "VPC", "VPI", "VPW", "VCW", "VNPC", "VZ",
  "VA",
  "A", "B", "C", "D",
  "STOP", "SRET", "SPROTO", "SARGS", "SAN", "PAA", "PVV", "PCC", "PKK", "PUU",
  -- Handler-table backup, the per-dispatch handler index and the handler value
  -- it resolves to. Every dispatch is compared against the private copy, so a
  -- swapped handler is replaced by the clean one before the next call.
  "HB", "VHI", "VHF", "G6",
  -- Environment chaff table (reads that only exist to blur an env log), the
  -- post-load primitive snapshot table the integrity tick re-checks, and the
  -- probe-shape counter that catches a removed anti-debug probe site.
  "CH", "IS", "ADN", "ASI",
  -- Layer 11 capability snapshot: the protected read helper, the raw host
  -- library handles and the plain snapshots the probe sites index. Appended
  -- last so earlier name slots stay stable across builds.
  "ADY", "ADB0", "ADS0",
  -- Layer 12 rotating audit + seal names: the handler key ring, the prototype
  -- length table, the read-only seal flag and the captured getmetatable.
  "IE", "IG", "IM", "G7",
  -- Layer 11 runtime debug self-test: the captured `debug.sethook`, and the
  -- rotating counter the integrity tick uses to re-check one library family
  -- per tick.
  "AGS", "ADZ",
  -- Per-prototype opcode keystream: the quadratic keystream table and the
  -- per-dispatch offset every word and handler operand is unwrapped with.
  "KSO", "KOF", "KRI", "KRM", "KRC", "KBR", "KBS", "KBP",
  -- Independent handler reference anchors sampled once, after handler creation.
  "IPIN",
  -- Separate mode list: packed/lazy prototypes keep their total length in Q.t.
  "IGM",
  -- Independent per-prototype opcode mixer metadata anchor.
  "KSR", "KSH",
  -- Independently committed prototype closure descriptors and signature.
  "PMA", "PMH",
  -- Host capability marker; only guards non-portable environment heuristics.
  "RBH",
  -- Build-local frame key for the current prototype index. Operand aliases
  -- now use both PC and prototype identity, including in nested closures.
  "SPID",
  -- Per-frame cached parameters for the discontinuous opcode mixer.
  "KW", "KY",
  -- One-shot reporter, shared by VM integrity and bytecode decode errors.
  "AL",

}

-- Environment chaff: a sandbox or devirt harness that logs global reads cannot
-- tell these apart from the few globals the runtime actually depends on, so
-- pruning the log down to "the reads that matter" stops being mechanical.
local CHAFF_GLOBALS = {
  "game", "workspace", "script", "Instance", "Vector3", "CFrame", "task",
  "tick", "wait", "spawn", "print", "warn", "require", "Players",
  "RunService", "UserInputService", "ReplicatedStorage", "HttpService",
  "CollectionService", "Drawing", "getgenv", "getrenv", "getreg",
  "hookfunction", "hookmetamethod", "getrawmetatable", "setreadonly",
  "islclosure", "getloadedmodules", "getconnections", "checkcaller",
  "newcclosure", "clonefunction", "secure_call", "request", "http_request",
  "loadstring", "load", "getfenv", "setfenv", "getmetatable", "rawget",
  "rawset", "xpcall", "tostring", "tonumber", "next", "unpack", "io",
  "select", "string", "table", "debug", "coroutine", "os", "math", "utf8",
  "bit32",
}
local CHAFF_FIELDS = {
  { "debug", "gethook" }, { "debug", "getinfo" }, { "debug", "getupvalue" },
  { "debug", "sethook" }, { "debug", "setupvalue" }, { "debug", "getregistry" },
  { "string", "dump" }, { "string", "byte" }, { "string", "sub" },
  { "string", "find" }, { "table", "concat" }, { "table", "unpack" },
  { "os", "clock" }, { "coroutine", "wrap" }, { "math", "random" },
  { "utf8", "char" }, { "io", "open" }, { "string", "rep" },
}

-- rng() values may carry the float subtype (Fengari math.floor keeps it) and
-- `%x` rejects integral floats, so digits are picked by hand.
local HEXDIGITS = {
  "0", "1", "2", "3", "4", "5", "6", "7",
  "8", "9", "a", "b", "c", "d", "e", "f",
}

local function hex4(n)
  n = math.floor(tonumber(n) or 0) % 65536
  local out = {}
  for i = 4, 1, -1 do
    local digit = n % 16
    out[i] = HEXDIGITS[digit + 1]
    n = (n - digit) / 16
  end
  return table.concat(out)
end

-- Decoder error text is assembled at runtime from byte codes, so the stage
-- names ("checksum", "bad key", "block checksum") never appear as words.
local function codes(text)
  local out = {}
  for i = 1, #text do out[i] = string.byte(text, i) end
  return table.concat(out, ",")
end

local LOWER = "abcdefghijklmnopqrstuvwxyz"
local ALNUM = "abcdefghijklmnopqrstuvwxyz0123456789"
local ALNUM_UP = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
local NAME_PREFIX = { "l_", "v_", "q_", "x_", "__" }

local function pick(rng, charset, count)
  local out = {}
  for i = 1, count do
    local k = rng(#charset)
    out[i] = charset:sub(k, k)
  end
  return table.concat(out)
end

-- Runtime identifiers are drawn from five shape families with the same seed
-- RNG. A file that always spells `_0x` + eight hex digits is trivial to
-- fingerprint (and was the visible tell a deobf bot used to pick its target
-- profile), so each build now mixes styles and lengths instead.
local function styledName(rng)
  local style = rng(5)
  if style == 1 then
    return "_0x" .. hex4(rng(65536) - 1) .. hex4(rng(65536) - 1)
  elseif style == 2 then
    return "_" .. pick(rng, ALNUM, 9 + rng(8))
  elseif style == 3 then
    local first = rng(#LOWER)
    return LOWER:sub(first, first) .. pick(rng, ALNUM_UP, 10 + rng(8))
  elseif style == 4 then
    return "__" .. pick(rng, "0123456789abcdef", 8 + rng(6))
  end
  local p = rng(#NAME_PREFIX)
  return NAME_PREFIX[p] .. pick(rng, ALNUM, 8 + rng(8))
end

-- A generated identifier must never spell an opcode mnemonic. The names are
-- printable text inside the chunk and two of the five style families mix
-- uppercase letters, so an unlucky draw could put "LT" or "EQ" in the file and
-- hand a scanner a free hint. Reject and redraw instead of trusting luck.
local MNEMONIC = {}
for i = 1, #Compiler.OPS do MNEMONIC[Compiler.OPS[i]] = true end
local function mnemonicFree(name)
  for word in pairs(MNEMONIC) do
    if name:find(word, 1, true) then return false end
  end
  return true
end

local function makeNames(seed, compactNames)
  local rng = makeRng(seed + 0x51ED)
  local names, used = {}, {}
  for i = 1, #NAME_KEYS do
    local name
    repeat
      -- [SIZE-NAMES] Short, per-build names save bytes at every VM use site.
      -- Keep the full-length polymorphic style in standard-size mode.
      if compactNames then
        name = "_" .. pick(rng, ALNUM, 4 + rng(2))
      else
        name = styledName(rng)
      end
    until not used[name] and mnemonicFree(name)
    used[name] = true
    names[NAME_KEYS[i]] = name
  end
  -- Hot-path names (six handler parameters, four decoded operands, the five
  -- frame fields and the five prototype fields) are short: they repeat 640
  -- times in the handler table, so long styled names would bloat the file
  -- without adding entropy. They are still drawn per build, never keywords
  -- (the leading underscore makes that impossible) and never collide with a
  -- field or library identifier used by a handler body.
  local shortKeys = {
    "VI", "VR", "VK", "VU", "VS", "VPC", "KOF",
    "A", "B", "C", "D",
    "STOP", "SRET", "SPROTO", "SARGS", "SAN",
    "PAA", "PVV", "PCC", "PKK", "PUU",
  }
  for i = 1, #shortKeys do
    local key = shortKeys[i]
    local name
    repeat
      name = "_" .. pick(rng, LOWER, 2 + rng(2))
    until not used[name] and mnemonicFree(name)
    used[name] = true
    names[key] = name
  end
  return names
end

local function substitute(code, names)
  return (code:gsub("%$([A-Z]+)", function(key)
    return names[key] or key
  end))
end

-- Handler bodies are written against a fixed vocabulary: a,b,c,d (decoded
-- operands), pc, the six dispatch arguments and a handful of scratch locals.
-- Every build renames all of them, so two builds of the same source share no
-- readable body skeleton at all. Field accesses (`S.top`, `p.v`, `Q.u`) go
-- through a second map keyed on the identifier after a dot, and string
-- literals are copied verbatim.
local VAR_TOKENS = {
  "a", "b", "c", "d", "pc", "R", "K", "U", "S", "I",
  "j", "u", "v", "w", "z", "t", "k", "f", "Q", "V", "e", "q", "G", "st", "lm",
}

local function makeBodyMaps(names, seed)
  local rng = makeRng((seed or 0) + 0x2B7D)
  local used = {}
  for _, value in pairs(names) do used[value] = true end
  local var = {}
  for i = 1, #VAR_TOKENS do
    local name
    repeat name = "_" .. pick(rng, LOWER, 2 + rng(2)) until not used[name]
    used[name] = true
    var[VAR_TOKENS[i]] = name
  end
  -- The dispatch arguments and decoded operands are shared with the emitted
  -- loop and the tests, so they come from the name table instead.
  var.a, var.b, var.c, var.d = names.A, names.B, names.C, names.D
  var.pc, var.R, var.K, var.U, var.S, var.I =
    names.VPC, names.VR, names.VK, names.VU, names.VS, names.VI
  local field = {
    top = names.STOP, ret = names.SRET, p = names.SPROTO,
    ar = names.SARGS, an = names.SAN,
    a = names.PAA, v = names.PVV, c = names.PCC, k = names.PKK, u = names.PUU,
  }
  return var, field
end

local function renameBody(code, var, field)
  local out, i, n = {}, 1, #code
  while i <= n do
    local c = code:sub(i, i)
    if c == '"' or c == "'" then
      local s = i
      local q = c
      i = i + 1
      while i <= n do
        local d = code:sub(i, i)
        if d == "\\" then i = i + 2
        elseif d == q then i = i + 1 break
        else i = i + 1 end
      end
      out[#out + 1] = code:sub(s, i - 1)
    elseif c:match("[%a_]") then
      local s = i
      repeat i = i + 1 until i > n or not code:sub(i, i):match("[%w_]")
      local word = code:sub(s, i - 1)
      local prev = s > 1 and code:sub(s - 1, s - 1) or ""
      local mapped
      -- A single dot means field access; `..` is concatenation and the token
      -- after it is a normal expression, not a field name.
      if prev == "." and not (s > 2 and code:sub(s - 2, s - 2) == ".") then
        mapped = field[word]
      else
        mapped = var[word]
      end
      out[#out + 1] = mapped or word
    else
      out[#out + 1] = c
      i = i + 1
    end
  end
  return table.concat(out)
end

-- Emit pre-split (symbol-complete) chunks as a table constructor. A `..` chain
-- is parsed as a right-nested expression and Lua refuses chunks past ~200
-- syntax levels, which large payloads would hit; a flat constructor joined at
-- runtime by table.concat stays parseable at any size.
local function chunkParts(add, name, parts, join, quote)
  local quotePart = quote or quoteRaw
  if #parts == 1 then
    add("local " .. name .. "=" .. quotePart(parts[1]))
    return
  end
  local tbl = name .. "t"
  add("local " .. tbl .. "={")
  for i = 1, #parts do
    add(quotePart(parts[i]) .. (i < #parts and "," or "}"))
  end
  add("local " .. name .. "=" .. join .. "(" .. tbl .. ")")
end

-- SipHash round as emitted source: the 64-bit state is four (hi, lo) 32-bit
-- word pairs in a flat table, so no step needs a 64-bit integer and the code
-- behaves the same on 5.1..5.4, Luau and Fengari.
local function sipRoundSource(xz)
  local M = "4294967296"
  local out = {
    "local a,b,c,d,e,f,g,h=v[1],v[2],v[3],v[4],v[5],v[6],v[7],v[8]",
    "local lo,hi,cr,nh,nl",
  }
  local function add(xh, xl, yh, yl)
    out[#out + 1] = "lo=" .. xl .. "+" .. yl .. " cr=0 if lo>=" .. M ..
      " then lo=lo-" .. M .. " cr=1 end"
    out[#out + 1] = "hi=" .. xh .. "+" .. yh .. "+cr if hi>=" .. M ..
      " then hi=hi-" .. M .. " end"
    out[#out + 1] = xh .. "," .. xl .. "=hi,lo"
  end
  local function rot(xh, xl, mul, div)
    out[#out + 1] = "nh=(" .. xh .. "*" .. mul .. ")%" .. M .. "+(" .. xl ..
      "-" .. xl .. "%" .. div .. ")/" .. div
    out[#out + 1] = "nl=(" .. xl .. "*" .. mul .. ")%" .. M .. "+(" .. xh ..
      "-" .. xh .. "%" .. div .. ")/" .. div
  end
  local function mix(xh, xl, yh, yl)
    out[#out + 1] = xh .. "," .. xl .. "=" .. xz .. "(" .. xh .. "," .. yh ..
      ")," .. xz .. "(" .. xl .. "," .. yl .. ")"
  end
  add("a", "b", "c", "d")
  rot("c", "d", 8192, 524288)
  out[#out + 1] = "c,d=nh,nl"
  mix("c", "d", "a", "b")
  out[#out + 1] = "a,b=b,a"
  add("e", "f", "g", "h")
  rot("g", "h", 65536, 65536)
  out[#out + 1] = "g,h=nh,nl"
  mix("g", "h", "e", "f")
  add("a", "b", "g", "h")
  rot("g", "h", 2097152, 2048)
  out[#out + 1] = "g,h=nh,nl"
  mix("g", "h", "a", "b")
  add("e", "f", "c", "d")
  rot("c", "d", 131072, 32768)
  out[#out + 1] = "c,d=nh,nl"
  mix("c", "d", "e", "f")
  out[#out + 1] = "e,f=f,e"
  out[#out + 1] = "v[1],v[2],v[3],v[4],v[5],v[6],v[7],v[8]=a,b,c,d,e,f,g,h"
  return table.concat(out, " ")
end

-- 16-bit halves keep the eight SipHash IV words out of the file as plain
-- 32-bit literals, the same way the ChaCha sigma constants are emitted.
local function sipIVSource()
  local iv = { 0x736f6d65, 0x70736575, 0x646f7261, 0x6e646f6d,
    0x6c796765, 0x6e657261, 0x74656462, 0x79746573 }
  local out = {}
  for i = 1, #iv do
    out[i] = math.floor(iv[i] / 65536) * 65536.0 + iv[i] % 65536
  end
  return out
end

-- Layer 9: emit the decoder for a packed payload instead of a prototype table
-- literal. Mirrors src/bytecode.lua helper for helper.
local function emitPacked(add, n, payload, rng, ig, keyBase, totalSlots)
  local SB, SC, SS, SJ, FL = n.SB, n.SC, n.SS, n.SJ, n.FL
  local XT, X8, M32, FN = n.XT, n.X8, n.M32, n.FN
  local D, K0 = n.D, n.K0
  local POS, RD, ZZ, DV = n.POS, n.RD, n.ZZ, n.DV
  local LD, TR = n.LD, n.TR
  local KB, O, B, HD = n.KB, n.O, n.B, n.HD
  local XC, XZ, QT, CB, CW = n.XC, n.XZ, n.QT, n.CB, n.CW
  local XB, NB = n.XB, n.NB
  local K1 = n.K1
  local DM = n.DM
  local CK, PL, KT = n.CK, n.PL, n.KT
  local RA, KD = n.G5, n.KD
  local BI, BA, B5, B6 = n.BI, n.BA, n.B5, n.B6
  -- Prototype field names are build-local too (see VMGen.emit), so the loader
  -- and the handler table agree on `a/v/c/k/u` without ever spelling them.
  local FA, FV, FC, FK, FU = n.PAA, n.PVV, n.PCC, n.PKK, n.PUU
  -- The prototype field names are per-build identifiers; a table constructor
  -- needs them as string keys, and a field read uses the dot form.
  local function fk(s) return "[\"" .. s .. "\"]" end

  -- String primitives are reached through a per-build random literal; byte/sub
  -- method names are computed from char codes so no readable .byte/.sub token or
  -- constant "\0" anchor survives in the shipped decoder.
  local sl = '("\\' .. string.format("%03d", rng(255)) .. '")'
  add("local " .. SC .. "=" .. sl .. ".char")
  add("local " .. SB .. "=" .. sl .. "[" .. SC .. "(98,121,116,101)]")
  add("local " .. SS .. "=" .. sl .. "[" .. SC .. "(115,117,98)]")
  -- Table primitives come from the env table captured above, not from a fresh
  -- global lookup, so a host that wraps or shadows the `table` global after
  -- load cannot break the decoder. The field names are char-coded like the
  -- string ones so no `.concat` / `.remove` token survives either. A nil table
  -- library is fatal anyway: the decoder cannot exist without it.
  add("local " .. SJ .. "=" .. n.G2 .. "[" .. SC .. "(99,111,110,99,97,116)]")
  add("local " .. TR .. "=" .. n.G2 .. "[" .. SC .. "(114,101,109,111,118,101)]")
  add("local " .. FL .. "=" .. n.MM .. ".floor")

  add("local " .. XT .. "={}")
  add("for a=0,15 do for b=0,15 do local z,pw,x,y=0,1,a,b " ..
    "for q=1,4 do local xa=x%2 local yb=y%2 if xa~=yb then z=z+pw end " ..
    "x=(x-xa)/2 y=(y-yb)/2 pw=pw*2 end " .. XT .. "[a*16+b]=z end end")
  -- Native byte XOR: `bit32` exists on Luau (every Roblox executor), so the
  -- payload body and the self-modifying block chain call it directly instead
  -- of walking a table per byte. The nibble table stays as the fallback for
  -- hosts without bit ops (5.1, LuaJIT). Library names stay char-coded.
  add("local " .. X8 .. "," .. XB)
  add("local " .. NB .. "=" .. n.E .. "[" .. SC .. "(98,105,116,51,50)]")
  add("local bx=" .. NB .. " and " .. NB .. "[" .. SC .. "(98,120,111,114)]")
  add("if " .. n.G4 .. "(bx)==\"function\" then " .. NB .. "=bx else " ..
    NB .. "=nil end")
  add("local function " .. M32 .. "(a,b) local a0=a%65536 " ..
    "local a1=(a-a0)/65536 local b0=b%65536 local b1=(b-b0)/65536 " ..
    "return ((a0+0.0)*b0+((a0*b1+a1*b0)%65536)*65536)%4294967296 end")
  add("local function " .. FN .. "(s) local h=2166136261 " ..
    "for i=1,#s do local b=" .. SB .. "(s,i) h=" .. M32 .. "(h-h%256+" ..
    X8 .. "(h%256,b),16777619) end return h end")

  -- Byte XOR table and 32-bit XOR: ChaCha, SipHash and the block keystream all
  -- need them before the payload is touched. With native bit ops the table is
  -- skipped entirely; X8/XB/XZ all point at `bxor`.
  add("local " .. XC .. "={}")
  add("if not " .. NB .. " then for a=0,255 do local h=a-a%16 local l=(a%16)*16 " ..
    "local bs=a*256 for b=0,255 do " .. XC .. "[bs+b]=" .. XT .. "[h+" ..
    FL .. "((b-b%16)/16)]*16+" .. XT .. "[l+b%16] end end end")
  add("if " .. NB .. " then " .. XB .. "=function(a,b) return " ..
    NB .. "(a,b) end else " .. XB .. "=function(a,b) return " .. XC ..
    "[a*256+b] end end")
  add(X8 .. "=" .. XB)
  add("local " .. XZ)
  add("if " .. NB .. " then " .. XZ ..
    "=function(a,b) return " .. NB .. "(a,b) end else " .. XZ ..
    "=function(a,b) local a0=a%256 local b0=b%256 " ..
    "local r=" .. XC .. "[a0*256+b0] a=(a-a0)/256 b=(b-b0)/256 " ..
    "a0=a%256 b0=b%256 r=r+" .. XC .. "[a0*256+b0]*256.0 " ..
    "a=(a-a0)/256 b=(b-b0)/256 a0=a%256 b0=b%256 r=r+" ..
    XC .. "[a0*256+b0]*65536.0 a=(a-a0)/256 b=(b-b0)/256 " ..
    "return r+" .. XC .. "[a*256+b]*16777216.0 end end")

  -- SipHash-2-4 retains the folded result for existing users and also returns
  -- the raw high/low words for the header+ciphertext integrity trailer.
  local SR, SP = n.SR, n.SP
  add("local function " .. SR .. "(v) " .. sipRoundSource(XZ) .. " end")
  local iv = sipIVSource()
  add("local function " .. SP .. "(s,p,q) local a=p%4294967296 " ..
    "local b=(" .. M32 .. "(a,2246822507)+3266489909)%4294967296 " ..
    "local c=q%4294967296 " ..
    "local d=(" .. M32 .. "(c,2507323147)+1515870810)%4294967296 " ..
    "local v={" .. XZ .. "(a," .. iv[1] .. ")," .. XZ .. "(b," .. iv[2] ..
    ")," .. XZ .. "(c," .. iv[3] .. ")," .. XZ .. "(d," .. iv[4] .. ")," ..
    XZ .. "(a," .. iv[5] .. ")," .. XZ .. "(b," .. iv[6] .. ")," ..
    XZ .. "(c," .. iv[7] .. ")," .. XZ .. "(d," .. iv[8] .. ")}")
  add("local n=#s local last=n-n%8 local i=1")
  add("while i<=last do local b0,b1,b2,b3=" .. SB .. "(s,i,i+3) " ..
    "local c0,c1,c2,c3=" .. SB .. "(s,i+4,i+7) " ..
    "local ml=b0+b1*256+b2*65536+b3*16777216.0 " ..
    "local mh=c0+c1*256+c2*65536+c3*16777216.0 " ..
    "v[7],v[8]=" .. XZ .. "(v[7],mh)," .. XZ .. "(v[8],ml) " ..
    SR .. "(v) " .. SR .. "(v) " ..
    "v[1],v[2]=" .. XZ .. "(v[1],mh)," .. XZ .. "(v[2],ml) i=i+8 end")
  add("local ml=0 local mh=(n%256)*16777216.0")
  add("if n%8>0 then local p0=last+1 local b0,b1,b2,b3=" .. SB ..
    "(s,p0,p0+3) local c0,c1,c2=" .. SB .. "(s,p0+4,p0+6) " ..
    "ml=b0+(b1 or 0)*256+(b2 or 0)*65536+(b3 or 0)*16777216.0 " ..
    "mh=mh+(c0 or 0)+(c1 or 0)*256+(c2 or 0)*65536 end")
  add("v[7],v[8]=" .. XZ .. "(v[7],mh)," .. XZ .. "(v[8],ml) " ..
    SR .. "(v) " .. SR .. "(v) " ..
    "v[1],v[2]=" .. XZ .. "(v[1],mh)," .. XZ .. "(v[2],ml)")
  add("v[6]=" .. XZ .. "(v[6],255) " .. SR .. "(v) " .. SR .. "(v) " ..
    SR .. "(v) " .. SR .. "(v)")
  add("local hi=" .. XZ .. "(" .. XZ .. "(v[1],v[3])," .. XZ .. "(v[5],v[7])) " ..
    "local lo=" .. XZ .. "(" .. XZ .. "(v[2],v[4])," .. XZ .. "(v[6],v[8])) " ..
    "return " .. XZ .. "(hi,lo),hi,lo end")

  if ig then
    local lines = Integrity.prologue(n, ig, SP)
    for i = 1, #lines do add(lines[i]) end
  end

  -- Key material: the literal key never appears in the file.
  local p1 = rng(67108864) - 1
  if p1 < 1 then p1 = 1 end
  local p2 = rng(67108864) - 1
  if p2 < 1 then p2 = 1 end
  local key = math.floor(tonumber(payload.key) or 0) % 4294967296
  local p3 = (key - p1 * p2) % 4294967296
  if p3 < 0 then p3 = p3 + 4294967296 end
  add("local " .. K0 .. "=(" .. p1 .. "*" .. p2 .. "+" .. p3 ..
    ")%4294967296")

  -- The blob is carried as a per-build symbol salad: all 91 printable ASCII
  -- symbols, ordered by the build seed, four base-91 digits per three payload
  -- bytes. The artifact stays 7-bit clean end to end while sharing no
  -- alphabet or digit grouping with base64. The decoder builds its map from
  -- the shipped alphabet; `=` is not a symbol, so a pad reads as nil and the
  -- group's byte count follows from which of the last two slots are nil.
  local chars = symbolAlphabet(rng)
  add("local " .. BA .. "={")
  for i = 1, #chars do
    add(quoteRaw(chars[i]) .. (i < #chars and "," or "}"))
  end
  add("local " .. BI .. "={} for i=1,#" .. BA .. " do " .. BI ..
    "[" .. BA .. "[i]]=i-1 end " .. BA .. "=nil")
  -- [TRANSPORT-CANONICAL] The base-91 transport must be a unique encoding
  -- of the payload. Earlier versions silently skipped groups with an invalid
  -- first symbol, so an analyst could append junk groups without changing the
  -- decoded bytecode (and without any integrity alarm). Reject invalid glyphs,
  -- non-terminal padding and out-of-range groups BEFORE the binary checksum.
  -- The canonical check is fused into the existing decoding pass; no extra
  -- full-payload scan, no extra output materialization.
  local badTransport = n.AL .. "() " .. n.ERR .. "(" .. DM .. "(" .. codes("bytecode: invalid transport") .. "))"
  add("local " .. B6 .. "=function(s) local o={} local p=1 local n=#s " ..
    "if n%4~=0 then " .. badTransport .. " end " ..
    "while p<=n do " ..
    "local a=" .. BI .. "[" .. SS .. "(s,p,p)] local b=" .. BI ..
    "[" .. SS .. "(s,p+1,p+1)] " ..
    "local e=" .. SS .. "(s,p+2,p+2) local f=" .. SS .. "(s,p+3,p+3) " ..
    "local c=" .. BI .. "[e] local d=" .. BI .. "[f] p=p+4 " ..
    "if a==nil or b==nil or (c==nil and (e~='=' or f~='=' or p<=n)) " ..
    "or (c~=nil and d==nil and (f~='=' or p<=n)) then " .. badTransport .. " end " ..
    "if c==nil then local v=a*91+b if v>=256 then " .. badTransport ..
    " end o[#o+1]=" .. SC .. "(v) " ..
    "elseif d==nil then local v=a*8281+b*91+c if v>=65536 then " ..
    badTransport .. " end o[#o+1]=" .. SC .. "(" .. FL ..
    "(v/256)%256,v%256) else " ..
    "local v=a*753571+b*8281+c*91+d if v>=16777216 then " ..
    badTransport .. " end o[#o+1]=" .. SC .. "(" .. FL ..
    "(v/65536)%256," .. FL .. "(v/256)%256,v%256) end end " ..
    "return " .. SJ .. "(o) end")
  local sectionText
  if #payload.blob == 0 then
    sectionText = "local " .. B5 .. "=\"\""
    add(sectionText)
  else
    local saladParts = saladEncode(payload.blob, chars, 8192)
    chunkParts(add, B5, saladParts, SJ, quoteSymbols)
    local quoted = {}
    for i = 1, #saladParts do quoted[i] = quoteSymbols(saladParts[i]) end
    if #saladParts == 1 then
      sectionText = "local " .. B5 .. "=" .. quoted[1]
    else
      sectionText = "local " .. B5 .. "t={ " ..
        table.concat(quoted, ", ") .. "} local " .. B5 .. "=" .. SJ ..
        "(" .. B5 .. "t)"
    end
  end
  add("local " .. D .. "=" .. B6 .. "(" .. B5 .. ") " .. B5 .. "=nil")
  if ig then add(Integrity.blobCheck(n, ig, payload.blob)) end

  local function reject(condition, reason)
    add("if " .. condition .. " then " .. n.AL .. "() " .. n.ERR .. "(" .. DM .. "(" ..
      codes("bytecode: " .. reason) .. ")) end")
  end
  add("if #" .. D .. "<24 then " .. n.AL .. "() " .. n.ERR ..
    "(" .. DM .. "(" .. codes("bytecode: truncated payload") .. ")) end")
  add("local " .. HD .. "=" .. SS .. "(" .. D .. ",1,16)")
  add("local b1,b2,b3,b4=" .. SB .. "(" .. HD .. ",1,4)")
  add("local b5,b6,b7,b8=" .. SB .. "(" .. HD .. ",5,8)")
  add("local b9,b10,b11,b12=" .. SB .. "(" .. HD .. ",9,12)")
  -- Header fields are built in the float domain (`*256.0`): a byte sum stays
  -- an integer on 5.3+, and Fengari compares mixed int/float values above
  -- 2^31 incorrectly, which would reject a valid payload.
  add("local " .. CK .. "=b1+b2*256.0+b3*65536.0+b4*16777216.0")
  add("local " .. PL .. "=b5+b6*256.0+b7*65536.0+b8*16777216.0")
  add("local " .. KT .. "=b9+b10*256.0+b11*65536.0+b12*16777216.0")
  add("local m0,m1=" .. KT .. "/16777216%256," .. KT .. "%256")
  add("local " .. B .. "=" .. SS .. "(" .. D .. ",17,-9)")
  add("if " .. FN .. "(" .. B .. ")~=" .. CK .. " then " .. n.AL .. "() " .. n.ERR ..
    "(" .. DM .. "(" .. codes("bytecode: checksum mismatch") .. ")) end")
  add("local " .. KB .. "=" .. SC .. "(" .. K0 .. "%256," .. FL ..
    "(" .. K0 .. "/256)%256," .. FL .. "(" .. K0 .. "/65536)%256," .. FL ..
    "(" .. K0 .. "/16777216)%256)")
  add("if " .. n.SP .. "(" .. KB .. "," .. K0 .. ",(" .. M32 .. "(" .. K0 ..
    ",2654435761)+1013904223)%4294967296)~=" .. KT .. " then " .. n.AL .. "() " .. n.ERR ..
    "(" .. DM .. "(" .. codes("bytecode: bad key") .. ")) end")
  add("local m2=" .. FL .. "(" .. KT .. "/256)%256 local m3=" .. FL ..
    "(" .. KT .. "/65536)%256")
  add("if " .. FL .. "(m0)~=" .. SB .. "(" .. HD .. ",13) or m1~=" ..
    SB .. "(" .. HD .. ",14) or " .. SB .. "(" .. HD .. ",15)~=m2 or " ..
    SB .. "(" .. HD .. ",16)~=m3 then " .. n.AL .. "() " .. n.ERR ..
    "(" .. DM .. "(" .. codes("bytecode: unsupported format") .. ")) end")

  add("do local _,hi,lo=" .. SP .. "(" .. SS .. "(" .. D .. ",1,-9)," ..
    K0 .. ",(" .. K0 .. "+1096111176)%4294967296) local tag=" .. SC ..
    "(lo%256," .. FL .. "(lo/256)%256," .. FL .. "(lo/65536)%256," .. FL ..
    "(lo/16777216)%256,hi%256," .. FL .. "(hi/256)%256," .. FL ..
    "(hi/65536)%256," .. FL .. "(hi/16777216)%256)")
  reject("tag~=" .. SS .. "(" .. D .. ",-8)", "authentication mismatch")
  add("end")
  add("local n=#" .. B)
  reject("n==0 or n%64~=0 or " .. PL .. "<1 or " .. PL .. ">n or n-" ..
    PL .. ">=64", "invalid length")
  -- The cipher session key derives from the build key and payload length.
  add("local " .. K1 .. "=(" .. K0 ..
    "+(n%65536)*2654435769+1515870810)%4294967296")
  -- ChaCha20 (RFC 8439) counter mode, arithmetic only: no bit operators and no
  -- 64-bit values, so the same bytes decrypt on 5.1..5.4 and Luau.
  add("local function " .. QT .. "(s,i,j,k,l) local x,y,z,w=s[i],s[j],s[k],s[l] " ..
    "x=x+y if x>=4294967296 then x=x-4294967296 end " ..
    "w=" .. XZ .. "(w,x) w=(w*65536)%4294967296+(w-w%65536)/65536 " ..
    "z=z+w if z>=4294967296 then z=z-4294967296 end " ..
    "y=" .. XZ .. "(y,z) y=(y*4096)%4294967296+(y-y%1048576)/1048576 " ..
    "x=x+y if x>=4294967296 then x=x-4294967296 end " ..
    "w=" .. XZ .. "(w,x) w=(w*256)%4294967296+(w-w%16777216)/16777216 " ..
    "z=z+w if z>=4294967296 then z=z-4294967296 end " ..
    "y=" .. XZ .. "(y,z) y=(y*128)%4294967296+(y-y%33554432)/33554432 " ..
    "s[i],s[j],s[k],s[l]=x,y,z,w end")
  add("local function " .. CB .. "(st) local w={} for i=1,16 do w[i]=st[i] end " ..
    "for r=1,10 do " ..
    QT .. "(w,1,5,9,13) " .. QT .. "(w,2,6,10,14) " ..
    QT .. "(w,3,7,11,15) " .. QT .. "(w,4,8,12,16) " ..
    QT .. "(w,1,6,11,16) " .. QT .. "(w,2,7,12,13) " ..
    QT .. "(w,3,8,9,14) " .. QT .. "(w,4,5,10,15) end " ..
    "for i=1,16 do local v=w[i]+st[i] if v>=4294967296 then " ..
    "v=v-4294967296 end w[i]=v end return w end")
  -- Key words: 8 words expanded from the session key by the LCG; the three
  -- nonce words bind the keystream to the session-key tag, true length and
  -- padded length.
  add("local kt=" .. n.SP .. "(" .. SC .. "(" .. K1 .. "%256," .. FL ..
    "(" .. K1 .. "/256)%256," .. FL .. "(" .. K1 .. "/65536)%256," .. FL ..
    "(" .. K1 .. "/16777216)%256)," .. K1 .. ",(" .. M32 .. "(" .. K1 ..
    ",2654435761)+1013904223)%4294967296) local pn=" .. FL .. "(" .. PL .. ")")
  -- Constant words are emitted as 16-bit halves so no recognisable 32-bit
  -- literal appears in the file.
  add("local " .. CW .. "={24944*65536.0+30821,13088*65536.0+25710," ..
    "31074*65536.0+11570,27424*65536.0+25972} " ..
    "local s=(" .. K1 .. "+1515870810)%4294967296")
  add("for i=1,8 do s=(s*1664525+1013904223)%4294967296 " ..
    CW .. "[4+i]=s end")
  add(CW .. "[13]=0 " .. CW .. "[14]=(kt+" .. M32 .. "(pn,2654435761))%4294967296 " ..
    CW .. "[15]=(" .. M32 .. "(kt,2246822519)+n)%4294967296 " ..
    CW .. "[16]=(pn+" .. M32 .. "(n,3266489917))%4294967296")
  add("local " .. O .. "={} local blk=0 local j=1")
  add("while j<=n do")
  add(CW .. "[13]=blk local w=" .. CB .. "(" .. CW .. ")")
  add("for i=1,16 do local q=w[i] local q0=q%256 " ..
    "local q1=(q-q0)/256%256 local q2=(q-q0-q1*256)/65536%256 " ..
    "local q3=(q-q0-q1*256-q2*65536)/16777216 " ..
    "local b0,b1,b2,b3=" .. SB .. "(" .. B .. ",j,j+3) " ..
    O .. "[#" .. O .. "+1]=" .. SC .. "(" .. XB .. "(b0,q0)," ..
    XB .. "(b1,q1)," .. XB .. "(b2,q2)," .. XB .. "(b3,q3)) " ..
    "j=j+4 end")
  add("blk=blk+1")
  add("end")
  add(O .. "=" .. SJ .. "(" .. O .. ") if #" .. O .. ">" .. PL .. " then " .. O ..
    "=" .. SS .. "(" .. O .. ",1," .. PL .. ") end")

  add("local pos=1")
  add("local function " .. POS .. "(s,p,ln)")
  reject("ln>#s-p+1", "section bounds")
  add("return " .. SS .. "(s,p,p+ln-1),p+ln end")
  add("local " .. RD .. "=function(s,p) local v=0 local m=1.0 for i=1,8 do " ..
    "local b=" .. SB .. "(s,p)")
  reject("not b", "section bounds")
  reject("(i==8 and b>15) or (i>1 and b==0)", "varint range or encoding")
  add("p=p+1 v=v+(b%128)*m if b<128 then return " .. FL .. "(v),p end m=m*128 end " ..
    n.AL .. "() " .. n.ERR .. "(" .. DM .. "(" .. codes("bytecode: varint range") .. ")) end")
  -- floor keeps the integer subtype on 5.3/5.4 (plain / yields a float and
  -- changes tostring output for integer operands).
  add("local function " .. ZZ .. "(v) if v%2==1 then return -"
    .. n.MM .. ".floor((v+1)/2) else return " .. n.MM ..
    ".floor(v/2) end end")
  -- Operand d is tagged: 0 = integer varint, 3/5/6/7 = float immediate.
  add("local function " .. DV .. "(s,p) local t=" .. SB .. "(s,p) p=p+1")
  add("if t==0 then local v; v,p=" .. RD .. "(s,p) return " ..
    ZZ .. "(v),p end")
  add("if t==3 then local ln; ln,p=" .. RD .. "(s,p) local x; x,p=" .. POS ..
    "(s,p,ln) x=tonumber(x)")
  reject("not x or x~=x or x==1/0 or x==-1/0", "bad number")
  add("return x,p end")
  add("if t==5 then return " .. n.MM .. ".huge,p end")
  add("if t==6 then return -" .. n.MM .. ".huge,p end")
  add("if t==7 then return 0/0,p end")
  add(n.AL .. "() " .. n.ERR .. "(" .. DM .. "(" .. codes("bytecode: field tag") .. ")) end")
  -- Layer 10 block loader: decodes the block that holds pc into the live map,
  -- evicting the oldest decoded block and re-encrypting it in place first.
  add("local function " .. LD .. "(p) return function(pc)")
  reject(n.G4 .. "(pc)~=\"number\" or pc<1 or pc>p.t or pc~=" .. FL .. "(pc)",
    "block position")
  add("local B=p.g local bi=" .. FL .. "((pc-1)/B)+1")
  add("local ka=" .. n.KSO .. "[p.i][1] local kc=" .. n.KSO ..
    "[p.i][2] local kb=" .. n.KSO .. "[p.i][3] local md=" .. n.KSO ..
    "[p.i][4] local sw=23+kb%74 local sh=1+kc%md")
  add("local nd=B local ls=p.t-(bi-1)*B if ls<nd then nd=ls end")
  add("while p.n+nd>p.m and #p.q>0 do")
  add("local od=" .. TR .. "(p.q,1)")
  add("local cnt=B local lt=p.t-(od-1)*B if lt<cnt then cnt=lt end")
  add("local rw=p.w[od]")
  add("p.s=(p.s*1664525+1013904223)%4294967296")
  add("local sv=p.s")
  add("local st=(p.k0+p.i*2654435761+od*2246822519+(sv%65536)+" ..
    FL .. "(sv/65536)*40961+p.h[od])%4294967296")
  add("local o={" .. SC .. "(sv%256," .. FL .. "(sv/256)%256," .. FL ..
    "(sv/65536)%256," .. FL .. "(sv/16777216)%256)}")
  add("for z=1,#rw do st=(st*1664525+1013904223)%4294967296 " ..
    "o[#o+1]=" .. SC .. "(" .. X8 .. "(" .. SB .. "(rw,z)," .. FL ..
    "(st/16777216)%256)) end")
  add("p.j[od]=" .. SJ .. "(o)")
  add("p.w[od]=nil p.n=p.n-cnt")
  add("for z=(od-1)*B+1,od*B do p." .. FC .. "[z]=nil end")
  add("end")
  add("local bk=p.j[bi]")
  add("local sv=" .. SB .. "(bk,1)+" .. SB .. "(bk,2)*256.0+" .. SB ..
    "(bk,3)*65536.0+" .. SB .. "(bk,4)*16777216.0")
  add("local st=(p.k0+p.i*2654435761+bi*2246822519+(sv%65536)+" ..
    FL .. "(sv/65536)*40961+p.h[bi])%4294967296")
  add("local o={}")
  add("for z=5,#bk do st=(st*1664525+1013904223)%4294967296 " ..
    "o[#o+1]=" .. SC .. "(" .. X8 .. "(" .. SB .. "(bk,z)," .. FL ..
    "(st/16777216)%256)) end")
  add("local s=" .. SJ .. "(o)")
  add("local ck=" .. SB .. "(s,1)+" .. SB .. "(s,2)*256.0+" .. SB ..
    "(s,3)*65536.0+" .. SB .. "(s,4)*16777216.0")
  add("if " .. FN .. "(" .. SS .. "(s,5))~=ck then " .. n.AL .. "() " .. n.ERR ..
    "(" .. DM .. "(" .. codes("bytecode: block checksum") .. ")) end")
  add("local bp=5")
  add("for z=1,nd do")
  add("local op; op,bp=" .. RD .. "(s,bp)")
  add("local qa; qa,bp=" .. RD .. "(s,bp)")
  add("local qb; qb,bp=" .. RD .. "(s,bp)")
  add("local qc; qc,bp=" .. RD .. "(s,bp)")
  add("local qd; qd,bp=" .. DV .. "(s,bp)")
  -- The packed block contains the *raw* alias key. Map that key through
  -- this prototype/window's bijective dispatch bank before adding KOF.
  add("local ix=(bi-1)*B+z local wi=" .. FL .. "((ix-1)/sw)")
  add("local rt=(ka*p.i+kb+wi*(1+kc%" .. totalSlots .. "))%" .. totalSlots)
  add("local os=op-" .. keyBase .. " local en=((kc+p.i+wi)%2==0 and (" ..
    totalSlots .. "-os) or (os-1))")
  add("p." .. FC .. "[ix]={((en+rt)%" .. totalSlots ..
    "+1)+((ix*ix*kc+ix*ka+kb+wi*sh)%md)," .. ZZ .. "(qa)," ..
    ZZ .. "(qb)," .. ZZ .. "(qc),qd}")
  add("end")
  reject("bp~=#s+1", "trailing block data")
  add("p.w[bi]=s p.n=p.n+nd p.q[#p.q+1]=bi")
  add("return p." .. FC .. "[pc]")
  add("end end")
  add("local np; np,pos=" .. RD .. "(" .. O .. ",pos)")
  reject("np<1 or np>" .. FL .. "((#" .. O .. "-pos+1)/6)", "prototype count")
  add("local " .. KD .. "={}")
  -- Block loaders live beside the prototype list, never inside it: a dump that
  -- walks P or calls a per-prototype decoder finds nothing to replay.
  add("local " .. n.LX .. "={}")
  add("local " .. n.P .. "={}")
  add("for pi=1,np do")
  add("local qa; qa,pos=" .. RD .. "(" .. O .. ",pos)")
  add("local qv; qv,pos=" .. RD .. "(" .. O .. ",pos)")
  add("local Q={" .. fk(FA) .. "=qa," .. fk(FV) .. "=qv==1," .. fk(FC) .. "={}," .. fk(FK) .. "={}," .. fk(FU) .. "={}}")
  add("local sm; sm,pos=" .. RD .. "(" .. O .. ",pos)")
  reject("qv>1 or sm>1", "flags")
  add("if sm==1 then")
  add("local B; B,pos=" .. RD .. "(" .. O .. ",pos)")
  add("local cp; cp,pos=" .. RD .. "(" .. O .. ",pos)")
  add("local tt; tt,pos=" .. RD .. "(" .. O .. ",pos)")
  add("local nb; nb,pos=" .. RD .. "(" .. O .. ",pos)")
  reject("B<1 or tt<1 or cp<1 or cp>tt or (cp<B and cp<tt) or " ..
    "(cp<tt and cp%B~=0) or nb~=" .. FL .. "((tt-1)/B)+1 or nb>" ..
    FL .. "((#" .. O .. "-pos+1)/15)", "block counts")
  add("Q.g=B Q.m=cp Q.t=tt Q.i=pi Q.j={} Q.h={} Q.q={} Q.w={} ")
  add("Q.n=0 Q.k0=" .. K0 .. " Q.s=" .. K0)
  add("for i=1,nb do local ch; ch,pos=" .. RD .. "(" .. O .. ",pos)")
  add("local ln; ln,pos=" .. RD .. "(" .. O .. ",pos)")
  add("local nd=tt-(i-1)*B if nd>B then nd=B end")
  reject("ch>=4294967296 or ln<8 or nd>" .. FL .. "((ln-8)/5)", "block bounds")
  add("Q.h[i]=ch Q.j[i],pos=" .. POS .. "(" .. O .. ",pos,ln) end")
  add(n.LX .. "[pi]=" .. LD .. "(Q)")  add("else")
      add("local nc; nc,pos=" .. RD .. "(" .. O .. ",pos)")
      reject("nc>" .. FL .. "((#" .. O .. "-pos+1)/5)", "instruction count")
      add("for i=1,nc do local i1; i1,pos=" .. RD .. "(" .. O .. ",pos)")
      add("local i2; i2,pos=" .. RD .. "(" .. O .. ",pos)")
      add("local i3; i3,pos=" .. RD .. "(" .. O .. ",pos)")
      add("local i4; i4,pos=" .. RD .. "(" .. O .. ",pos)")
      add("local i5; i5,pos=" .. DV .. "(" .. O .. ",pos)")
      add("local ks=" .. n.KSO .. "[pi] local wi=" .. FL ..
        "((i-1)/(23+ks[3]%74)) local slot=i1-" .. keyBase)
      add("local rt=(ks[1]*pi+ks[3]+wi*(1+ks[2]%" .. totalSlots ..
        "))%" .. totalSlots .. " local en=((ks[2]+pi+wi)%2==0 and (" ..
        totalSlots .. "-slot) or (slot-1))")
      add("Q." .. FC .. "[i]={((en+rt)%" .. totalSlots ..
        "+1)+((i*i*ks[2]+i*ks[1]+ks[3]+wi*(1+ks[2]%ks[4]))%ks[4])," ..
        ZZ .. "(i2)," .. ZZ .. "(i3)," .. ZZ .. "(i4),i5} end")
  add("end")
  add("local nk; nk,pos=" .. RD .. "(" .. O .. ",pos)")
  add("Q." .. FK .. "={}")
  -- Sealed constant section. The pool stays ciphertext until the first read,
  -- then the whole prototype's constants are opened at once and cached. A dump
  -- taken after startup only sees the prototypes the program has run.
  add("if nk>0 then")
  add("local kl; kl,pos=" .. RD .. "(" .. O .. ",pos)")
  reject("kl<8 or nk>kl-8", "constant bounds")
  add("local kc; kc,pos=" .. POS .. "(" .. O .. ",pos,kl)")
  add("local dec=function(t,i) if not kc then return nil end")
  add("local st=" .. SB .. "(kc,1)+" .. SB .. "(kc,2)*256.0+" .. SB ..
    "(kc,3)*65536.0+" .. SB .. "(kc,4)*16777216.0")
  add("local o={} local j=5 local lim=#kc local pv=st%256")
  add("while j<=lim do st=(st*1664525+1013904223)%4294967296 local cb=" ..
    SB .. "(kc,j) o[#o+1]=" .. SC .. "(" .. X8 .. "(cb," .. X8 .. "(" .. FL ..
    "(st/16777216)%256,pv))) pv=cb j=j+1 end")
  add("local sf=" .. SJ .. "(o)")
  add("local ck=" .. SB .. "(sf,1)+" .. SB .. "(sf,2)*256.0+" .. SB ..
    "(sf,3)*65536.0+" .. SB .. "(sf,4)*16777216.0")
  add("if " .. FN .. "(" .. SS .. "(sf,5))~=ck then " .. n.AL .. "() " .. n.ERR .. "(" .. DM ..
    "(" .. codes("bytecode: constant checksum") .. ")) end")
  add("local bp=5")
  add("for z=1,nk do local tg=" .. SB .. "(sf,bp) bp=bp+1")
  reject("not tg or tg>7", "constant tag")
  add("if tg==1 then " .. RA .. "(t,z,false) end")
  add("if tg==2 then " .. RA .. "(t,z,true) end")
  add("if tg==3 then local v; v,bp=" .. DV .. "(sf,bp-1) " .. RA ..
    "(t,z,v) end")
  add("if tg==4 then local ln; ln,bp=" .. RD .. "(sf,bp) local v; v,bp=" ..
    POS .. "(sf,bp,ln) " .. RA .. "(t,z,v) end")
  add("if tg==5 then " .. RA .. "(t,z,1/0) end")
  add("if tg==6 then " .. RA .. "(t,z,-1/0) end")
  add("if tg==7 then " .. RA .. "(t,z,0/0) end")
  add("end")
  reject("bp~=#sf+1", "trailing constant data")
  add("kc=nil return t[i] end")
  add(KD .. "[pi]=dec")
  add(n.G9 .. "(Q." .. FK .. ",{[" .. DM .. "(" .. codes("__metatable") .. ")]=false,[" ..
    DM .. "(" .. codes("__index") .. ")]=dec})")
  add("end")
  add("local nu; nu,pos=" .. RD .. "(" .. O .. ",pos)")
  reject("nu>" .. FL .. "((#" .. O .. "-pos+1)/2)", "upvalue count")
  add("for i=1,nu do local kd; kd,pos=" .. RD .. "(" .. O .. ",pos) " ..
    "local kx; kx,pos=" .. RD .. "(" .. O .. ",pos)")
  reject("kd>1", "upvalue flag")
  add("Q." .. FU .. "[i]={kd,kx} end")
  add(n.P .. "[pi]=Q")
  add("end")
  reject("pos~=#" .. O .. "+1", "trailing data")
  add(D .. "=nil " .. B .. "=nil " .. O .. "=nil " .. KB ..
    "=nil " .. HD .. "=nil")
  return sectionText
end

function VMGen.emit(plan, opts)
  opts = opts or {}
  local names = makeNames(plan.seed or VMGen.DEFAULT_SEED,
    opts.compactNames == true)
  local rng = makeRng((plan.seed or VMGen.DEFAULT_SEED) + 0x9E37)

  -- Entry wall. The chunk opens with a plain function whose parameter list is
  -- rebuilt on every build; the last parameter is overwritten with the state
  -- table and the real runtime sits in a nested function, so the wall never
  -- shares a register frame with the interpreter body. Nothing reads the
  -- parameters, but they shadow nothing either: the names are drawn outside
  -- every generated identifier and every global the runtime uses.
  local wall, wallSeen = {}, {}
  local wallKeyword = { ["do"] = true, ["if"] = true, ["in"] = true, ["or"] = true }
  for _, value in pairs(names) do
    if type(value) == "string" then wallSeen[value] = true end
  end
  local function wallName()
    local name
    repeat
      local p = rng(#LOWER)
      name = LOWER:sub(p, p)
      if rng(3) ~= 1 then
        local q = rng(#LOWER)
        name = name .. LOWER:sub(q, q)
      end
      if rng(4) == 1 then
        name = name:sub(1, 1):upper() .. name:sub(2)
      end
    until not wallSeen[name] and not wallKeyword[name]
    wallSeen[name] = true
    return name
  end
  for i = 1, 34 + rng(9) do wall[i] = wallName() end
  local wallText = table.concat(wall, ",")

  -- Dispatch transform. Keys are dense slot ids (1..#slots), so the handler
  -- table stays in the array part; the identity transform stays in the
  -- runtime text so the call site keeps the same shape across builds.
  local kMul, kBias = 1, 0
  local slotMap = plan.slots or {}
  local keyBase = plan.keyBase or 0
  local bankCount = assert(plan.totalSlots, "vmgen: missing dispatch bank size")
  local function keyNum(key)
    local slot = slotMap[key]
    if slot then return slot end
    return key * kMul + kBias
  end

  local lines = {}
  local function add(s) lines[#lines + 1] = s end
  -- Frame and prototype field names are identifiers; a table constructor
  -- needs them quoted, a field read uses the dot form.
  local function qn(s) return "[\"" .. s .. "\"]" end

  -- Runtime string builder: field names and error text are assembled from byte
  -- codes so no English word identifies a layer in the shipped file.
  local dl = '("\\' .. string.format("%03d", rng(255)) .. '")'
  -- Use Lua concatenation for short field/API names instead of table.concat.
  -- Environment loggers commonly intercept table.concat and thereby obtain
  -- the entire decoded name at once (as observed in dump.zip). With this
  -- builder the name is not passed to table.concat at all. This is leak
  -- reduction, NOT protection from an attacker who controls string.char or
  -- the entire Lua interpreter. Names are short, so per-byte concatenation
  -- adds negligible startup cost and avoids materializing a temporary table
  -- full of decoded characters for the instrumented API.
  add("local function " .. names.DM ..
    "(...) local a={...} local c=" .. dl .. ".char local s=\"\" " ..
    "for i=1,#a do s=s..c(a[i]) end return s end")

  -- DM-coded string literal: keeps Roblox API names out of the shipped text.
  local function dms(s) return names.DM .. "(" .. codes(s) .. ")" end

  -- Environment acquisition must survive hosts where `_ENV` is absent (5.1,
  -- Luau), where `getfenv` is missing (5.2+), and where `getfenv` exists but
  -- raises on a security level. `_G` is probed first with a standard global so
  -- an executor on Luau never needs a getfenv call at all; every step is
  -- independent and falls through, and the final `{}` only keeps the chunk
  -- alive long enough to exit cleanly.
  add("local " .. names.E .. "=_ENV")
  -- Luau has no `_ENV`; its global table is `getfenv(1)`. Asking first matters
  -- beyond accuracy: a sandbox may freeze `_G` (Luau's safe environment does),
  -- and a piece of a split build carries cross-piece values through SETGLOBAL.
  -- `_G` stays as the fallback for hosts where getfenv is blocked.
  add("if " .. names.E .. "==nil and _VERSION==" .. dms("Luau") ..
    " then local ok,g=pcall(function() local f=getfenv if type(f)==\"function\" then return f(1) end end) " ..
    "if ok and type(g)==\"table\" and type(g[" .. dms("string") .. "])==\"table\" " ..
    "and type(g[" .. dms("pcall") .. "])==\"function\" then " .. names.E .. "=g end end")
  add("if " .. names.E .. "==nil then local ok,g=pcall(function() local f=getfenv " ..
    "if type(f)==\"function\" then return f(1) end end) " ..
    "if ok and type(g)==\"table\" and type(g[" .. dms("string") .. "] )==\"table\" " ..
    "and type(g[" .. dms("pcall") .. "] )==\"function\" then " .. names.E .. "=g end end")
  add("if " .. names.E .. "==nil then local ok,g=pcall(function() local f=getgenv " ..
    "if type(f)==\"function\" then return f() end end) " ..
    "if ok and type(g)==\"table\" and type(g[" .. dms("string") .. "] )==\"table\" " ..
    "and type(g[" .. dms("pcall") .. "] )==\"function\" then " .. names.E .. "=g end end")
  add("if " .. names.E .. "==nil then " .. names.E ..
    "=(type(_G)==\"table\" and _G) or {} end")

  -- Roblox/Luau engines may legitimately differ from PUC Lua in debug APIs,
  -- userdata representations and service availability. Probe host identity
  -- without mutating it. A true Roblox host is NOT evidence of tampering;
  -- only payload, VM opcode and frame integrity may fail closed there.
  add("local " .. names.RBH .. "=0 do local ok,v=pcall(function() " ..
    "local f=" .. names.E .. "[" .. dms("typeof") .. "] " ..
    "local g=" .. names.E .. "[" .. dms("game") .. "] " ..
    -- [V1.0.1] Platform identification is non-authoritative: _VERSION
    -- alone is spoofable and cannot disable security checks.
    "local w=" .. names.E .. "[" .. dms("workspace") .. "] " ..
    "if _VERSION~=\"Luau\" or type(f)~=\"function\" or g==nil or w==nil then return false end " ..
    "return f(g)==\"Instance\" and f(w)==\"Instance\" " ..
    "and g.ClassName==\"DataModel\" and w.ClassName==\"Workspace\" end) " ..
    "if ok and v==true then " .. names.RBH .. "=1 end end")


  -- Environment chaff. The real captures below are a handful of reads; an env
  -- logger that records global traffic can normally pick them out. These
  -- decoy reads (Roblox services, executor helpers, debug/string fields) are
  -- assigned to a table that stays in scope, so at any point in the load the
  -- log and the live locals look the same whether or not the runtime actually
  -- uses a name. Two shuffled groups land on both sides of the real captures.
  local envChaff = 0
  local chaffGroup
  if names.CH and opts.envChaff ~= false then
    add("local " .. names.CH .. "={}")
    local cp = names.E .. "[" .. dms("pcall") .. "]"
    local usedKeys = {}
    local function chaffKey()
      for _ = 1, 64 do
        local k = rng(140) + 1
        if not usedKeys[k] then
          usedKeys[k] = true
          return k
        end
      end
      return nil
    end
    chaffGroup = function(list)
      local reads = {}
      for i = 1, #list do
        local item = list[i]
        local expr
        if item[2] then
          expr = names.E .. "[" .. dms(item[1]) .. "][" .. dms(item[2]) .. "]"
        else
          expr = names.E .. "[" .. dms(item[1]) .. "]"
        end
        local k = chaffKey()
        if k then
          reads[#reads + 1] = names.CH .. "[" .. k .. "]=" .. expr
          envChaff = envChaff + 1
        end
      end
      if #reads > 0 then
        add(cp .. "(function() " .. table.concat(reads, " ") .. " end)")
      end
    end
    local pool = {}
    for i = 1, #CHAFF_GLOBALS do pool[i] = { CHAFF_GLOBALS[i] } end
    shuffle(pool, rng)
    local first = {}
    for i = 1, math.min(9, #pool) do first[#first + 1] = pool[i] end
    chaffGroup(first)
  end

  -- Hardcoded globals: each library handle is resolved once here and only the
  -- local is used afterwards (bit helpers, DM, integrity, deviation, the
  -- sentinel guard). A hook that swaps `string.byte`, `table.concat`,
  -- `setmetatable` or `pcall` after load therefore cannot reach the protected
  -- runtime, and a devirt harness that restores the originals before dumping
  -- has nothing to restore. Values are captured positionally, never by name
  -- lookup at call time.
  local HARDCAPS = {
    { "G1", "string" }, { "G2", "table" }, { "G3", "pcall" },
    { "G4", "type" }, { "G9", "setmetatable" }, { "G5", "rawset" },
    { "G6", "pairs" }, { "G7", "getmetatable" },
  }
  for i = 1, #HARDCAPS do
    add("local " .. names[HARDCAPS[i][1]] .. "=" .. names.E ..
      "[" .. dms(HARDCAPS[i][2]) .. "]")
  end
  -- (game-side tamper probes are emitted further down, after the stop
  -- functions they call on a trip)
  -- Frozen function handles: the hot helpers below are copied by value, so a
  -- field swap performed after load cannot reach the protected runtime.
  add("local " .. names.B1 .. "=" .. names.G1 .. " and " .. names.G1 ..
    "[" .. dms("byte") .. "]")
  add("local " .. names.C1 .. "=" .. names.G1 .. " and " .. names.G1 ..
    "[" .. dms("char") .. "]")
  add("local " .. names.U1 .. "=" .. names.G1 .. " and " .. names.G1 ..
    "[" .. dms("sub") .. "]")
  add("local " .. names.C2 .. "=" .. names.G2 .. " and " .. names.G2 ..
    "[" .. dms("concat") .. "]")
  add("local " .. names.MM .. "=" .. names.E .. "[" .. dms("math") .. "]")
  add("local " .. names.SEL .. "=" .. names.E .. "[" .. dms("select") .. "]")
  -- A sandbox may leave a placeholder (a string) in table.unpack; the 5.1
  -- global is only a fallback when the field is not callable.
  add("local " .. names.SU .. "=" .. names.G2 .. " and " .. names.G2 ..
    "[" .. dms("unpack") .. "] if " .. names.G4 .. "(" .. names.SU ..
    ")~=\"function\" then " .. names.SU .. "=" .. names.E ..
    "[" .. dms("unpack") .. "] end")
  add("local " .. names.ERR .. "=" .. names.E .. "[" .. dms("error") .. "]")
  add("local " .. names.PK .. "=function(...) return {n=" .. names.SEL ..
    "(\"#\",...),...} end")

  -- Second chaff group: globals plus debug/string/io fields, emitted after the
  -- real captures so the log has no "reads stop after setup" boundary either.
  if names.CH and opts.envChaff ~= false then
    local rest = {}
    for i = 10, math.min(20, #CHAFF_GLOBALS) do rest[#rest + 1] = CHAFF_GLOBALS[i] end
    local fields = {}
    for i = 1, #CHAFF_FIELDS do fields[i] = CHAFF_FIELDS[i] end
    shuffle(rest, rng)
    shuffle(fields, rng)
    local second = {}
    for i = 1, #rest do second[#second + 1] = { rest[i] } end
    for i = 1, math.min(5, #fields) do second[#second + 1] = fields[i] end
    chaffGroup(second)
  end

  add("local " .. names.BW .. "," .. names.BN .. "," .. names.SHL .. "," ..
    names.SHR)
  add(names.BW .. "=function(x,y,m)")
  add("x=" .. names.MM .. ".floor(x)%9007199254740992 " ..
    "y=" .. names.MM .. ".floor(y)%9007199254740992")
  add("local r,pw=0,1")
  add("for j=1,53 do")
  add("local xa=x%2 local xb=y%2 local z")
  add("if m==1 then z=((xa==1)and(xb==1))and 1 or 0 end")
  add("if m==2 then z=((xa==1)or(xb==1))and 1 or 0 end")
  add("if m==3 then z=(xa~=xb)and 1 or 0 end")
  add("r=r+z*pw x=(x-xa)/2 y=(y-xb)/2 pw=pw*2")
  add("end")
  add("return r")
  add("end")
  add(names.BN .. "=function(x) return -" .. names.MM .. ".floor(x)-1 end")
  add(names.SHL .. "=function(x,y)")
  add("x=" .. names.MM .. ".floor(x) y=" .. names.MM .. ".floor(y)")
  add("if y<0 then return " .. names.SHR .. "(x,-y) end")
  add("if y>=53 then return 0 end")
  add("for j=1,y do x=x*2 end")
  add("return x")
  add("end")
  add(names.SHR .. "=function(x,y)")
  add("x=" .. names.MM .. ".floor(x) y=" .. names.MM .. ".floor(y)")
  add("if y<0 then return " .. names.SHL .. "(x,-y) end")
  add("if y>=53 then return 0 end")
  add("for j=1,y do x=" .. names.MM .. ".floor(x/2) end")
  add("return x")
  add("end")

  -- Joining the two limbs uses native integer overflow to recover the signed result.
  local integerBits = [=[
if @G4@(@MM@.tointeger)=="function" and @MM@.maxinteger then
  do
    local b={I=@MM@.tointeger,F=@MM@.floor,W=64,
      R=@E@.rawget,G=@E@.getmetatable,
      D=(function() local o,v=@G3@(function() return @E@.debug end)
        if o then return v end end)(),
      K={"__band","__bor","__bxor"}}
    if @E@._VERSION=="Lua 5.4" then
      b.C=b.I
      b.I=function(x) if @G4@(x)=="number" then return b.C(x) end end
    end
    if @MM@.maxinteger==2147483647 then b.W=32 end
    do local g
      @G3@(function() if @G4@(b.D)=="table" then
        local v=b.D.getmetatable
        if @G4@(v)=="function" then g=v end
      end end)
      if g then b.G=g b.A=true else b.G=function() return nil end end
    end
    b.M=function(x,k)
      local t=b.G(x)
      if t~=nil and @G4@(t)~="table" then
        return @ERR@("protected bitwise metamethod is unavailable",2)
      end
      if @G4@(t)=="table" then return b.R(t,k) end
    end
    b.E=function(x,y,k)
      local f=b.M(x,k)
      if f==nil then f=b.M(y,k) end
      if f~=nil then return (f(x,y)) end
      return @ERR@("attempt to perform bitwise operation (integer required)",2)
    end
    b.S=function(x)
      local l=x%4294967296
      if b.W==32 then return l,0 end
      return l,b.I((x-l)/4294967296)%4294967296
    end
    b.J=function(l,h)
      if b.W==32 then
        if l>=2147483648 then l=l-4294967296 end
        return b.I(l)
      end
      return b.I(h)*4294967296+b.I(l)
    end
    b.B=function(x,y,m)
      local r,p=0,1
      for j=1,32 do
        local a,c=x%2,y%2
        if (m==1 and a==1 and c==1) or
          (m==2 and (a==1 or c==1)) or (m==3 and a~=c) then r=r+p end
        x=(x-a)/2 y=(y-c)/2 p=p*2.0
      end
      return r
    end
    @BW@=function(x,y,m)
      local a,c=b.I(x),b.I(y)
      if a==nil or c==nil then return b.E(x,y,b.K[m]) end
      local l,h=b.S(a) local v,w=b.S(c)
      return b.J(b.B(l,v,m),b.B(h,w,m))
    end
    @BN@=function(x)
      local a=b.I(x)
      if a==nil then return b.E(x,x,"__bnot") end
      local l,h=b.S(a)
      return b.J(4294967295-l,4294967295-h)
    end
    b.T=function(x,y,left,k)
      local a,c=b.I(x),b.I(y)
      if a==nil or c==nil then return b.E(x,y,k) end
      if c>=b.W or c<=-b.W then return 0 end
      if c<0 then c=-c left=not left end
      local l,h=b.S(a)
      for j=1,c do
        if left then
          h=(h*2.0+b.F(l/2147483648))%4294967296
          l=(l*2.0)%4294967296
        else
          l=b.F(l/2)+(h%2)*2147483648
          h=b.F(h/2)
        end
      end
      return b.J(l,h)
    end
    @SHL@=function(x,y) return b.T(x,y,true,"__shl") end
    @SHR@=function(x,y) return b.T(x,y,false,"__shr") end
  end
else
]=]
  add((integerBits:gsub("@([A-Z0-9]+)@", function(k) return names[k] end)))
  -- Luau/Lua 5.2 retain bit32; older hosts retain the arithmetic floor above.
  add("local bt=" .. names.E .. "[" .. dms("bit32") .. "]")
  add("if " .. names.G4 .. "(bt)==\"table\" then")
  add("local bd,bo,bx,bl,br=bt[" .. dms("band") .. "],bt[" .. dms("bor") ..
    "],bt[" .. dms("bxor") .. "],bt[" .. dms("lshift") .. "],bt[" ..
    dms("rshift") .. "]")
  add("if " .. names.G4 .. "(bd)==\"function\" and " .. names.G4 .. "(bl)==\"function\" then")
  add(names.BW .. "=function(x,y,m) if m==1 then return bd(x,y) end if m==2 then return bo(x,y) end return bx(x,y) end")
  -- bit32.bnot returns the unsigned 32-bit value; every other host (and the
  -- reference VM) return the signed two's-complement result, so it is folded
  -- back into signed form to keep all hosts bit-identical.
  add(names.BN .. "=function(x) local v=bt[" .. dms("bnot") ..
    "](x) if v>=2147483648 then return v-4294967296 end return v end")
  add(names.SHL .. "=function(x,y) if y<0 then return br(x,-y) end return bl(x,y) end")
  add(names.SHR .. "=function(x,y) if y<0 then return bl(x,-y) end return br(x,y) end")
  add("end end end")

  -- Executor-only gate: skip only when the host shows no Roblox or executor
  -- marker at all (plain website runners). Detection is a wide OR over every
  -- known executor API plus the Roblox globals, so an executor that hides
  -- getgenv, or a game whose env only exposes `workspace`, is never mistaken
  -- for a plain host and silently skipped.
  if opts.executor then
    local exParts = {}
    for i = 1, #Antidebug.EXECUTOR_KEYS do
      exParts[i] = names.G4 .. "(" .. names.E .. "[" ..
        dms(Antidebug.EXECUTOR_KEYS[i]) .. "])==\"function\""
    end
    add("local EG=(" .. table.concat(exParts, " or ") .. ")")
    add("if not EG and " .. names.E .. "[" .. dms("game") .. "]==nil and " ..
      names.E .. "[" .. dms("Instance") .. "]==nil and " ..
      names.E .. "[" .. dms("workspace") .. "]==nil then return end")
  end

  -- gethui: prefer the executor's hidden container; polyfill one under CoreGui
  -- when absent. pcall-guarded so a non-Roblox host simply skips it.
  if opts.gethui then
    add(names.G3 .. "(function() local E=" .. names.E .. " local k=" .. dms("gethui") ..
      " if " .. names.G4 .. "(E[k])==\"function\" then return end local ok,cg=" .. names.G3 .. "(function() " ..
      "return E[" .. dms("game") .. "]:GetService(" .. dms("CoreGui") .. ") end) " ..
      "if ok and cg then E[k]=function() return cg end end end)")
  end

  -- anti-webhook: wrap the executor HTTP globals so any request aimed at a
  -- webhook URL is dropped silently. Plain function replacement, no metamethod
  -- hooks; a host without these globals is untouched.
  if opts.antiwebhook then
    add(names.G3 .. "(function() local E=" .. names.E .. " local hk=" .. dms("http_request") ..
      " local rk=" .. dms("request") .. " local H=E[hk] or E[rk] " ..
      "if " .. names.G4 .. "(H)~=\"function\" then return end local wb=" .. dms("webhook") ..
      " local uk=" .. dms("Url") .. " local lk=" .. dms("url") ..
      " local function bad(t) if " .. names.G4 .. "(t)~=\"table\" then return false end " ..
      "local u=\"\"..(t[uk] or t[lk] or \"\") return u:find(wb,1,true)~=nil end " ..
      "local function wrap(o) return function(t) if bad(t) then " ..
      "return {StatusCode=200,Body=\"\"} end return o(t) end end " ..
      "if " .. names.G4 .. "(E[hk])==\"function\" then E[hk]=wrap(E[hk]) end " ..
      "if " .. names.G4 .. "(E[rk])==\"function\" then E[rk]=wrap(E[rk]) end end)")
  end

  add(ClaxAlert.emit(names.KS, names.AL))
  -- The full Roblox API matrix is highly host/version dependent. It used to
  -- abort even for healthy clients when three ordinary APIs behaved
  -- differently. Leave this aggressive heuristic opt-in; the independent
  -- blob, VM opcode, handler and instruction checks stay fail-closed.
  local tamperProbes = 0
  if opts.strictHostChecks == true then
    add(Tamper.emit(names, { kill = names.KS .. "()" }))
    tamperProbes = Tamper.probeCount or 0
  end

  local ad = opts.antidebug
  if ad == true then ad = Antidebug.plan({ seed = plan.seed or VMGen.DEFAULT_SEED }) end
  if ad then
    local lines = Antidebug.prologue(names, ad)
    for i = 1, #lines do add(lines[i]) end
    -- [V1.0.1] Host probes are scored uniformly. Platform fingerprints are
    -- informational only; never reset an accumulated anti-debug result.
  end

  local el
  if ad and names.ADT then
    el = Envlog.plan({ seed = plan.seed })
    local lines = Envlog.prologue(names, el)
    for i = 1, #lines do add(lines[i]) end
    -- [V1.0.1] Anti-debug results cannot be bypassed via _VERSION/typeof.
    add("if " .. names.ADT .. "==1 then " .. names.KS .. "() end")
  end

  local ig = opts.integrity
  if ig == true then
    -- Every numeric dispatch key the handler table will hold: the real opcode
    -- keys plus the decoys. The integrity tick samples two of them per
    -- checkpoint and the one-shot audit verifies all of them against HB, so a
    -- pruned decoy or a swapped handler is caught instead of assumed benign.
    local allKeys = {}
    for i = 1, #Compiler.OPS do
      local keys = plan.opkeys[Compiler.OPS[i]]
      if keys then
        for j = 1, #keys do
          allKeys[#allKeys + 1] = keyNum(keys[j])
        end
      end
    end
    for i = 1, #(plan.decoys or {}) do
      allKeys[#allKeys + 1] = keyNum(plan.decoys[i])
    end
    ig = Integrity.plan({
      seed = plan.seed or VMGen.DEFAULT_SEED,
      keys = allKeys,
      total = #allKeys,
    })
    ig.fail = names.KS .. "()"
    -- Record ALL prototype instruction counts. Previously every lazy/selfmod
    -- prototype was marked zero, disabling the entire length check when the
    -- strong preset made every prototype lazy.  For lazy prototypes, Q.t is
    -- the immutable-at-runtime *expected total*; Q.c is merely a cache window
    -- whose sparse length must NOT be used for integrity validation.
    local lens, modes = {}, {}
    for pi = 1, #plan.protos do
      local PP = plan.protos[pi]
      local sm = PP.sm == true
      local total = sm and PP.total or (PP.c and #PP.c)
      if type(total) ~= "number" or total < 1 or total ~= math.floor(total) then
        error("vmgen: prototype " .. pi .. " has no valid instruction count", 0)
      end
      lens[pi], modes[pi] = total, sm and 1 or 0
    end
    ig.protoLens, ig.protoModes, ig.protoCount = lens, modes, #plan.protos
    -- The key ring stays in the builder until the handler table is emitted;
    -- vmgen places the literal right before HB is copied.
    ig.ring = allKeys
    -- Seal flag: the read-only guard sets it once the three tables carry
    -- `__metatable=false`. Without a captured getmetatable the guard leaves the
    -- flag at 0 and the tick skips the seal check instead of raising.
    if names.G7 then ig.mtFlag = names.IM end
  end
  -- The integrity tick also advances the anti-debug late-hook latch, and a
  -- confirmed latch becomes an integrity failure. The latch only moves when no
  -- load-time probe fired and the host is not an executor (both already set up
  -- by the probe block), so a normal executor session and a hook installed
  -- before load never reach it.
  if ig and ad and names.ADH then
    -- VM integrity tick also runs on Roblox; lateCheck handles unsupported
    -- debug APIs by skipping, not by clearing a tamper flag.
    ig.pre = Antidebug.lateCheck(names)
    ig.lateFlag = names.ADH
  end
  -- Post-load primitive snapshot. The debug entry points and the loaders are
  -- what a dump / devirt harness hooks to intercept dispatch, pull upvalues or
  -- replay bytecode. Their identities are recorded here, after the load-time
  -- probes have settled, and the integrity tick reports an error if any of them
  -- is replaced while the script is running. Missing entries (Luau has no
  -- getinfo/string.dump, sandboxes strip parts of debug) are stored as nil and
  -- skipped, so a host that never had them is never flagged.
  if ig and ad and names.IS and names.ADB and names.ADS then
    local ADB, ADS, E = names.ADB, names.ADS, names.E
    -- With the capability snapshot the live values are read through the same
    -- protected helper the probes use: a proxy that denies one entry yields
    -- nil (stored and re-read as nil), never a raising index at dispatch time.
    local safe = names.ADY and names.ADB0 and names.ADS0 and names.DM
    local function rd(base, key) return names.ADY .. "(" .. base .. "," .. key .. ")" end
    local function dbg(key) return rd(names.ADB0, key) end
    local function str(key) return rd(names.ADS0, key) end
    local function env(key) return rd(names.E, dms(key)) end
    local function nested(lib, field)
      return rd(rd(names.E, dms(lib)), dms(field))
    end
    local snap, checks = {}, {}
    local function add2(expr)
      snap[#snap + 1] = expr
      checks[#checks + 1] = expr
    end
    for _, key in ipairs({ names.AGH, names.AGI, names.ADU, names.AGR }) do
      add2(safe and dbg(key) or (ADB .. " and " .. ADB .. "[" .. key .. "]"))
    end
    add2(safe and str(names.AGD) or (ADS .. " and " .. ADS .. "[" .. names.AGD .. "]"))
    -- Wider primitive snapshot. The five entries above cover the classic
    -- dump surfaces; these add every other function a live instruction tracer,
    -- string spy or handler emulator has to wrap: debug's remaining entry
    -- points, the coroutine machinery, metatable/raw access, the protected
    -- call, the pattern library and the core type/number conversions. They are
    -- gated on `not ADE` so a healthy executor that legitimately wraps any of
    -- them can continue running.
    local extra = {
      { "D", "info" }, { "D", "traceback" }, { "D", "getlocal" },
      { "D", "setlocal" }, { "D", "setupvalue" }, { "D", "sethook" },
      { "C", "resume" }, { "C", "wrap" }, { "C", "yield" }, { "C", "status" },
      { "E", "setmetatable" }, { "E", "getmetatable" }, { "E", "rawget" },
      { "E", "rawset" }, { "E", "xpcall" }, { "E", "select" },
      { "E", "tonumber" }, { "E", "tostring" }, { "E", "next" },
      { "E", "pairs" }, { "E", "ipairs" }, { "E", "error" },
      -- The source loaders. A dump/emulation harness replaces load or
      -- loadstring while it replays the artifact; a healthy executor leaves
      -- them (or has none) and the nil-handling below keeps this a no-op there.
      { "E", "load" }, { "E", "loadstring" },
      { "E", "getfenv" }, { "E", "setfenv" },
      { "S", "char" }, { "S", "byte" }, { "S", "sub" }, { "S", "find" },
      { "S", "gsub" },
      { "B", "table", "concat" }, { "B", "math", "floor" },
      -- Luau anti-environment capabilities. Check identity changes after a
      -- healthy startup without treating an originally absent API as tamper.
      -- Existing executor compatibility gate still applies to these optional
      -- snapshots; bytecode and handler integrity remain unconditional.
      { "B", "table", "pack" }, { "B", "table", "freeze" },
      { "B", "table", "isfrozen" },
      { "B", "buffer", "create" }, { "B", "buffer", "readu16" },
      { "B", "buffer", "writeu16" }, { "B", "buffer", "len" },
    }
    local extraCount = 0
    if names.ADE and names.DM then
      for i = 1, #extra do
        local kind, field = extra[i][1], extra[i][2]
        local expr
        if safe then
          if kind == "D" then expr = dbg(dms(field))
          elseif kind == "S" then expr = str(dms(field))
          elseif kind == "C" then expr = nested("coroutine", field)
          elseif kind == "B" then expr = nested(field, extra[i][3])
          else expr = env(field) end
        elseif kind == "D" then
          expr = ADB .. " and " .. ADB .. "[" .. dms(field) .. "]"
        elseif kind == "S" then
          expr = ADS .. " and " .. ADS .. "[" .. dms(field) .. "]"
        elseif kind == "C" then
          local ce = E .. "[" .. dms("coroutine") .. "]"
          expr = ce .. " and " .. ce .. "[" .. dms(field) .. "]"
        elseif kind == "B" then
          local ce = E .. "[" .. dms(field) .. "]"
          expr = ce .. " and " .. ce .. "[" .. dms(extra[i][3]) .. "]"
        else
          expr = E .. "[" .. dms(field) .. "]"
        end
        add2(expr)
      end
      extraCount = #extra
    end
    add("local " .. names.IS .. "={" .. table.concat(snap, ",") .. "}")
    -- Preserve nil/false baselines: `baseline and current~=baseline` silently
    -- ignores changes to capabilities that were initially absent. Comparing
    -- both directions also detects late insertion of a debug/library field.
    -- Rotating the lower-priority extra identities avoids re-reading dozens
    -- of optional APIs on every checkpoint (and reduces redundant dump logs).
    -- The initial five core identities remain checked on EVERY checkpoint.
    local core, optional = {}, {}
    for i = 1, #checks do
      local term = "(" .. names.IS .. "[" .. i .. "]~=" .. checks[i] .. ")"
      if i <= 5 then
        core[#core + 1] = term
      else
        optional[#optional + 1] = term
      end
    end
    local rotationSize = 6
    local rotationGroups = math.max(1, math.ceil(#optional / rotationSize))
    add("local " .. names.ASI .. "=0")
    local branches = {}
    for group = 1, rotationGroups do
      local items = {}
      for j = (group - 1) * rotationSize + 1,
          math.min(group * rotationSize, #optional) do
        items[#items + 1] = optional[j]
      end
      branches[#branches + 1] = "(" .. names.ASI .. "==" .. group ..
        " and (" .. table.concat(items, " or ") .. "))"
    end
    -- The existing host-compatibility gate is retained for optional APIs;
    -- runtime opcode, prototype, packed-payload and handler checks are NOT
    -- gated or cached by this rotation.
    ig.extra = "(" .. table.concat(core, " or ") ..
      " or (" .. names.ADE .. "==0 and (" ..
      table.concat(branches, " or ") .. ")))"
    -- Executed once per integrity checkpoint, *before* evaluating ig.extra.
    ig.pre = (ig.pre or "") .. " " .. names.ASI .. "=" .. names.ASI ..
      "%" .. rotationGroups .. "+1"
    ig.snapshotChecks = #checks
    ig.extraChecks = extraCount
    ig.snapshotRotationGroups = rotationGroups
  end
  -- Per-prototype opcode keystream. Every instruction stores `slot+off` with
  -- `off=(pc*pc*kc+pc*ka+kb)%md` instead of the bare dispatch slot, so neither
  -- the packed payload nor a dump of the live instruction map lines up with
  -- the handler keys in the source. Along with the quadratic term, a
  -- window-boundary-dependent adjustment means a single polynomial fit does
  -- not explain all PCs. The runtime subtracts the same value before lookup;
  -- the handler bodies and dispatch validation remain unchanged.
  local ks = plan.keystream
  if not ks then
    ks = buildKeystream(plan.seed or VMGen.DEFAULT_SEED, #plan.protos)
  end
  local ksParts = {}
  for pi = 1, #ks do
    local k = ks[pi]
    ksParts[pi] = "{" .. k[1] .. "," .. k[2] .. "," .. k[3] .. "," .. k[4] .. "}"
  end
  add("local " .. names.KSO .. "={" .. table.concat(ksParts, ",") .. "}")
  if ig then
    -- Independent one-word checksum per prototype, rather than a second full
    -- byte-for-byte copy of the four-word opcode-mixer table. A modified
    -- coefficient is detected by comparing a runtime checksum with this
    -- build-time anchor. This is not authentication against a hostile host.
    local function checksum(k)
      local h = 811
      for j = 1, 4 do h = (h * 257 + k[j]) % 4294967296 end
      return h
    end
    local anchors = {}
    for pi = 1, #ks do anchors[pi] = tostring(checksum(ks[pi])) end
    add("local " .. names.KSR .. "={" .. table.concat(anchors, ",") .. "}")
    add("local function " .. names.KSH .. "(r) if " .. names.G4 ..
      "(r)~=\"table\" then return -1 end local h=811 " ..
      "for j=1,4 do local v=r[j] if " .. names.G4 ..
      "(v)~=\"number\" or v%1~=0 then return -1 end " ..
      "h=(h*257+v)%4294967296 end return h end")
  end
  local payload = opts.payload
  local payloadSection
  if payload then
    payloadSection = emitPacked(add, names, payload, rng, ig, keyBase, bankCount)
  else
    local protoParts = {}
    for pi = 1, #plan.protos do
      local P = plan.protos[pi]
      local pk = ks[pi]
      local code = {}
      for i = 1, #P.c do
        local I = P.c[i]
        local off = koff(i, pk)
        code[i] = "{" .. (tonumber(I[1]) and (bankSlot(I[1] - keyBase, pi, i, pk, bankCount) + off) or I[1]) ..
          "," .. I[2] .. "," .. I[3] .. "," .. I[4] .. "," .. I[5] .. "}"
      end
      local k = {}
      for i = 1, #P.k do k[i] = serializeValue(P.k[i]) end
      local u = {}
      for i = 1, #P.u do u[i] = "{" .. P.u[i][1] .. "," .. P.u[i][2] .. "}" end
      protoParts[pi] = "{[\"" .. names.PCC .. "\"]={" ..
        table.concat(code, ",") .. "},[\"" .. names.PKK .. "\"]={" ..
        table.concat(k, ",") .. "},[\"" .. names.PUU .. "\"]={" ..
        table.concat(u, ",") .. "},[\"" .. names.PAA ..
        "\"]=" .. (P.a or 0) .. ",[\"" .. names.PVV .. "\"]=" ..
        (P.v and "true" or "false") .. "}"
    end
    add("local " .. names.P .. "={" .. table.concat(protoParts, ",") .. "}")
  end
  -- [PROTO-META] Every prototype's call signature and upvalue capture
  -- descriptors are committed at build time. The packed loader verifies the
  -- ciphertext, but the running VM must also detect changes to the unpacked
  -- mutable tables. No extra per-dispatch work is needed.
  if ig then
    local function metadataHash(p)
      local h = 811
      local function fold(v) h = (h * 257 + v) % 4294967296 end
      fold(p.a or 0)
      fold(p.v and 1 or 0)
      fold(#(p.u or {}))
      for j = 1, #(p.u or {}) do
        fold(p.u[j][1])
        fold(p.u[j][2])
      end
      return h
    end
    local anchors = {}
    for pi = 1, #plan.protos do
      anchors[pi] = tostring(metadataHash(plan.protos[pi]))
    end
    add("local " .. names.PMA .. "={" .. table.concat(anchors, ",") .. "}")
    add("local function " .. names.PMH .. "(pi) local p=" .. names.P .. "[pi] " ..
      "if " .. names.G4 .. "(p)~=\"table\" then return false end " ..
      "local u=p." .. names.PUU .. " local a=p." .. names.PAA ..
      " local v=p." .. names.PVV ..
      " if " .. names.G4 .. "(u)~=\"table\" or " .. names.G4 ..
      "(a)~=\"number\" or a~=a or a%1~=0 or a<0 or " ..
      "(v~=true and v~=false) then return false end " ..
      "local h=811 h=(h*257+a)%4294967296 " ..
      "h=(h*257+(v and 1 or 0))%4294967296 " ..
      "h=(h*257+#u)%4294967296 " ..
      "for j=1,#u do local e=u[j] " ..
      "if " .. names.G4 .. "(e)~=\"table\" or " ..
      names.G4 .. "(e[1])~=\"number\" or " .. names.G4 ..
      "(e[2])~=\"number\" or e[1]%1~=0 or e[2]%1~=0 " ..
      "or e[1]<0 or e[1]>1 or e[2]<0 then return false end " ..
      "h=(h*257+e[1])%4294967296 " ..
      "h=(h*257+e[2])%4294967296 end " ..
      "return h==" .. names.PMA .. "[pi] end")
    ig.protoMetadata = true
  end
  -- Handler-table backup: the function table is complete before the loop
  -- starts, so a private copy is taken and every dispatch compares the
  -- resolved handler with that copy before calling it. A harness that swaps a
  -- table entry to record, wrap or emulate dispatch is reverted to the clean
  -- function on the very instruction that would have used it. The cost is one
  -- extra table read and one compare per instruction, no table walk.
  -- Without a packed payload there is no K0 in the chunk, so the two
  -- constants are emitted directly. Dense slot ids make both the identity.
  add("local " .. names.OM .. "=1 local " .. names.OB .. "=0")
  add("local " .. names.H .. "={}")
  -- Declared before the handlers so CLOSURE captures it as an upvalue.
  add("local " .. names.X .. "," .. names.F)
  add("local " .. names.HB)
  if ig and ig.pinCount and ig.pinCount > 0 then add("local " .. names.IPIN) end
  -- Seal flag and the key ring the rotating audit walks. The ring is a private
  -- copy of the dispatch key list, so the tick needs no key enumeration.
  add("local " .. names.IM .. "=0")
  if ig and ig.ring then
    add("local " .. names.IE .. "={" .. table.concat(ig.ring, ",") .. "}")
  end
  add(names.X .. "=function(" .. names.VPI .. "," .. names.VU .. ",...)")
  add("local " .. names.VPW .. "=" .. names.P .. "[" .. names.VPI .. "]")
  if ig and names.IGM and names.IG then
    -- Every function entry checks its own immutable expected total.  A lazy
    -- decoder is allowed to evict cache entries, but NOT to change Q.t.
    add("if " .. names.G4 .. "(" .. names.VPW .. ")~=\"table\" or " ..
      names.IG .. "[" .. names.VPI .. "]==nil then " .. names.KS ..
      "() elseif " .. names.IGM .. "[" .. names.VPI .. "]==1 then " ..
      "if " .. names.VPW .. ".t~=" .. names.IG .. "[" .. names.VPI ..
      "] then " .. names.KS .. "() end else " ..
      "if #" .. names.VPW .. "." .. names.PCC .. "~=" ..
      names.IG .. "[" .. names.VPI .. "] then " .. names.KS ..
      "() end end")
  end
  if ig then
    add("if not " .. names.PMH .. "(" .. names.VPI .. ") then " ..
      names.KS .. "() end")
  end
  add("local " .. names.VK .. "=" .. names.VPW .. "." .. names.PKK ..
    " local " .. names.VCW .. "=" .. names.VPW .. "." .. names.PCC)
  if ig and names.KSR then
    local a, b = names.KSO .. "[" .. names.VPI .. "]", names.KSR .. "[" .. names.VPI .. "]"
    add("if " .. names.KSH .. "(" .. a .. ")~=" .. b ..
      " then " .. names.KS .. "() end")
  end
  add("local " .. names.VR .. " local " .. names.VS)
  -- Fixed-arity prototypes never read S.ar, so the packed-vararg table and the
  -- copy loop are skipped: the register file *is* the argument list. This is
  -- the per-call fast path; a game script makes far more calls than loops.
  add("if " .. names.VPW .. "." .. names.PVV .. " then local " .. names.VA ..
    "={n=" .. names.SEL .. "(\"#\",...),...} " .. names.VR .. "={} " ..
    "for j=1," .. names.VPW .. "." .. names.PAA .. " do " .. names.VR ..
    "[j]=" .. names.VA .. "[j] end " .. names.VS .. "={" .. qn(names.STOP) ..
    "=" .. names.VPW .. "." .. names.PAA .. "+1," .. qn(names.SPROTO) .. "=" ..
    names.VPW .. "," .. qn(names.SARGS) .. "=" .. names.VA .. "," ..
    qn(names.SAN) .. "=" .. names.VA .. ".n," ..
    qn(names.SPID) .. "=" .. names.VPI .. "}")
  add("else " .. names.VR .. "={...} " .. names.VS .. "={" .. qn(names.STOP) ..
    "=" .. names.VPW .. "." .. names.PAA .. "+1," .. qn(names.SPROTO) .. "=" ..
    names.VPW .. "," .. qn(names.SARGS) .. "=" .. names.VR .. "," ..
    qn(names.SAN) .. "=" .. names.VPW .. "." .. names.PAA .. "," ..
    qn(names.SPID) .. "=" .. names.VPI .. "} end")
  add("local " .. names.VPC .. "=1")
  add("local " .. names.KW .. "=23+" .. names.KSO .. "[" .. names.VPI ..
    "][3]%74 local " .. names.KY .. "=1+" .. names.KSO .. "[" ..
    names.VPI .. "][2]%" .. names.KSO .. "[" .. names.VPI .. "][4]")
  -- Cache frame-invariant dispatch-bank coefficients once per prototype call.
  -- The inverse still varies at each instruction window; only fixed terms
  -- move out of the hot dispatch loop.
  add("local " .. names.KBR .. "=(" .. names.KSO .. "[" .. names.VPI ..
    "][1]*" .. names.VPI .. "+" .. names.KSO .. "[" .. names.VPI ..
    "][3])%" .. bankCount)
  add("local " .. names.KBS .. "=1+" .. names.KSO .. "[" .. names.VPI ..
    "][2]%" .. bankCount .. " local " .. names.KBP .. "=(" ..
    names.KSO .. "[" .. names.VPI .. "][2]+" .. names.VPI .. ")%2")
  -- The four keystream words of this prototype stay in KSO; the loop below
  -- evaluates the quadratic mix and hands the result to the handler, which
  -- unwraps its register operands with it.
  -- The six dispatch arguments keep their values but trade positions per
  -- build: the call site and every handler signature are emitted from the same
  -- shuffled list, so a dumped handler cannot be parsed positionally into
  -- (instr, regs, consts, upvals, frame, pc) across builds.
  local frameParams = { names.VI, names.VR, names.VK, names.VU, names.VS,
    names.VPC }
  shuffle(frameParams, rng)
  local frameSig = table.concat(frameParams, ",")
  -- The interpreter loop is spelled one of three equivalent ways per build;
  -- nothing else in the emitted chunk depends on the keyword, and every
  -- handler exits with `return`, so the shapes are interchangeable even for
  -- the repeat form.
  local loopShape = rng(3)
  if loopShape == 1 then
    add("repeat")
  elseif loopShape == 2 then
    add("while 1==1 do")
  else
    add("while true do")
  end
  if ig then
    add(Integrity.loop(names, ig))
    -- Runtime CFI: reject illegal/fragmentary virtual control-flow BEFORE
    -- attempting to index the instruction cache or lazy decoder.  This is
    -- deliberately separate from the packed-blob checksum: a debugger may
    -- edit a live frame after load while leaving the encrypted blob intact.
    -- Only the protected mode carries the expected per-prototype totals.
    add("if " .. names.G4 .. "(" .. names.VPC .. ")~=\"number\" or " ..
      names.VPC .. "~= " .. names.VPC .. " or " .. names.VPC .. "<1 or " ..
      names.VPC .. ">" .. names.IG .. "[" .. names.VPI .. "] or " ..
      names.VPC .. "%1~=0 then " .. names.KS .. "() end")
    -- Re-check this prototype's 4-word opcode mixer on every dispatch.
    -- This is a live-table tripwire, NOT a secret held outside the artifact.
    if names.KSR then
      local a, b = names.KSO .. "[" .. names.VPI .. "]", names.KSR .. "[" .. names.VPI .. "]"
      add("if " .. names.KSH .. "(" .. a .. ")~=" .. b ..
        " then " .. names.KS .. "() end")
    end
  end
  -- Early hook observations used to hard-fail after two samples. That
  -- incorrectly killed scripts when a legitimate profiler attached during
  -- execution. Hook presence is now diagnostic only; actual VM opcode,
  -- payload and handler-integrity checks below remain fail-closed.
  add("local " .. names.VI .. "=" .. names.VCW .. "[" .. names.VPC .. "]")
  add("if not " .. names.VI .. " then " .. names.VI .. "=" .. names.LX ..
    "[" .. names.VPI .. "](" .. names.VPC .. ") end")
  if ig then
    -- An interpreter must never execute an incomplete or foreign instruction.
    -- Operands are numeric; the final immediate may be fractional, so we
    -- intentionally check *type* rather than imposing integer operands.
    local fields = {}
    for j = 1, 5 do
      fields[#fields+1] = names.G4 .. "(" .. names.VI .. "[" .. j ..
        "])~=\"number\""
    end
    add("if " .. names.G4 .. "(" .. names.VI .. ")~=\"table\" then " ..
      names.KS .. "() end")
    add("if " .. table.concat(fields," or ") .. " then " .. names.KS ..
      "() end")
  end
  -- `OM*key+OB` is the identity (both are emitted as 1 and 0), so the fold is
  -- only there to keep the packed and non-packed call sites textually alike.
  -- The word carries slot+off(pc), including the prototype-specific window
  -- adjustment; the same expression is subtracted back here. This raises
  -- static decoding work but cannot conceal a host-visible runtime forever.
  add("local " .. names.KRI .. "=" .. names.MM .. ".floor((" .. names.VPC ..
    "-1)/" .. names.KW .. ")")
  add("local " .. names.KOF .. "=((((" .. names.VPC .. "*" .. names.VPC ..
    "*" .. names.KSO .. "[" .. names.VPI .. "][2]+" .. names.VPC .. "*" ..
    names.KSO .. "[" .. names.VPI .. "][1]+" .. names.KSO .. "[" ..
    names.VPI .. "][3]+" .. names.KRI .. "*" .. names.KY .. ")%" ..
    names.KSO .. "[" .. names.VPI .. "][4])))")
  -- Undo the bijective dispatch-bank transform before the protected
  -- handler lookup. Its parameters vary by both prototype and instruction
  -- window; all three transport paths share the same inverse.
  add("local " .. names.KRM .. "=(" .. names.KBR .. "+" .. names.KRI ..
    "*" .. names.KBS .. ")%" .. bankCount)
  add("local " .. names.KRC .. "=(" .. names.VI .. "[1]-" .. names.KOF ..
    "-1-" .. names.KRM .. ")%" .. bankCount)
  add("local " .. names.VHI .. "=((" .. names.KBP .. "+" .. names.KRI ..
    ")%2==0) and (" ..
    bankCount .. "-" .. names.KRC .. ") or (" .. names.KRC .. "+1)")
  add("local " .. names.VHF .. "=" .. names.H .. "[" .. names.VHI .. "]")
  -- Fail closed on every dispatched handler: an unknown opcode, a changed
  -- live entry or a coupled live/backup replacement is rejected immediately.
  -- The independent anchor is populated after all definitions and before the
  -- program enters the VM loop.  It is an in-process tripwire, not a secret.
  if ig and names.IPIN then
    add("if " .. names.VHF .. "==nil or " .. names.VHF .. "~=" ..
      names.HB .. "[" .. names.VHI .. "] or " .. names.VHF .. "~=" ..
      names.IPIN .. "[" .. names.VHI .. "] then " .. names.KS .. "() end")
  else
    add("if " .. names.VHF .. "==nil then " .. names.KS .. "() end")
  end
  -- Sampled dispatch guard. The tick audits a rotating slice; between ticks a
  -- swapped handler table would still be callable. The checkpoint's primary
  -- sample key is compared on every dispatch instead: one integer compare, no
  -- modulo, and a hit raises the same error the tick uses. The key is a
  -- baked literal that changes per build and per seed.
  local guard = nil
  if ig and names.HB and ig.fail and ig.probe then
    guard = "if " .. names.VHI .. "==" .. ig.probe .. " and " .. names.VHF ..
      "~=" .. names.HB .. "[" .. ig.probe .. "] then " .. ig.fail .. " end "
    add(guard)
    ig.dispatchGuard = true
  end
  add("local " .. names.VNPC .. "=" .. names.VHF .. "(" .. frameSig .. ")")
  -- RETURN supplies packed results and false. TAILCALL supplies a register
  -- index and nil so the interpreter itself can make a proper Lua tail call.
  add("if not " .. names.VNPC .. " then local " .. names.VZ .. "=" ..
    names.VS .. "." .. names.SRET ..
    " if " .. names.VNPC .. "==nil then return " .. names.VR .. "[" ..
    names.VZ .. "](" .. names.SU .. "(" .. names.VR .. "," .. names.VZ ..
    "+1," .. names.VS .. "." .. names.STOP .. "-1)) end return " ..
    names.SU .. "(" .. names.VZ .. ",1," .. names.VZ .. ".n) end")
  if ig then
    -- Validate the branch target as soon as the handler returns. The next
    -- iteration repeats the guard before dereferencing the instruction table.
    add("if " .. names.G4 .. "(" .. names.VNPC .. ")~=\"number\" or " ..
      names.VNPC .. "~=" .. names.VNPC .. " or " .. names.VNPC .. "<1 or " ..
      names.VNPC .. ">" .. names.IG .. "[" .. names.VPI .. "] or " ..
      names.VNPC .. "%1~=0 then " .. names.KS .. "() end")
  end
  add(names.VPC .. "=" .. names.VNPC)
  if loopShape == 1 then add("until false") else add("end") end
  add("end")

  local entries = {}
  local bodyVar, bodyField = makeBodyMaps(names, plan.seed or VMGen.DEFAULT_SEED)
  for i = 1, #(plan.activeOps or Compiler.OPS) do
    local name = (plan.activeOps or Compiler.OPS)[i]
    local keys = plan.opkeys[name]
    local bodies = VARIANTS[name] or { HANDLERS[name] }
    local variants = {}
    for j = 1, #bodies do variants[j] = bodies[j] end
    shuffle(variants, rng)
    for j = 1, #keys do
      local base = variants[(j - 1) % #variants + 1]
      if name == "CLOSURE" and ig then
        base = "if not $PMH(b) then $KS() end " .. base
      end
      if not base:find("return", 1, true) then base = base .. " return pc+1" end
      local code = substitute(wrapBody(base, rng), names)
      entries[#entries + 1] = {
        num = keyNum(keys[j]), code = code, layout = plan.layouts[keys[j]],
        mask = plan.operandMasks[keys[j]],
      }
    end
  end
  -- Decoys are reachable only from corrupted bytecode, so every branch that
  -- mutates state is behind a predicate that cannot hold for a numeric
  -- operand. They still carry the same per-key layout and mask as a real
  -- handler, so a dumped table has no entry that is visibly "the inert kind".
  for i = 1, #plan.decoys do
    local code
    if rng(3) == 1 then
      code = DECOYS[rng(#DECOYS)]
      if rng(2) == 1 then code = DECOY_PREFIX[rng(#DECOY_PREFIX)] .. code end
    else
      code = synthDecoy(rng)
      if rng(3) == 1 then code = DECOY_PREFIX[rng(#DECOY_PREFIX)] .. code end
    end
    if rng(4) == 1 then code = wrapBody(code, rng) end
    local perm = { 2, 3, 4 }
    for j = 3, 2, -1 do
      local m = rng(j)
      perm[j], perm[m] = perm[m], perm[j]
    end
    local mask = { signs = { 1, 1, 1, 1 }, biases = { 0, 0, 0, 0 } }
    for j = 1, 3 do
      mask.signs[j] = rng(2) == 1 and 1 or -1
      mask.biases[j] = rng(4095)
    end
    entries[#entries + 1] = {
      num = keyNum(plan.decoys[i]), code = code,
      layout = { perm[1], perm[2], perm[3], 5 }, mask = mask,
    }
  end
  shuffle(entries, rng)
  for i = 1, #entries do
    local entry = entries[i]
    local operands = {}
    local dynamic = entry.mask.pc
    local biasVar = "_gsxpc"
    for j = 1, 4 do
      local slot = entry.layout[j]
      local value = names.VI .. "[" .. slot .. "]"
      local bias = entry.mask.biases[j]
      if dynamic and j <= 3 then
        -- Decode x*sign + staticBias + pcBias without changing operand order.
        local shift = bias == 0 and biasVar or (bias .. "+" .. biasVar)
        if entry.mask.signs[j] == 1 then
          value = value .. "-(" .. shift .. ")"
        else
          value = "(" .. shift .. ")-" .. value
        end
      elseif bias == 0 then
        if entry.mask.signs[j] ~= 1 then value = "0-" .. value end
      elseif entry.mask.signs[j] == 1 then
        value = value .. "-" .. bias
      else
        value = bias .. "-" .. value
      end
      operands[j] = value
    end
    local dynamicInit = dynamic and ("local " .. biasVar .. "=(" ..
      names.VPC .. "*" .. dynamic.mul .. "+" .. dynamic.salt .. "+" ..
      names.VS .. "." .. names.SPID .. "*" .. dynamic.protoMul .. ")%" ..
      dynamic.mod .. " ") or ""
    add(names.H .. "[" .. entry.num .. "]=function(" .. frameSig .. ") " ..
      dynamicInit .. "local " .. names.A .. "," .. names.B .. "," .. names.C ..
      "," .. names.D .. "=" .. table.concat(operands, ",") .. " " ..
      renameBody(saltBody(entry.code, entry.num, rng), bodyVar, bodyField) .. " end")
  end
  add(names.HB .. "={} for k,v in " .. names.G6 .. "(" .. names.H .. ") do " ..
    names.HB .. "[k]=v end")
  -- Independently pin ALL registered dispatch slots. The previous six
  -- anchors covered only checkpoint samples; a coupled H/HB edit to a decoy
  -- or an unsampled opcode could survive the one-shot audit.  This third
  -- reference map is checked on dispatch and by the rotating full-table scan.
  -- Host-side upvalue/table access can still change all three; this is not
  -- a cryptographic trust boundary.
  if ig and ig.pinCount and ig.pinCount > 0 then
    local refs = {}
    for i = 1, #ig.ring do
      local key = ig.ring[i]
      refs[i] = "[" .. key .. "]=" .. names.H .. "[" .. key .. "]"
    end
    add(names.IPIN .. "={" .. table.concat(refs, ",") .. "}")
  end
  -- Mutation tripwires, NOT a portable Lua read-only guarantee: __newindex
  -- catches only normal additions, not assignments to existing slots or rawset.
  -- Those changes are covered by the independent reference audits and the
  -- prototype metadata checks.  Luau table.freeze is used when available to
  -- actually reject existing-key assignments and rawset on root tables.
  -- Lazy constant pools retain their special __index decoder metatable.
  local guard =
    names.G3 .. "(function() local SM=" .. names.G9 ..
    " if " .. names.G4 .. "(SM)~=\"function\" then return end local GM={[" ..
    dms("__metatable") .. "]=false,[" .. dms("__newindex") ..
    "]=function() " .. names.KS .. "() end} SM(" .. names.P .. ",GM) SM(" .. names.H .. ",GM) SM(" ..
    names.HB .. ",GM) for i=1,#" .. names.P .. " do local kt=" .. names.P ..
    "[i]." .. names.PKK .. " if " .. names.G4 .. "(kt)==\"table\" then " ..
    names.G3 .. "(" .. names.G9 .. ",kt,GM) end end if " .. names.G4 .. "(" ..
    names.G7 .. ")==\"function\" then " .. names.IM .. "=1 end end)"
  if ig and ig.pinCount and ig.pinCount > 0 then
    -- The third reference set is protected by the same read-only sentinel.
    guard = guard:gsub(" for i=1,#", " " .. names.G9 .. "(" .. names.IPIN ..
      ",GM) for i=1,#", 1)
  end
  add(guard)
  -- Luau only: table.freeze prevents both existing-key writes and rawset on
  -- the four root tables. Standard Lua has no equivalent primitive; its
  -- integrity policy is detect-and-fail rather than immutable tables.
  if ig then
    add("do local fr=" .. names.G2 .. " and " .. names.G2 .. ".freeze " ..
      "if " .. names.G4 .. "(fr)==\"function\" then " ..
      names.G3 .. "(fr," .. names.P .. ") " ..
      names.G3 .. "(fr," .. names.H .. ") " ..
      names.G3 .. "(fr," .. names.HB .. ") " ..
      ((ig.pinCount or 0) > 0 and
        (names.G3 .. "(fr," .. names.IPIN .. ") ") or "") ..
      "end end")
  end

  -- V0.5 security regression: a short-lived chunk may execute fewer than
  -- `period` dispatches, so a purely periodic integrity check might never
  -- run. Perform one complete checkpoint (including the initial full H/HB/
  -- IPIN audit and canary check) before any protected instruction executes.
  -- The regular rolling checkpoints remain enabled after this preflight.
  if ig then
    add(names.II .. "=" .. names.IP .. "-1")
    add(Integrity.loop(names, ig))
  end

  add(names.F .. "=function(" .. names.VPI .. "," .. names.VU ..
    ") return function(...) return " .. names.X .. "(" .. names.VPI .. "," ..
    names.VU .. ",...) end end")
  add("local " .. names.W .. "=" .. names.F .. "(1,{})")
  add("return " .. names.W .. "(...)")

  -- Every emitted statement is complete, so the whole chunk can be glued with
  -- single spaces into one line: fewer structural anchors for a decompiler.
  -- The chunk opens with a parameter wall around a nested entry function, and
  -- the host varargs are forwarded through both calls unchanged.
  local source = "return(function(" .. wallText .. ",...)" .. wall[#wall] ..
    "={};return (function(...)" .. table.concat(lines, " ") ..
    "end)(...)end)(" .. wallText .. ",...)"
  local realKeys = {}
  local emittedOps = plan.activeOps or Compiler.OPS
  for i = 1, #emittedOps do
    local keys = plan.opkeys[emittedOps[i]]
    for j = 1, #keys do realKeys[#realKeys + 1] = keys[j] end
  end
  local instructionCount, smProtos, smBlocks, smBytes, smCap = 0, 0, 0, 0, 0
  for pi = 1, #plan.protos do
    local P = plan.protos[pi]
    if P.sm then
      instructionCount = instructionCount + (P.total or 0)
      smProtos = smProtos + 1
      smBlocks = smBlocks + #P.blocks
      for i = 1, #P.blocks do smBytes = smBytes + #P.blocks[i] end
      if (P.cap or 0) > smCap then smCap = P.cap end
    else
      instructionCount = instructionCount + #P.c
    end
  end

  return source, {
    bytes = #source + 1,
    protos = #plan.protos,
    instructions = instructionCount,
    opcodes = #emittedOps,
    isaOpcodes = #Compiler.OPS,
    prunedOpcodes = #Compiler.OPS - #emittedOps,
    aliases = #realKeys - #emittedOps,
    decoys = plan.decoyCount,
    keys = #realKeys + plan.decoyCount,
    map = plan.opnum,
    opkeys = plan.opkeys,
    layouts = plan.layouts,
    operandMasks = plan.operandMasks,
    realKeys = realKeys,
    decoyKeys = plan.decoys,
    names = names,
    packed = payload ~= nil,
    payloadBytes = payload and payload.blobBytes or nil,
    plainBytes = payload and payload.plainBytes or nil,
    payloadSection = opts.recordSection and payloadSection or nil,
    keyMul = kMul, keyBias = kBias, slots = plan.slots,
    key = payload and payload.key or nil,
    selfmod = smProtos > 0,
    selfmodProtos = smProtos,
    selfmodBlocks = smBlocks,
    selfmodBytes = smBytes,
    liveCap = smCap,
    antidebug = ad ~= nil,
    antidebugProbes = ad and #ad.probes or 0,
    antidebugMask = ad and ad.mask or 0,
    antidebugThreshold = ad and ad.threshold or 0,
    envlog = el ~= nil,
    integrity = ig ~= nil,
    integrityPeriod = ig and ig.period or 0,
    integrityCanaryLen = ig and ig.canaryLen or 0,
    integrityProbe = ig and ig.probe or 0,
    integritySalt = ig and ig.salt or 0,
    integrityExpect = ig and ig.expect or 0,
    integrityCanary = ig and ig.canary or nil,
    integrityCanaries = ig and ig.count or 0,
    integrityCheckpoints = ig and ig.checkpointCount or 0,
    integrityAuditTotal = ig and ig.total or 0,
    integrityPinned = ig and ig.pinCount or 0,
    integrityProtoLens = ig and ig.protoLens or nil,
    integrityProtoModes = ig and ig.protoModes or nil,
    integrityCanaryParts = ig and ig.canaryParts or nil,
    envChaff = envChaff,
    identityChecks = ig and ig.snapshotChecks or 0,
    identityExtra = ig and ig.extraChecks or 0,
    identityRotationGroups = ig and ig.snapshotRotationGroups or 0,
    dispatchGuard = (ig and ig.dispatchGuard) or false,
    tamperProbes = tamperProbes,
  }
end

function VMGen.generate(compiled, opts)
  local plan = VMGen.randomize(compiled, opts)
  return VMGen.emit(plan, opts)
end

return VMGen
