-- compiler.lua -- compiles a resolved AST into a custom stack/register bytecode.
-- Registers are 1-based. Captured locals live in one-element cell tables so
-- that closures share variables exactly like real Lua upvalues.
local U = require("src.util")
local Compiler = {}

local function isMultiExpr(e)
  return e and (e.t == "Call" or e.t == "Vararg")
end

function Compiler.compile(resolved, opts)
  opts = opts or {}
  local state = {
    protos = {},
    strings = {},
    stringMap = {},
    opts = opts,
    errors = {},
  }

  local function strIndex(s)
    local idx = state.stringMap[s]
    if not idx then
      idx = #state.strings + 1
      state.strings[idx] = s
      state.stringMap[s] = idx
    end
    return idx
  end

  local function newProto(fn)
    local P = {
      code = {}, k = {}, kmap = {},
      params = #fn.params,
      vararg = fn.vararg and true or false,
      maxstack = 0,
      name = fn.name,
      updesc = {},
    }
    state.protos[#state.protos + 1] = P
    fn.protoIndex = #state.protos
    return P
  end

  local compileFunction

  local function compileProtoBody(fn)
    local P = newProto(fn)
    local ctx = {
      P = P, fn = fn,
      top = 1, max = 1,
      loops = {},
      labelObjects = {},
      pendingGotos = {},
    }

    local function emit(op, a, b, c, d)
      local inst = { op = op, a = a or 0, b = b or 0, c = c or 0, d = d or 0 }
      P.code[#P.code + 1] = inst
      return inst, #P.code
    end
    ctx.emit = emit

    local function alloc(n)
      n = n or 1
      local base = ctx.top
      ctx.top = ctx.top + n
      if ctx.top - 1 > ctx.max then ctx.max = ctx.top - 1 end
      return base
    end
    local function freeTo(mark) ctx.top = mark end
    ctx.alloc = alloc
    ctx.freeTo = freeTo

    local function newLabel() return { pc = nil, jumps = {} } end
    local function markLabel(lab) lab.pc = #P.code + 1 end
    local function jump(op, reg, lab)
      local inst = emit(op, reg or 0)
      inst.target = lab
      inst.tfield = "b"
      lab.jumps[#lab.jumps + 1] = inst
      return inst
    end
    ctx.newLabel = newLabel
    ctx.mark = markLabel
    ctx.jump = jump

    local function kIndex(v)
      local key
      if type(v) == "number" then
        if v ~= v then return nil end
        key = "n" .. U.formatNumber(v) .. ":" .. tostring(1 / v > 0)
      elseif type(v) == "boolean" then
        key = "b" .. tostring(v)
      else
        return nil
      end
      local idx = P.kmap[key]
      if idx then return idx end
      idx = #P.k + 1
      P.k[idx] = v
      P.kmap[key] = idx
      return idx
    end
    ctx.kIndex = kIndex

    local function getLocal(dest, binding)
      if binding.captured then
        emit("CELLGET", dest, binding.slot)
      else
        emit("MOVE", dest, binding.slot)
      end
    end

    local function setLocal(binding, src)
      if binding.captured then
        emit("CELLSET", src, binding.slot)
      else
        emit("MOVE", binding.slot, src)
      end
    end

    local function setTarget(target, src)
      if target.t == "Name" then
        local b = target.binding
        if b then
          if b.kind == "upval" then
            emit("SETUPVAL", src, b.idx)
          else
            setLocal(b, src)
          end
        else
          emit("SETGLOBAL", src, strIndex(target.v))
        end
      else
        local tg = target._cg
        if target.key.t == "String" then
          emit("SETFIELD", tg.obj, src, strIndex(target.key.v))
        else
          emit("SETTABLE", tg.obj, tg.key, src)
        end
      end
    end

    local compileExpr, compileExprMulti, compileCall, compileTable, compileStmt, compileBlock

    compileExpr = function(e, dest)
      local mark = ctx.top
      local t = e.t
      if t == "Nil" then
        emit("LOADNIL", dest)
      elseif t == "True" then
        emit("LOADBOOL", dest, 1)
      elseif t == "False" then
        emit("LOADBOOL", dest, 0)
      elseif t == "Number" then
        local ki = kIndex(e.v)
        if ki then emit("LOADK", dest, ki) else emit("LOADNIL", dest) end
      elseif t == "String" then
        emit("LOADSTR", dest, strIndex(e.v))
      elseif t == "Vararg" then
        emit("VARARG", dest, 1)
      elseif t == "Name" then
        local b = e.binding
        if b then
          if b.kind == "upval" then
            emit("GETUPVAL", dest, b.idx)
          else
            getLocal(dest, b)
          end
        else
          emit("GETGLOBAL", dest, strIndex(e.v))
        end
      elseif t == "Paren" then
        compileExpr(e.e, dest)
      elseif t == "Un" then
        compileExpr(e.e, dest)
        if e.op == "-" then emit("UNM", dest, dest)
        elseif e.op == "not" then emit("NOT", dest, dest)
        elseif e.op == "#" then emit("LEN", dest, dest)
        elseif e.op == "~" then emit("BNOT", dest, dest)
        else error({ __compile = true, msg = "unsupported unary operator " .. e.op, node = e }) end
      elseif t == "Bin" then
        if e.op == "and" then
          local lab = newLabel()
          compileExpr(e.l, dest)
          jump("JMPF", dest, lab)
          compileExpr(e.r, dest)
          markLabel(lab)
        elseif e.op == "or" then
          local lab = newLabel()
          compileExpr(e.l, dest)
          jump("JMPT", dest, lab)
          compileExpr(e.r, dest)
          markLabel(lab)
        else
          compileExpr(e.l, dest)
          local rt = alloc(1)
          compileExpr(e.r, rt)
          local opmap = {
            ["+"] = "ADD", ["-"] = "SUB", ["*"] = "MUL", ["/"] = "DIV",
            ["%"] = "MOD", ["^"] = "POW", ["//"] = "IDIV", [".."] = "CONCAT",
            ["=="] = "EQ", ["~="] = "NE", ["<"] = "LT", ["<="] = "LE",
            [">"] = "GT", [">="] = "GE",
            ["&"] = "BAND", ["|"] = "BOR", ["~"] = "BXOR", ["<<"] = "SHL", [">>"] = "SHR",
          }
          local op = opmap[e.op]
          if not op then error({ __compile = true, msg = "unsupported binary operator " .. tostring(e.op), node = e }) end
          emit(op, dest, dest, rt)
        end
      elseif t == "Index" then
        compileExpr(e.obj, dest)
        if e.key.t == "String" then
          emit("GETFIELD", dest, dest, strIndex(e.key.v))
        else
          local kt = alloc(1)
          compileExpr(e.key, kt)
          emit("GETTABLE", dest, dest, kt)
        end
      elseif t == "Call" then
        compileCall(e, dest, 1)
      elseif t == "Func" then
        local child = compileFunction(e)
        emit("CLOSURE", dest, child)
      elseif t == "Table" then
        compileTable(e, dest)
      elseif t == "IfExpr" then
        local endLab = newLabel()
        for i = 1, #e.branches do
          local br = e.branches[i]
          local nextLab = newLabel()
          local ct = alloc(1)
          compileExpr(br.cond, ct)
          jump("JMPF", ct, nextLab)
          compileExpr(br.value, dest)
          jump("JMP", nil, endLab)
          markLabel(nextLab)
        end
        compileExpr(e.orelse, dest)
        markLabel(endLab)
      else
        error({ __compile = true, msg = "unsupported expression node '" .. tostring(t) .. "'", node = e })
      end
      freeTo(mark)
    end

    compileExprMulti = function(e, base, want)
      if isMultiExpr(e) then
        if e.t == "Call" then
          compileCall(e, base, want)
        else
          emit("VARARG", base, want)
        end
      else
        if want == 0 then
          -- Evaluate for side effects only.
          local tmp = alloc(1)
          compileExpr(e, tmp)
        else
          compileExpr(e, base)
        end
      end
    end

    compileCall = function(e, dest, want)
      local mark = ctx.top
      local nargs = #e.args
      if e.method then
        local base = alloc(2 + nargs)
        compileExpr(e.fn, base)
        emit("SELF", base, base, strIndex(e.method))
        local lastMulti = nargs > 0 and isMultiExpr(e.args[nargs])
        if nargs > 0 then
          for i = 1, nargs - 1 do compileExpr(e.args[i], base + 1 + i) end
          if lastMulti then
            compileExprMulti(e.args[nargs], base + 1 + nargs, -1)
            emit("CALL", base, -1, want, dest)
          else
            compileExpr(e.args[nargs], base + 1 + nargs)
            emit("CALL", base, 1 + nargs, want, dest)
          end
        else
          emit("CALL", base, 1, want, dest)
        end
      else
        local base = alloc(1 + nargs)
        compileExpr(e.fn, base)
        local lastMulti = nargs > 0 and isMultiExpr(e.args[nargs])
        if nargs > 0 then
          for i = 1, nargs - 1 do compileExpr(e.args[i], base + i) end
          if lastMulti then
            compileExprMulti(e.args[nargs], base + nargs, -1)
            emit("CALL", base, -1, want, dest)
          else
            compileExpr(e.args[nargs], base + nargs)
            emit("CALL", base, nargs, want, dest)
          end
        else
          emit("CALL", base, 0, want, dest)
        end
      end
      freeTo(mark)
    end

    compileTable = function(e, dest)
      local mark = ctx.top
      emit("NEWTABLE", dest)
      local arrayIdx = 1
      for i = 1, #e.fields do
        local f = e.fields[i]
        if f.kind == "array" then
          local isLast = (i == #e.fields)
          if isLast and isMultiExpr(f.value) then
            local base = alloc(1)
            compileExprMulti(f.value, base, -1)
            emit("SETLIST", dest, -1, base, arrayIdx)
          else
            local vt = alloc(1)
            compileExpr(f.value, vt)
            emit("SETIDX", dest, arrayIdx, vt)
          end
          arrayIdx = arrayIdx + 1
        elseif f.kind == "name" then
          local vt = alloc(1)
          compileExpr(f.value, vt)
          emit("SETFIELD", dest, vt, strIndex(f.key.v))
        else
          if f.key.t == "String" then
            local vt = alloc(1)
            compileExpr(f.value, vt)
            emit("SETFIELD", dest, vt, strIndex(f.key.v))
          else
            local kt = alloc(1)
            compileExpr(f.key, kt)
            local vt = alloc(1)
            compileExpr(f.value, vt)
            emit("SETTABLE", dest, kt, vt)
          end
        end
      end
      freeTo(mark)
    end

    local function assignFromRHS(targets, exprs)
      local mark = ctx.top
      -- Pre-evaluate indexed targets (Lua evaluates lvalues before values).
      for i = 1, #targets do
        local tg = targets[i]
        if tg.t == "Index" then
          local obj = alloc(1)
          compileExpr(tg.obj, obj)
          local key
          if tg.key.t == "String" then
            key = nil
          else
            key = alloc(1)
            compileExpr(tg.key, key)
          end
          tg._cg = { obj = obj, key = key }
        end
      end
      local n = #targets
      local ne = #exprs
      local lastMulti = ne > 0 and isMultiExpr(exprs[ne])
      if ne > 0 then
        local blockSize = math.max(n, ne)
        local base = alloc(blockSize)
        for i = 1, ne - 1 do
          compileExpr(exprs[i], base + i - 1)
        end
        if ne <= n then
          if lastMulti then
            compileExprMulti(exprs[ne], base + ne - 1, n - (ne - 1))
          else
            compileExpr(exprs[ne], base + ne - 1)
          end
        else
          if lastMulti then
            compileExprMulti(exprs[ne], base + ne - 1, 0)
          else
            compileExpr(exprs[ne], base + ne - 1)
          end
        end
        -- A trailing call/vararg fills the remaining targets; individual
        -- expressions only fill their own slot.
        local produced = ne
        if lastMulti and ne <= n then produced = n end
        for i = 1, n do
          if i <= produced then
            setTarget(targets[i], base + i - 1)
          else
            local nt = alloc(1)
            emit("LOADNIL", nt)
            setTarget(targets[i], nt)
          end
        end      else
        for i = 1, n do
          local nt = alloc(1)
          emit("LOADNIL", nt)
          setTarget(targets[i], nt)
        end
      end
      freeTo(mark)
    end

    local function makeDeclarations(names, exprs)
      local n = #names
      local mark = ctx.top
      local base = alloc(n)
      local ne = #exprs
      if ne > 0 then
        local valBase = alloc(math.max(n, ne))
        local lastMulti = isMultiExpr(exprs[ne])
        for i = 1, ne - 1 do compileExpr(exprs[i], valBase + i - 1) end
        if ne <= n then
          if lastMulti then
            compileExprMulti(exprs[ne], valBase + ne - 1, n - (ne - 1))
          else
            compileExpr(exprs[ne], valBase + ne - 1)
          end
        else
          if lastMulti then
            compileExprMulti(exprs[ne], valBase + ne - 1, 0)
          else
            compileExpr(exprs[ne], valBase + ne - 1)
          end
        end
        local produced = ne
        if lastMulti and ne <= n then produced = n end
        for i = 1, n do
          if i <= produced then
            local b = names[i]
            b.slot = base + i - 1
            if b.captured then
              emit("MOVE", b.slot, valBase + i - 1)
              emit("CELLINIT", b.slot)
            else
              emit("MOVE", b.slot, valBase + i - 1)
            end
          else
            local b = names[i]
            b.slot = base + i - 1
            emit("LOADNIL", b.slot)
            if b.captured then emit("CELLINIT", b.slot) end
          end
        end
      else
        for i = 1, n do
          local b = names[i]
          b.slot = base + i - 1
          emit("LOADNIL", b.slot)
          if b.captured then emit("CELLINIT", b.slot) end
        end
      end
      freeTo(base + n)
      return base
    end

    local function emitCondFalse(reg, lab)
      if U.chance(35) then
        emit("JMPT", reg, 1)
        jump("JMP", nil, lab)
      else
        jump("JMPF", reg, lab)
      end
    end
    compileStmt = function(st)
      local t = st.t
      if t == "Local" then
        makeDeclarations(st.bindings, st.exprs)
      elseif t == "Assign" then
        assignFromRHS(st.targets, st.exprs)
      elseif t == "CallStat" then
        local mark = ctx.top
        compileCall(st.call, 0, 0)
        freeTo(mark)
      elseif t == "LocalFunction" then
        local b = st.binding
        local slot = alloc(1)
        b.slot = slot
        if b.captured then
          emit("CELLINIT", slot)
          local tmp = alloc(1)
          local child = compileFunction(st.func)
          emit("CLOSURE", tmp, child)
          emit("CELLSET", tmp, slot)
        else
          local child = compileFunction(st.func)
          emit("CLOSURE", slot, child)
        end
        ctx.top = slot + 1
      elseif t == "FunctionStat" then
        local mark = ctx.top
        local tg = st.target
        local pre
        if tg.t == "Index" then
          local obj = alloc(1)
          compileExpr(tg.obj, obj)
          local key
          if tg.key.t ~= "String" then
            key = alloc(1)
            compileExpr(tg.key, key)
          end
          pre = { obj = obj, key = key }
        end
        local tmp = alloc(1)
        local child = compileFunction(st.func)
        emit("CLOSURE", tmp, child)
        if tg.t == "Name" then
          setTarget(tg, tmp)
        else
          if tg.key.t == "String" then
            emit("SETFIELD", pre.obj, tmp, strIndex(tg.key.v))
          else
            emit("SETTABLE", pre.obj, pre.key, tmp)
          end
        end
        freeTo(mark)
      elseif t == "Do" then
        compileBlock(st.block)
      elseif t == "If" then
        local endLab = newLabel()
        for i = 1, #st.branches do
          local br = st.branches[i]
          local mark = ctx.top
          local ct = alloc(1)
          compileExpr(br.cond, ct)
          local nextLab = newLabel()
          emitCondFalse(ct, nextLab)
          freeTo(mark)
          compileBlock(br.block)
          jump("JMP", nil, endLab)
          markLabel(nextLab)
        end
        if st.orelse then compileBlock(st.orelse) end
        markLabel(endLab)
      elseif t == "While" then
        local mark = ctx.top
        local startLab = newLabel()
        local breakLab = newLabel()
        markLabel(startLab)
        local ct = alloc(1)
        compileExpr(st.cond, ct)
        emitCondFalse(ct, breakLab)
        freeTo(mark)
        local loop = { breaks = {}, contLabel = startLab, breakLabel = breakLab }
        ctx.loops[#ctx.loops + 1] = loop
        compileBlock(st.block)
        ctx.loops[#ctx.loops] = nil
        jump("JMP", nil, startLab)
        markLabel(breakLab)
        freeTo(mark)
      elseif t == "Repeat" then
        local startLab = newLabel()
        local breakLab = newLabel()
        local condLab = newLabel()
        local markTop = ctx.top
        markLabel(startLab)
        local loop = { breaks = {}, contLabel = condLab, breakLabel = breakLab }
        ctx.loops[#ctx.loops + 1] = loop
        -- The until-condition sees the body's locals, so their registers must
        -- stay reserved while the condition is compiled.
        compileBlock(st.block, true)
        ctx.loops[#ctx.loops] = nil
        markLabel(condLab)
        local ct = alloc(1)
        compileExpr(st.cond, ct)
        ctx.top = markTop
        jump("JMPF", ct, startLab)
        markLabel(breakLab)
      elseif t == "NumFor" then
        local mark = ctx.top
        local base = alloc(4)
        compileExpr(st.from, base)
        compileExpr(st.to, base + 1)
        if st.step then compileExpr(st.step, base + 2) else emit("LOADK", base + 2, kIndex(1)) end
        local bodyLab = newLabel()
        local breakLab = newLabel()
        local skipLab = newLabel()
        local prep = emit("FORPREP", base, 0, st.binding.captured and 1 or 0)
        prep.target = skipLab
        prep.tfield = "b"
        markLabel(bodyLab)
        st.binding.slot = base + 3
        local loop = { breaks = {}, contLabel = newLabel(), breakLabel = breakLab }
        ctx.loops[#ctx.loops + 1] = loop
        compileBlock(st.block)
        ctx.loops[#ctx.loops] = nil
        markLabel(loop.contLabel)
        local loopInst = emit("FORLOOP", base, 0, st.binding.captured and 1 or 0)
        loopInst.target = bodyLab
        loopInst.tfield = "b"
        markLabel(skipLab)
        markLabel(breakLab)
        freeTo(mark)
      elseif t == "GenFor" then
        local mark = ctx.top
        local nvars = #st.names
        local base = alloc(3 + nvars)
        local ne = #st.exprs
        local tmp = alloc(math.max(3, ne))
        local lastMulti = ne > 0 and isMultiExpr(st.exprs[ne])
        for i = 1, ne do
          if i == ne and lastMulti then
            local want = 0
            if ne <= 3 then want = 3 - (ne - 1) end
            compileExprMulti(st.exprs[ne], tmp + i - 1, want)
          elseif i <= 3 then
            compileExpr(st.exprs[i], tmp + i - 1)
          else
            local extra = alloc(1)
            compileExpr(st.exprs[i], extra)
            freeTo(tmp + math.max(3, ne))
          end
        end
        if not lastMulti then
          for i = ne + 1, 3 do emit("LOADNIL", tmp + i - 1) end
        end
        for i = 1, 3 do emit("MOVE", base + i - 1, tmp + i - 1) end
        freeTo(base + 3 + nvars)
        local callLab = newLabel()
        local bodyLab = newLabel()
        local breakLab = newLabel()
        local afterLab = newLabel()
        markLabel(callLab)
        emit("TFORCALL", base, nvars)
        local tl = emit("TFORLOOP", base, nvars, 0)
        tl.target = bodyLab
        tl.tfield = "c"
        jump("JMP", nil, afterLab)
        markLabel(bodyLab)
        for i = 1, nvars do
          local b = st.bindings[i]
          b.slot = base + 3 + i - 1
          if b.captured then emit("CELLINIT", b.slot) end
        end
        local loop = { breaks = {}, contLabel = callLab, breakLabel = breakLab }
        ctx.loops[#ctx.loops + 1] = loop
        compileBlock(st.block)
        ctx.loops[#ctx.loops] = nil
        jump("JMP", nil, callLab)
        markLabel(afterLab)
        markLabel(breakLab)
        freeTo(mark)
      elseif t == "Return" then
        local mark = ctx.top
        local ne = #st.exprs
        if ne == 0 then
          emit("RETURN", 0, 0)
        else
          local base = alloc(ne)
          local lastMulti = isMultiExpr(st.exprs[ne])
          for i = 1, ne - 1 do compileExpr(st.exprs[i], base + i - 1) end
          if lastMulti then
            compileExprMulti(st.exprs[ne], base + ne - 1, -1)
            emit("RETURN", base, -1)
          else
            compileExpr(st.exprs[ne], base + ne - 1)
            emit("RETURN", base, ne)
          end
        end
        freeTo(mark)
      elseif t == "Break" then
        local loop = ctx.loops[#ctx.loops]
        if loop then jump("JMP", nil, loop.breakLabel) end
      elseif t == "Continue" then
        local loop = ctx.loops[#ctx.loops]
        if loop then jump("JMP", nil, loop.contLabel) end
      elseif t == "Label" then
        local lab = ctx.labelObjects[st]
        if not lab then lab = newLabel(); ctx.labelObjects[st] = lab end
        markLabel(lab)
      elseif t == "Goto" then
        local tar = st.labelObj
        if tar then
          local lab = ctx.labelObjects[tar]
          if not lab then lab = newLabel(); ctx.labelObjects[tar] = lab end
          jump("JMP", nil, lab)
        end
      else
        error({ __compile = true, msg = "unsupported statement node '" .. tostring(t) .. "'", node = st })
      end
    end

    compileBlock = function(block, keepTop)
      local mark = ctx.top
      for i = 1, #block do
        if block[i] then
          compileStmt(block[i])
          if U.chance(5) then emit("NOP") end
        end
      end
      if not keepTop then ctx.top = mark end
    end

    -- Parameter registers and captured-parameter cells.
    for i = 1, #fn.params do
      local b = fn.paramBindings[i]
      b.slot = i
      ctx.top = i + 1
      if ctx.top - 1 > ctx.max then ctx.max = ctx.top - 1 end
      if b.captured then emit("CELLINIT", i) end
    end
    if #fn.params > 0 then ctx.top = #fn.params + 1 end

    compileBlock(fn.body)
    emit("RETURN", 0, 0)
    P.maxstack = ctx.max

    -- Resolve label offsets.
    local function patchField(inst, field)
      local lab = inst.target
      if not lab or lab.pc == nil then
        error({ __compile = true, msg = "unresolved jump target", node = fn })
      end
      inst[field] = lab.pc - ((inst._pc or 0) + 1)
    end
    for pc = 1, #P.code do
      local inst = P.code[pc]
      inst._pc = pc - 1
      if inst.target then
        local lab = inst.target
        if lab.pc == nil then
          error({ __compile = true, msg = "unresolved jump target", node = fn })
        end
        inst[inst.tfield] = lab.pc - pc - 1
      end
    end
    for pc = 1, #P.code do P.code[pc]._pc = nil end
    return P
  end

  compileFunction = function(fn)
    local P = compileProtoBody(fn)
    -- Upvalue descriptors are relative to the enclosing function, so they are
    -- computed by the caller at CLOSURE emission time.
    if fn.info and fn.info.upvals then
      for i = 1, #fn.info.upvals do
        local entry = fn.info.upvals[i]
        if entry.instack then
          if not entry.binding.slot then
            error({ __compile = true, msg = "captured local has no register slot", node = fn })
          end
          P.updesc[i] = { 1, entry.binding.slot }
        else
          P.updesc[i] = { 0, entry.idx }
        end
      end
    end
    return fn.protoIndex
  end

  local started, compileErr = pcall(function()
    compileFunction(resolved.main)
  end)
  if not started then
    if type(compileErr) == "table" and compileErr.__compile then
      state.errors[#state.errors + 1] = {
        line = compileErr.node and compileErr.node.line or 0,
        col = compileErr.node and compileErr.node.col or 0,
        msg = compileErr.msg,
      }
    else
      error(compileErr, 0)
    end
  end

  -- Update upvalue descriptors after the whole program is compiled: slots are
  -- assigned during parent compilation, which always happens before a child
  -- closure instruction is emitted.
  for pi = 2, #state.protos do
    -- descriptors were set in compileFunction via fn.info; nothing to do here
  end

  return {
    protos = state.protos,
    strings = state.strings,
    errors = state.errors,
  }
end

return Compiler
