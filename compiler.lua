-- compiler.lua -- normalized AST -> register bytecode (layer 7).
--
-- Pipeline position:
--   scope -> consts -> flatten -> opaque -> strings -> compiler
--
-- The compiler always runs after M6, so the tree includes the synthetic
-- string-decoder binding. That binding is an ordinary `local x = (function ...)
-- (pool)` statement and is compiled like user code; M8 folds it into the VM
-- prototype tree, leaving no named decoder on the host.
--
-- Instruction format: { op = "NAME", a = n, b = n, c = n, d = n }.
-- Registers are 1-based; register 0 is never allocated. Field roles:
--
--   MOVE A B              R[A] = R[B]
--   LOADK A D             R[A] = K[D]            (any constant)
--   LOADINT A D           R[A] = D               (small integer)
--   LOADBOOL A B          R[A] = (B ~= 0)
--   LOADNIL A             R[A] = nil
--   LOADNILN A D          R[A .. A+D-1] = nil
--   GETUPVAL A B          R[A] = U[B][1]
--   SETUPVAL A B          U[B][1] = R[A]
--   NEWCELL A B           R[A] = { R[B] }        (B == 0 -> empty cell)
--   GETCELL A B           R[A] = R[B][1]
--   SETCELL A B           R[A][1] = R[B]
--   GETGLOBAL A D         R[A] = G[K[D]]
--   SETGLOBAL A D         G[K[D]] = R[A]
--   NEWTABLE A            R[A] = {}
--   GETTABLE A B C        R[A] = R[B][R[C]]
--   SETTABLE A B C        R[A][R[B]] = R[C]
--   GETFIELD A B D        R[A] = R[B][K[D]]
--   SETFIELD A B D        R[A][K[D]] = R[B]
--   SELF A B D            R[A+1] = R[B]; R[A] = R[B][K[D]]
--   SETLIST A B C D       R[A][B+i] = R[C+i], i = 0 .. D-1; D < 0 -> top-C
--   GETIDXI A B D         R[A] = R[B][D]
--   SETIDXI A B D         R[A][D] = R[B]
--   ADD..GE A B C         R[A] = R[B] <op> R[C]  (comparisons yield booleans)
--   BAND..SHR A B C       portable 53-bit arithmetic bit operations
--   UNM/NOT/LEN/BNOT A B  R[A] = <unary> R[B]
--   BOOL A B C            R[A] = truthy(R[B]) XOR (C ~= 0)
--   ADDK..IDIVK A B D     R[A] = R[B] <op> K[D]
--   ADDI..MODI A B D      R[A] = R[B] <op> D
--   EQK/NEK/LTK/LEK A B D R[A] = R[B] <op> K[D]
--   TEST A B              if truthy(R[B]) == (A ~= 0) then skip next
--   TESTSET A B C         same, and R[C] = R[B] when the test holds
--   TESTNIL A B           if R[B] == nil then skip next
--   JMP D                 pc = pc + 1 + D
--   JMPF A D / JMPT A D   conditional, same offset rule
--   FORPREP A D           R[A] = R[A] - R[A+2]; pc = pc + 1 + D
--   FORLOOP A D           step/limit test; pc = pc + 1 + D on stay
--   TFORCALL A B          call R[A](R[A+1], R[A+2]), B results to R[A+3..]
--   TFORLOOP A B D        if R[A+3] ~= nil then R[A+2] = R[A+3]; pc += 1 + D
--   CLOSE A               close barrier (cells own their storage)
--   NOP
--   SETTOP A              top = A
--   CALL A B C D          B args (B < 0 -> to top), C results (C < 0 -> all,
--                         C == 0 -> none), destination D (D == 0 -> A)
--   TAILCALL A B          return R[A](args)
--   RETURN A B            B results (B < 0 -> to top)
--   CLOSURE A B           R[A] = closure(protos[B])
--   VARARG A B            B varargs (B < 0 -> all, top = A + n)
--
-- Captured locals live in one-element cell tables: the register holds the
-- cell, reads use GETCELL and writes SETCELL. A closure receives the cells
-- themselves, so mutation is shared exactly like a Lua upvalue. Loop variables
-- captured by a closure get a fresh cell per iteration.
local Ast = require("src.ast")

local Compiler = {}

local OPS = {
  "MOVE", "LOADK", "LOADNIL", "LOADBOOL", "LOADINT", "LOADNILN",
  "GETUPVAL", "SETUPVAL", "NEWCELL", "GETCELL", "SETCELL",
  "GETGLOBAL", "SETGLOBAL",
  "NEWTABLE", "GETTABLE", "SETTABLE", "GETFIELD", "SETFIELD", "SELF",
  "SETLIST", "GETIDXI", "SETIDXI",
  "ADD", "SUB", "MUL", "DIV", "MOD", "POW", "IDIV", "UNM", "CONCAT",
  "BAND", "BOR", "BXOR", "BNOT", "SHL", "SHR",
  "LEN", "NOT", "BOOL",
  "EQ", "NE", "LT", "LE", "GT", "GE",
  "TEST", "TESTSET", "TESTNIL",
  "JMP", "JMPF", "JMPT", "FORPREP", "FORLOOP", "TFORCALL", "TFORLOOP",
  "CLOSE", "NOP", "SETTOP",
  "CALL", "TAILCALL", "RETURN", "CLOSURE", "VARARG",
  "ADDK", "SUBK", "MULK", "DIVK", "MODK", "POWK", "IDIVK",
  "ADDI", "SUBI", "MULI", "DIVI", "MODI",
  "EQK", "NEK", "LTK", "LEK",
}
Compiler.OPS = OPS
Compiler.OPCOUNT = #OPS

local OPSET = {}
for i = 1, #OPS do OPSET[OPS[i]] = i end

local BINOP = {
  ["+"] = "ADD", ["-"] = "SUB", ["*"] = "MUL", ["/"] = "DIV",
  ["%"] = "MOD", ["^"] = "POW", ["//"] = "IDIV", [".."] = "CONCAT",
  ["=="] = "EQ", ["~="] = "NE", ["<"] = "LT", ["<="] = "LE",
  [">"] = "GT", [">="] = "GE",
  ["&"] = "BAND", ["|"] = "BOR", ["~"] = "BXOR", ["<<"] = "SHL", [">>"] = "SHR",
}
local KOP = {
  ADD = "ADDK", SUB = "SUBK", MUL = "MULK", DIV = "DIVK", MOD = "MODK",
  POW = "POWK", IDIV = "IDIVK",
  EQ = "EQK", NE = "NEK", LT = "LTK", LE = "LEK",
}
local IOP = {
  ADD = "ADDI", SUB = "SUBI", MUL = "MULI", DIV = "DIVI", MOD = "MODI",
}
local UNOP = { ["-"] = "UNM", ["not"] = "NOT", ["#"] = "LEN", ["~"] = "BNOT" }

local function isMulti(e)
  return e ~= nil and (e.type == "Call" or e.type == "Vararg")
end

local function isIntImmediate(v)
  return type(v) == "number" and v == math.floor(v) and
    v >= -1073741824 and v <= 1073741824
end

local function numberKey(v)
  if math.type and math.type(v) == "integer" then
    return "i" .. tostring(v)
  end
  local tag = ""
  if v == 0 then tag = (1 / v > 0) and "+" or "-" end
  return "n" .. string.format("%.17g", v) .. tag
end

-- ------------------------------------------------------------------ prepare
-- Resolves every identifier with a name-based lexical walk (layer 2 names are
-- globally unique, but the walk still honours shadowing) and marks the locals
-- that have to live in cells because a nested function reads or writes them.
local function prepare(ast)
  local seq = 0

  local function newInfo(parent)
    return { parent = parent, upvalSet = {}, upvalList = nil, upvalIndex = nil }
  end

  local rootInfo = newInfo(nil)
  ast._info = rootInfo

  local function newScope(parent, fnInfo)
    return { vars = {}, parent = parent, fnInfo = fnInfo }
  end

  local function declare(scope, fnInfo, name)
    seq = seq + 1
    local binding = {
      id = seq, name = name, fn = fnInfo, captured = false, slot = nil,
    }
    scope.vars[name] = binding
    return binding
  end

  local function resolve(scope, name)
    local s = scope
    while s do
      local binding = s.vars[name]
      if binding then return binding end
      s = s.parent
    end
    return nil
  end

  local function capture(binding, fnInfo)
    binding.captured = true
    local fn = fnInfo
    while fn and fn ~= binding.fn do
      fn.upvalSet[binding] = true
      fn = fn.parent
    end
  end

  local walkExpr, walkList

  local function walkFunction(node, outerScope, parentInfo)
    local info = newInfo(parentInfo)
    node._info = info
    local scope = newScope(outerScope, info)
    local params = node.params or {}
    node._paramBindings = {}
    for i = 1, #params do
      node._paramBindings[i] = declare(scope, info, params[i])
    end
    walkList(node.children, 1, #node.children, scope, info)
  end

  walkExpr = function(node, scope, info)
    local t = node.type
    if t == "Name" then
      local binding = resolve(scope, node.value)
      if binding then
        node._b = binding
        if binding.fn ~= info then capture(binding, info) end
      else
        node._g = true
      end
    elseif t == "Function" then
      walkFunction(node, scope, info)
    else
      local kids = node.children
      for i = 1, #kids do walkExpr(kids[i], scope, info) end
    end
  end

  local function declareList(scope, info, names)
    local list = {}
    for i = 1, #(names or {}) do list[i] = declare(scope, info, names[i]) end
    return list
  end

  local function walkStmt(node, scope, info)
    local t = node.type
    local kids = node.children
    if t == "Local" then
      for i = 1, #kids do walkExpr(kids[i], scope, info) end
      node._bindings = declareList(scope, info, node.names)
    elseif t == "Assign" or t == "Return" then
      for i = 1, #kids do walkExpr(kids[i], scope, info) end
    elseif t == "CallStatement" then
      walkExpr(kids[1], scope, info)
    elseif t == "Do" then
      walkList(kids, 1, #kids, newScope(scope, info), info)
    elseif t == "While" then
      walkExpr(kids[1], scope, info)
      walkList(kids, 2, #kids, newScope(scope, info), info)
    elseif t == "Repeat" then
      local inner = newScope(scope, info)
      walkList(kids, 1, #kids - 1, inner, info)
      walkExpr(kids[#kids], inner, info)
    elseif t == "If" then
      local index = 1
      local branches = node.branches or {}
      for i = 1, #branches do
        local branch = branches[i]
        walkExpr(kids[index], scope, info)
        walkList(kids, index + 1, index + branch.count, newScope(scope, info), info)
        index = index + 1 + branch.count
      end
      if (node.elseCount or 0) > 0 then
        walkList(kids, index, index + node.elseCount - 1, newScope(scope, info), info)
      end
    elseif t == "NumericFor" then
      walkExpr(kids[1], scope, info)
      walkExpr(kids[2], scope, info)
      local start = 3
      if node.hasStep then
        walkExpr(kids[3], scope, info)
        start = 4
      end
      local inner = newScope(scope, info)
      node._cb = declare(inner, info, node.var)
      walkList(kids, start, #kids, inner, info)
    elseif t == "GenericFor" then
      local count = node.exprCount or 0
      for i = 1, count do walkExpr(kids[i], scope, info) end
      local inner = newScope(scope, info)
      node._cbs = declareList(inner, info, node.names)
      walkList(kids, count + 1, #kids, inner, info)
    elseif t == "FunctionDeclaration" then
      walkExpr(kids[1], scope, info)
      walkFunction(kids[2], scope, info)
    elseif t == "LocalFunction" then
      node._cb = declare(scope, info, node.name)
      walkFunction(kids[1], scope, info)
    elseif t == "Break" or t == "Continue" or t == "Goto" or t == "Label" then
      -- no value bindings
    else
      -- Unknown statements are reported by the compiler proper.
    end
  end

  walkList = function(list, from, to, scope, info)
    from = from or 1
    to = to or #list
    for i = from, to do
      if list[i] then walkStmt(list[i], scope, info) end
    end
  end

  local rootScope = newScope(nil, rootInfo)
  walkList(ast.children, 1, #ast.children, rootScope, rootInfo)
  return rootInfo
end

local function finalizeUpvals(info)
  if info.upvalList then return end
  local list = {}
  for binding in pairs(info.upvalSet) do list[#list + 1] = binding end
  table.sort(list, function(x, y) return x.id < y.id end)
  info.upvalList = list
  info.upvalIndex = {}
  for i = 1, #list do info.upvalIndex[list[i]] = i end
end

-- ------------------------------------------------------------------ compile
function Compiler.compile(ast, opts)
  opts = opts or {}
  local state = {
    protos = {},
    errors = {},
    stats = {
      protos = 0, instructions = 0, constants = 0, cells = 0,
      upvalues = 0, maxstack = 0, opcodes = 0, used = {},
    },
  }

  local compileFunction

  local function compileError(msg, node)
    error({
      __compile = true, msg = msg,
      line = (node and node.line) or 0,
      col = (node and node.col) or 0,
    }, 0)
  end

  compileFunction = function(fn, info)
    local isChunk = (fn.type == "Chunk")
    local params = isChunk and {} or (fn.params or {})
    local paramBindings = fn._paramBindings or {}

    local P = {
      code = {}, k = {},
      params = #params,
      vararg = isChunk and true or (fn.vararg and true or false),
      maxstack = 1,
      updesc = {},
    }
    state.protos[#state.protos + 1] = P
    local protoIndex = #state.protos
    fn._protoIndex = protoIndex

    finalizeUpvals(info)

    local kmap = {}
    local ctx = {
      P = P, info = info, protoIndex = protoIndex,
      top = 1, max = 1, cells = 0,
      loops = {}, labels = {}, pending = {},
    }

    local function emit(op, a, b, c, d)
      if not OPSET[op] then
        compileError("internal: unknown opcode '" .. tostring(op) .. "'", fn)
      end
      local inst = { op = op, a = a or 0, b = b or 0, c = c or 0, d = d or 0 }
      P.code[#P.code + 1] = inst
      if op == "NEWCELL" then ctx.cells = ctx.cells + 1 end
      return inst
    end

    local function alloc(n)
      n = n or 1
      local base = ctx.top
      ctx.top = ctx.top + n
      if ctx.top - 1 > ctx.max then ctx.max = ctx.top - 1 end
      return base
    end
    local function freeTo(markTop) ctx.top = markTop end

    local function kIndex(value)
      local key
      if type(value) == "number" then key = numberKey(value)
      elseif type(value) == "string" then key = "s" .. value
      else compileError("unsupported constant type " .. type(value), fn) end
      local idx = kmap[key]
      if idx then return idx end
      idx = #P.k + 1
      P.k[idx] = value
      kmap[key] = idx
      return idx
    end

    local function newLabel() return { pc = nil } end
    local function mark(label) label.pc = #P.code + 1 end
    local function jump(op, reg, label)
      local inst = emit(op, reg or 0)
      inst._lab = label
      return inst
    end

    local function labelFor(node)
      local key = node.bindingId or ("name:" .. tostring(node.name))
      local label = ctx.labels[key]
      if not label then
        label = newLabel()
        ctx.labels[key] = label
      end
      return label
    end

    local function getLocal(dest, binding)
      if binding.captured then emit("GETCELL", dest, binding.slot)
      else emit("MOVE", dest, binding.slot) end
    end

    local function setLocal(binding, src)
      if binding.captured then emit("SETCELL", binding.slot, src)
      else emit("MOVE", binding.slot, src) end
    end

    local function upvalIndex(binding)
      local idx = info.upvalIndex[binding]
      if not idx then
        compileError("internal: missing upvalue '" .. tostring(binding.name) .. "'", fn)
      end
      return idx
    end

    local function readName(node, dest)
      local binding = node._b
      if binding then
        if binding.fn == info then getLocal(dest, binding)
        else emit("GETUPVAL", dest, upvalIndex(binding)) end
      else
        emit("GETGLOBAL", dest, 0, 0, kIndex(node.value))
      end
    end

    local function writeName(node, src)
      local binding = node._b
      if binding then
        if binding.fn == info then
          setLocal(binding, src)
        else
          emit("SETUPVAL", src, upvalIndex(binding))
        end
      else
        emit("SETGLOBAL", src, 0, 0, kIndex(node.value))
      end
    end

    local compileExpr, compileMulti, compileCall, compileTail, compileTable
    local compileExprList, compileStmt, compileBlock

    local function evalSideEffect(e)
      local markTop = ctx.top
      local tmp = alloc(1)
      if isMulti(e) then compileMulti(e, tmp, 0) else compileExpr(e, tmp) end
      freeTo(markTop)
    end

    local function buildUpdesc(childInfo, parentInfo, pi)
      local desc = {}
      local list = childInfo.upvalList or {}
      for i = 1, #list do
        local binding = list[i]
        if binding.fn == parentInfo then
          if not binding.slot then
            compileError("internal: captured local '" ..
              tostring(binding.name) .. "' has no register", fn)
          end
          desc[i] = { 1, binding.slot }
        else
          local idx = parentInfo.upvalIndex[binding]
          if not idx then
            compileError("internal: upvalue '" .. tostring(binding.name) ..
              "' not carried by the enclosing function", fn)
          end
          desc[i] = { 0, idx }
        end
      end
      state.protos[pi].updesc = desc
    end

    local function compileClosure(fnNode, dest)
      local childInfo = fnNode._info
      if not childInfo then
        compileError("internal: function was not prepared", fnNode)
      end
      local pi = compileFunction(fnNode, childInfo)
      buildUpdesc(childInfo, info, pi)
      emit("CLOSURE", dest, pi)
    end

    compileExpr = function(e, dest)
      local markTop = ctx.top
      local t = e.type
      if t == "Nil" then
        emit("LOADNIL", dest)
      elseif t == "Boolean" then
        emit("LOADBOOL", dest, e.value and 1 or 0)
      elseif t == "Number" then
        if isIntImmediate(e.value) then emit("LOADINT", dest, 0, 0, e.value)
        else emit("LOADK", dest, 0, 0, kIndex(e.value)) end
      elseif t == "String" then
        emit("LOADK", dest, 0, 0, kIndex(e.value))
      elseif t == "Vararg" then
        emit("VARARG", dest, 1)
      elseif t == "Name" then
        readName(e, dest)
      elseif t == "Parenthesized" then
        compileExpr(e.children[1], dest)
      elseif t == "UnaryOp" then
        local op = UNOP[e.op]
        if not op then
          compileError("unsupported unary operator '" .. tostring(e.op) .. "'", e)
        end
        compileExpr(e.children[1], dest)
        emit(op, dest, dest)
      elseif t == "BinaryOp" then
        local op = e.op
        if op == "and" then
          local skip = newLabel()
          compileExpr(e.children[1], dest)
          jump("JMPF", dest, skip)
          compileExpr(e.children[2], dest)
          mark(skip)
        elseif op == "or" then
          local skip = newLabel()
          compileExpr(e.children[1], dest)
          jump("JMPT", dest, skip)
          compileExpr(e.children[2], dest)
          mark(skip)
        else
          local name = BINOP[op]
          if not name then
            compileError("unsupported binary operator '" .. tostring(op) .. "'", e)
          end
          compileExpr(e.children[1], dest)
          local right = e.children[2]
          local literal = right.type == "Number" and right.value or nil
          local emitted = false
          if literal ~= nil then
            if isIntImmediate(literal) and IOP[name] then
              emit(IOP[name], dest, dest, 0, literal)
              emitted = true
            elseif KOP[name] then
              emit(KOP[name], dest, dest, 0, kIndex(literal))
              emitted = true
            end
          end
          if not emitted then
            local rt = alloc(1)
            compileExpr(right, rt)
            emit(name, dest, dest, rt)
          end
        end
      elseif t == "Index" then
        compileExpr(e.children[1], dest)
        local key = e.children[2]
        if key.type == "String" then
          emit("GETFIELD", dest, dest, 0, kIndex(key.value))
        elseif key.type == "Number" and isIntImmediate(key.value) then
          emit("GETIDXI", dest, dest, 0, key.value)
        else
          local kt = alloc(1)
          compileExpr(key, kt)
          emit("GETTABLE", dest, dest, kt)
        end
      elseif t == "Call" then
        compileCall(e, dest, 1)
      elseif t == "Function" then
        compileClosure(e, dest)
      elseif t == "Table" then
        compileTable(e, dest)
      elseif t == "IfExpression" then
        local endLabel = newLabel()
        local branches = e.branches or {}
        for i = 1, #branches do
          local branch = branches[i]
          local nextLabel = newLabel()
          local cmark = ctx.top
          local ct = alloc(1)
          compileExpr(e.children[branch.cond], ct)
          jump("JMPF", ct, nextLabel)
          freeTo(cmark)
          compileExpr(e.children[branch.value], dest)
          jump("JMP", 0, endLabel)
          mark(nextLabel)
        end
        compileExpr(e.children[e.elseIndex], dest)
        mark(endLabel)
      else
        compileError("unsupported expression node '" .. tostring(t) .. "'", e)
      end
      freeTo(markTop)
    end

    compileMulti = function(e, base, want)
      if want == 0 and not isMulti(e) then
        evalSideEffect(e)
        return
      end
      if e.type == "Call" then
        compileCall(e, base, want)
      elseif e.type == "Vararg" then
        emit("VARARG", base, want)
      elseif want < 0 then
        compileExpr(e, base)
        emit("SETTOP", base + 1)
      else
        compileExpr(e, base)
        if want > 1 then emit("LOADNILN", base + 1, 0, 0, want - 1) end
      end
    end

    compileExprList = function(exprs, base, want)
      local ne = #exprs
      if want == 0 then
        for i = 1, ne do evalSideEffect(exprs[i]) end
        return
      end
      local keep = math.min(ne, want)
      if keep == 0 then
        for i = 1, ne do evalSideEffect(exprs[i]) end
        emit("LOADNILN", base, 0, 0, want)
        return
      end
      for i = 1, keep - 1 do compileExpr(exprs[i], base + i - 1) end
      local last = exprs[keep]
      if keep == ne then
        compileMulti(last, base + keep - 1, want - (keep - 1))
      else
        compileExpr(last, base + keep - 1)
        for i = keep + 1, ne do evalSideEffect(exprs[i]) end
        if keep < want then emit("LOADNILN", base + keep, 0, 0, want - keep) end
      end
    end

    local function compileArgs(args, argBase)
      local nargs = #args
      if nargs == 0 then return 0 end
      local last = args[nargs]
      if isMulti(last) then
        for i = 1, nargs - 1 do compileExpr(args[i], argBase + i - 1) end
        compileMulti(last, argBase + nargs - 1, -1)
        return -1
      end
      for i = 1, nargs do compileExpr(args[i], argBase + i - 1) end
      return nargs
    end

    compileCall = function(e, dest, want)
      local markTop = ctx.top
      local kids = e.children
      local nargs = #kids - 1
      local args = {}
      for i = 2, #kids do args[#args + 1] = kids[i] end
      local base, argBase
      if e.method then
        base = alloc(2 + nargs)
        compileExpr(kids[1], base)
        emit("SELF", base, base, 0, kIndex(e.method))
        argBase = base + 2
        local count = compileArgs(args, argBase)
        local bfield = count
        if count >= 0 then bfield = 1 + count end
        emit("CALL", base, bfield, want, dest)
      else
        base = alloc(1 + nargs)
        compileExpr(kids[1], base)
        argBase = base + 1
        local count = compileArgs(args, argBase)
        emit("CALL", base, count, want, dest)
      end
      freeTo(markTop)
    end

    compileTail = function(e)
      local markTop = ctx.top
      local kids = e.children
      local nargs = #kids - 1
      local args = {}
      for i = 2, #kids do args[#args + 1] = kids[i] end
      local base, count
      if e.method then
        base = alloc(2 + nargs)
        compileExpr(kids[1], base)
        emit("SELF", base, base, 0, kIndex(e.method))
        count = compileArgs(args, base + 2)
        if count >= 0 then count = 1 + count end
      else
        base = alloc(1 + nargs)
        compileExpr(kids[1], base)
        count = compileArgs(args, base + 1)
      end
      emit("TAILCALL", base, count)
      freeTo(markTop)
    end

    compileTable = function(e, dest)
      local markTop = ctx.top
      emit("NEWTABLE", dest)
      local fields = e.children
      local arrayIndex = 1
      for i = 1, #fields do
        local field = fields[i]
        local value = field.children[#field.children]
        if field.kind == "array" then
          if i == #fields and isMulti(value) then
            local base = alloc(1)
            compileMulti(value, base, -1)
            emit("SETLIST", dest, arrayIndex, base, -1)
          else
            local vt = alloc(1)
            compileExpr(value, vt)
            emit("SETIDXI", dest, vt, 0, arrayIndex)
          end
          arrayIndex = arrayIndex + 1
        else
          local key = field.key
          if key and key.type == "String" then
            local vt = alloc(1)
            compileExpr(value, vt)
            emit("SETFIELD", dest, vt, 0, kIndex(key.value))
          else
            local kt = alloc(1)
            compileExpr(key, kt)
            local vt = alloc(1)
            compileExpr(value, vt)
            emit("SETTABLE", dest, kt, vt)
          end
        end
        freeTo(markTop)
      end
      freeTo(markTop)
    end

    local function compileDeclarations(node)
      local names = node.names or {}
      local bindings = node._bindings or {}
      local n = #names
      local base = alloc(n)
      local exprs = node.children
      if #exprs > 0 then
        local vb = alloc(math.max(n, #exprs))
        compileExprList(exprs, vb, n)
        for i = 1, n do
          local binding = bindings[i]
          binding.slot = base + i - 1
          if binding.captured then
            emit("NEWCELL", binding.slot, vb + i - 1)
          else
            emit("MOVE", binding.slot, vb + i - 1)
          end
        end
      else
        for i = 1, n do
          local binding = bindings[i]
          binding.slot = base + i - 1
          if binding.captured then emit("NEWCELL", binding.slot, 0)
          else emit("LOADNIL", binding.slot) end
        end
      end
      ctx.top = base + n
    end

    local function compileAssign(node)
      local targetCount = node.targetCount or 0
      local kids = node.children
      local exprs = {}
      for i = targetCount + 1, #kids do exprs[#exprs + 1] = kids[i] end
      local markTop = ctx.top
      local pre = {}
      for i = 1, targetCount do
        local target = kids[i]
        if target.type == "Index" then
          local obj = alloc(1)
          compileExpr(target.children[1], obj)
          local key = nil
          if target.children[2].type ~= "String" then
            key = alloc(1)
            compileExpr(target.children[2], key)
          end
          pre[i] = { obj = obj, key = key, keyNode = target.children[2] }
        end
      end
      local n = targetCount
      if n > 0 then
        local vb = alloc(math.max(n, #exprs))
        compileExprList(exprs, vb, n)
        for i = 1, n do
          local target = kids[i]
          local src = vb + i - 1
          if target.type == "Name" then
            writeName(target, src)
          else
            local p = pre[i]
            if p.key then
              emit("SETTABLE", p.obj, p.key, src)
            else
              emit("SETFIELD", p.obj, src, 0, kIndex(p.keyNode.value))
            end
          end
        end
      else
        for i = 1, #exprs do evalSideEffect(exprs[i]) end
      end
      freeTo(markTop)
    end

    compileBlock = function(list, from, to, keepTop)
      from = from or 1
      to = to or #list
      local markTop = ctx.top
      for i = from, to do
        if list[i] then compileStmt(list[i]) end
      end
      if not keepTop then ctx.top = markTop end
    end

    compileStmt = function(st)
      local t = st.type
      local kids = st.children
      if t == "Local" then
        compileDeclarations(st)
      elseif t == "Assign" then
        compileAssign(st)
      elseif t == "CallStatement" then
        local markTop = ctx.top
        compileCall(kids[1], 0, 0)
        freeTo(markTop)
      elseif t == "Do" then
        compileBlock(kids)
      elseif t == "If" then
        local endLabel = newLabel()
        local index = 1
        local branches = st.branches or {}
        for i = 1, #branches do
          local branch = branches[i]
          local cmark = ctx.top
          local ct = alloc(1)
          compileExpr(kids[index], ct)
          local nextLabel = newLabel()
          jump("JMPF", ct, nextLabel)
          freeTo(cmark)
          compileBlock(kids, index + 1, index + branch.count)
          jump("JMP", 0, endLabel)
          mark(nextLabel)
          index = index + 1 + branch.count
        end
        if (st.elseCount or 0) > 0 then
          compileBlock(kids, index, index + st.elseCount - 1)
        end
        mark(endLabel)
      elseif t == "While" then
        local startLabel = newLabel()
        local breakLabel = newLabel()
        mark(startLabel)
        local cmark = ctx.top
        local ct = alloc(1)
        compileExpr(kids[1], ct)
        jump("JMPF", ct, breakLabel)
        freeTo(cmark)
        ctx.loops[#ctx.loops + 1] = {
          breakLabel = breakLabel, continueLabel = startLabel,
        }
        compileBlock(kids, 2, #kids)
        ctx.loops[#ctx.loops] = nil
        jump("JMP", 0, startLabel)
        mark(breakLabel)
      elseif t == "Repeat" then
        local startLabel = newLabel()
        local condLabel = newLabel()
        local breakLabel = newLabel()
        local markTop = ctx.top
        mark(startLabel)
        ctx.loops[#ctx.loops + 1] = {
          breakLabel = breakLabel, continueLabel = condLabel,
        }
        compileBlock(kids, 1, #kids - 1, true)
        ctx.loops[#ctx.loops] = nil
        mark(condLabel)
        local ct = alloc(1)
        compileExpr(kids[#kids], ct)
        ctx.top = markTop
        jump("JMPF", ct, startLabel)
        mark(breakLabel)
      elseif t == "NumericFor" then
        local markTop = ctx.top
        local base = alloc(4)
        compileExpr(kids[1], base)
        compileExpr(kids[2], base + 1)
        local bodyStart = 3
        if st.hasStep then
          compileExpr(kids[3], base + 2)
          bodyStart = 4
        else
          emit("LOADINT", base + 2, 0, 0, 1)
        end
        local bodyLabel = newLabel()
        local loopLabel = newLabel()
        local breakLabel = newLabel()
        jump("FORPREP", base, loopLabel)
        mark(bodyLabel)
        local binding = st._cb
        if binding.captured then
          binding.slot = alloc(1)
          emit("NEWCELL", binding.slot, base + 3)
        else
          binding.slot = base + 3
        end
        ctx.loops[#ctx.loops + 1] = {
          breakLabel = breakLabel, continueLabel = loopLabel,
        }
        compileBlock(kids, bodyStart, #kids)
        ctx.loops[#ctx.loops] = nil
        mark(loopLabel)
        jump("FORLOOP", base, bodyLabel)
        mark(breakLabel)
        freeTo(markTop)
      elseif t == "GenericFor" then
        local markTop = ctx.top
        local names = st._cbs or {}
        local nvars = #names
        local exprCount = st.exprCount or 0
        local base = alloc(3 + nvars)
        local tmpCount = math.max(3, exprCount)
        local tmp = alloc(tmpCount)
        local exprs = {}
        for i = 1, exprCount do exprs[i] = kids[i] end
        compileExprList(exprs, tmp, tmpCount)
        for i = 1, 3 do emit("MOVE", base + i - 1, tmp + i - 1) end
        ctx.top = base + 3 + nvars
        local callLabel = newLabel()
        local bodyLabel = newLabel()
        local afterLabel = newLabel()
        local breakLabel = newLabel()
        mark(callLabel)
        emit("TFORCALL", base, nvars)
        jump("TFORLOOP", base, bodyLabel)
        jump("JMP", 0, afterLabel)
        mark(bodyLabel)
        for i = 1, nvars do
          local binding = names[i]
          local src = base + 3 + i - 1
          if binding.captured then
            binding.slot = alloc(1)
            emit("NEWCELL", binding.slot, src)
          else
            binding.slot = src
          end
        end
        ctx.loops[#ctx.loops + 1] = {
          breakLabel = breakLabel, continueLabel = callLabel,
        }
        compileBlock(kids, exprCount + 1, #kids)
        ctx.loops[#ctx.loops] = nil
        jump("JMP", 0, callLabel)
        mark(afterLabel)
        mark(breakLabel)
        freeTo(markTop)
      elseif t == "FunctionDeclaration" then
        local markTop = ctx.top
        local target = kids[1]
        local fnNode = kids[2]
        if target.type == "Index" then
          local obj = alloc(1)
          compileExpr(target.children[1], obj)
          local key = nil
          if target.children[2].type ~= "String" then
            key = alloc(1)
            compileExpr(target.children[2], key)
          end
          local tmp = alloc(1)
          compileClosure(fnNode, tmp)
          if key then
            emit("SETTABLE", obj, key, tmp)
          else
            emit("SETFIELD", obj, tmp, 0, kIndex(target.children[2].value))
          end
        else
          local tmp = alloc(1)
          compileClosure(fnNode, tmp)
          writeName(target, tmp)
        end
        freeTo(markTop)
      elseif t == "LocalFunction" then
        local binding = st._cb
        local fnNode = kids[1]
        local slot = alloc(1)
        binding.slot = slot
        if binding.captured then
          emit("NEWCELL", slot, 0)
          local tmp = alloc(1)
          compileClosure(fnNode, tmp)
          emit("SETCELL", slot, tmp)
          ctx.top = slot + 1
        else
          compileClosure(fnNode, slot)
        end
      elseif t == "Return" then
        local ne = #kids
        if ne == 0 then
          emit("RETURN", 0, 0)
        elseif ne == 1 and kids[1].type == "Call" then
          compileTail(kids[1])
        else
          local base = alloc(ne)
          local last = kids[ne]
          for i = 1, ne - 1 do compileExpr(kids[i], base + i - 1) end
          if isMulti(last) then
            compileMulti(last, base + ne - 1, -1)
            emit("RETURN", base, -1)
          else
            compileExpr(last, base + ne - 1)
            emit("RETURN", base, ne)
          end
          freeTo(base)
        end
      elseif t == "Break" then
        local loop = ctx.loops[#ctx.loops]
        if loop then jump("JMP", 0, loop.breakLabel) end
      elseif t == "Continue" then
        local loop = ctx.loops[#ctx.loops]
        if loop then jump("JMP", 0, loop.continueLabel) end
      elseif t == "Label" then
        mark(labelFor(st))
      elseif t == "Goto" then
        jump("JMP", 0, labelFor(st))
      else
        compileError("unsupported statement node '" .. tostring(t) .. "'", st)
      end
    end

    -- Parameters occupy registers 1..n; captured parameters get their cell
    -- wrapper before any body instruction runs.
    for i = 1, #params do
      local binding = paramBindings[i]
      binding.slot = i
      if binding.captured then emit("NEWCELL", i, i) end
    end
    ctx.top = #params + 1
    if #params > ctx.max then ctx.max = #params end

    if isChunk then
      compileBlock(fn.children)
    else
      compileBlock(fn.children)
    end
    emit("RETURN", 0, 0)

    if ctx.top - 1 > ctx.max then ctx.max = ctx.top - 1 end
    P.maxstack = math.max(ctx.max, P.params, 1)

    -- Resolve jump offsets relative to the next instruction.
    for pc = 1, #P.code do
      local inst = P.code[pc]
      if inst._lab then
        local label = inst._lab
        if not label.pc then
          compileError("unresolved jump target", fn)
        end
        inst.d = label.pc - (pc + 1)
        inst._lab = nil
      end
    end

    state.stats.cells = state.stats.cells + ctx.cells
    return protoIndex
  end

  local rootInfo = prepare(ast)
  local ok, err = pcall(function()
    compileFunction(ast, rootInfo)
  end)
  if not ok then
    if type(err) == "table" and err.__compile then
      state.errors[#state.errors + 1] = {
        line = err.line or 0, col = err.col or 0, msg = err.msg,
      }
    else
      error(err, 0)
    end
  end

  local instr = 0
  local consts = 0
  local upvalues = 0
  local maxstack = 0
  local used = {}
  local usedCount = 0
  for i = 1, #state.protos do
    local P = state.protos[i]
    instr = instr + #P.code
    consts = consts + #P.k
    upvalues = upvalues + #P.updesc
    if P.maxstack > maxstack then maxstack = P.maxstack end
    for j = 1, #P.code do
      local op = P.code[j].op
      if not used[op] then
        used[op] = true
        usedCount = usedCount + 1
      end
    end
  end
  state.stats.protos = #state.protos
  state.stats.instructions = instr
  state.stats.constants = consts
  state.stats.upvalues = upvalues
  state.stats.maxstack = maxstack
  state.stats.opcodes = usedCount
  state.stats.used = used

  return {
    protos = state.protos,
    ops = OPS,
    errors = state.errors,
    stats = state.stats,
    -- Pool indices that back field names; forwarded to the anti-debug layer.
    fieldKeys = ast.fieldKeys,
    canaryKeys = ast.canaryKeys,
  }
end

-- ----------------------------------------------------------------- validate
-- Structural checks used by the acceptance test (and by later layers as a
-- cheap guard before packaging). Returns a list of human-readable problems.
-- Operand roles in a/b/c/d order. '-' is unused (omission encodes as zero),
-- r register, k constant, u upvalue, p prototype, j jump, f flag, t stack top,
-- c count with the -1 open-arity sentinel, i integer, n numeric immediate.
local OPERANDS = {
  MOVE = "rr", LOADK = "r--k", LOADNIL = "r", LOADBOOL = "rf",
  LOADINT = "r--n", LOADNILN = "i--i", GETUPVAL = "ru", SETUPVAL = "ru",
  NEWCELL = "ri", GETCELL = "rr", SETCELL = "rr",
  GETGLOBAL = "r--k", SETGLOBAL = "r--k", NEWTABLE = "r",
  GETTABLE = "rrr", SETTABLE = "rrr", GETFIELD = "rr-k", SETFIELD = "rr-k",
  SELF = "rr-k", SETLIST = "riic", GETIDXI = "rr-n", SETIDXI = "rr-n",
  BOOL = "rrf", TEST = "fr", TESTSET = "frr", TESTNIL = "-r",
  JMP = "---j", JMPF = "r--j", JMPT = "r--j", FORPREP = "r--j",
  FORLOOP = "r--j", TFORCALL = "ri", TFORLOOP = "r--j",
  CLOSE = "i", NOP = "", SETTOP = "t", CALL = "rcci", TAILCALL = "rc",
  RETURN = "ic", CLOSURE = "rp", VARARG = "ic",
}
for _, op in pairs(BINOP) do OPERANDS[op] = "rrr" end
for _, op in pairs(UNOP) do OPERANDS[op] = "rr" end
for _, op in pairs(KOP) do OPERANDS[op] = "rr-k" end
for _, op in pairs(IOP) do OPERANDS[op] = "rr-n" end

function Compiler.validate(compiled)
  local problems = {}
  local function fail(msg)
    if #problems < 40 then problems[#problems + 1] = msg end
  end
  -- Leave room for operand masks and zigzag encoding in the portable exact
  -- integer range. Numeric literals/constants are not register operands.
  local function integer(v)
    return type(v) == "number" and v == v and
      v >= -4503599627366400 and v <= 4503599627366400 and v == math.floor(v)
  end
  local function record(t, where)
    if type(t) ~= "table" or getmetatable(t) ~= nil then
      fail(where .. ": expected plain table")
      return false
    end
    return true
  end
  local function sequence(t, where)
    if not record(t, where) then return {}, 0 end
    local count, last = 0, 0
    for key in next, t do
      if not integer(key) or key < 1 then
        fail(where .. ": expected dense array")
        return {}, 0
      end
      count = count + 1
      if key > last then last = key end
    end
    if last ~= count then
      fail(where .. ": expected dense array")
      return {}, 0
    end
    return t, count
  end

  if not record(compiled, "compiled program") then return problems end
  if compiled.errors ~= nil then
    local _, count = sequence(compiled.errors, "compiled errors")
    if count > 0 then fail("compiled errors present") end
  end
  for _, key in ipairs({ "fieldKeys", "canaryKeys" }) do
    if compiled[key] ~= nil then record(compiled[key], key) end
  end
  local protos, np = sequence(compiled.protos, "prototypes")
  if np == 0 then fail("no prototypes") end
  local headers = {}
  for pi = 1, np do
    local P, where = protos[pi], "proto " .. pi
    if record(P, where) then
      local code, nc = sequence(P.code, where .. " code")
      local k, nk = sequence(P.k, where .. " constants")
      local updesc, nu = sequence(P.updesc, where .. " updesc")
      local max = P.maxstack
      if not integer(max) or max < 1 then
        fail(where .. ": invalid maxstack")
        max = 0
      end
      local params = P.params
      if params == nil then params = 0 end
      if not integer(params) or params < 0 or params > max then
        fail(where .. ": invalid params or params exceed maxstack")
      end
      if P.vararg ~= nil and type(P.vararg) ~= "boolean" then
        fail(where .. ": invalid vararg flag")
      end
      if nc == 0 then fail(where .. ": empty code") end
      if pi == 1 and nu > 0 then fail(where .. ": entry cannot capture upvalues") end
      for i = 1, nk do
        local kind = type(k[i])
        if kind ~= "number" and kind ~= "string" and kind ~= "boolean" then
          fail(where .. ": unsupported constant " .. i)
        end
      end
      local captures = {}
      for i = 1, nu do
        local d, nd = sequence(updesc[i], where .. " upvalue descriptor " .. i)
        if nd ~= 2 or (d[1] ~= 0 and d[1] ~= 1) or
           not integer(d[2]) or d[2] < 1 then
          fail(where .. ": bad upvalue descriptor " .. i)
        else
          captures[#captures + 1] = d
        end
      end
      headers[pi] = { code = code, nc = nc, nk = nk, nu = nu, max = max,
        captures = captures, vararg = P.vararg == true }
    end
  end

  local fields = { "a", "b", "c", "d" }
  for pi = 1, np do
    local P = headers[pi]
    if P then
      for pc = 1, P.nc do
        local I, where = P.code[pc], "proto " .. pi .. "@" .. pc
        if record(I, where) then
          local op = I.op
          local spec = type(op) == "string" and OPERANDS[op]
          if not spec then
            fail(where .. ": unknown opcode" .. (type(op) == "string" and (" " .. op) or ""))
          else
            local valid = true
            for slot = 1, 4 do
              local field = fields[slot]
              local role = spec:sub(slot, slot)
              if role == "" then role = "-" end
              local v = I[field]
              local ok = role == "n" and type(v) == "number" or
                (role ~= "n" and ((role == "-" and v == nil) or integer(v)))
              local detail = "invalid operand " .. field
              if ok and role == "r" then
                ok, detail = v >= 1 and v <= P.max, "register " .. field .. " out of range"
              elseif ok and role == "k" then
                ok, detail = v >= 1 and v <= P.nk, "constant index out of range"
              elseif ok and role == "u" then
                ok, detail = v >= 1 and v <= P.nu, "upvalue index out of range"
              elseif ok and role == "p" then
                ok, detail = v >= 1 and v <= np and headers[v] ~= nil,
                  "prototype index out of range"
              elseif ok and role == "j" then
                -- Finalization appends RETURN after all labels. One-past-code
                -- is not an implicit exit: both interpreters fetch at that pc.
                ok, detail = v >= -pc and v <= P.nc - pc - 1, "jump out of range"
              elseif ok and role == "f" then
                ok, detail = v == 0 or v == 1, "invalid boolean flag " .. field
              elseif ok and role == "t" then
                ok, detail = v >= 1 and v <= P.max + 1, "stack top out of range"
              elseif ok and role == "c" then
                ok, detail = v >= -1, "invalid count " .. field
              end
              if not ok then fail(where .. ": " .. detail) valid = false end
            end
            if valid then
              local a, b, c, d = I.a, I.b, I.c, I.d
              local function window(first, count, label)
                if first < 1 or first > P.max + 1 or count < 0 or
                   count > P.max - first + 1 then
                  fail(where .. ": " .. label .. " register window out of range")
                end
              end
              if op == "LOADNILN" then
                window(a, d, "LOADNILN")
              elseif op == "NEWCELL" then
                if b < 0 or b > P.max then fail(where .. ": cell register out of range") end
              elseif op == "SELF" then
                window(a, 2, "SELF")
              elseif op == "SETLIST" then
                window(c, d == -1 and 1 or d, "SETLIST")
              elseif op == "FORPREP" then
                window(a, 3, "FORPREP")
              elseif op == "FORLOOP" or op == "TFORLOOP" then
                window(a, 4, op)
              elseif op == "TFORCALL" then
                if b < 0 then fail(where .. ": invalid TFORCALL result count") end
                window(a, 3 + math.max(b, 0), "TFORCALL")
              elseif op == "CLOSE" then
                if a < 0 or a > P.max + 1 then fail(where .. ": close register out of range") end
              elseif op == "CALL" or op == "TAILCALL" then
                window(a, b == -1 and 1 or b + 1, "call arguments")
                if op == "CALL" then
                  if d < 0 then fail(where .. ": invalid call destination")
                  else window(d == 0 and a or d, c == -1 and 1 or c, "call results") end
                end
              elseif op == "RETURN" or op == "VARARG" then
                if op == "VARARG" and not P.vararg then
                  fail(where .. ": VARARG in non-vararg prototype")
                end
                if not (op == "RETURN" and a == 0 and b == 0) then
                  window(a, b == -1 and 1 or b, op)
                end
              elseif op == "CLOSURE" then
                for _, capture in ipairs(headers[b].captures) do
                  local limit = capture[1] == 1 and P.max or P.nu
                  if capture[2] > limit then
                    fail(where .. ": closure capture out of range in enclosing prototype")
                  end
                end
              end
              if (op == "TEST" or op == "TESTSET" or op == "TESTNIL") and pc + 2 > P.nc then
                fail(where .. ": skip target out of range")
              end
            end
          end
        end
      end
    end
  end
  return problems
end

return Compiler
