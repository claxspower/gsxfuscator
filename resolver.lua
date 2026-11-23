-- resolver.lua -- scope resolution, capture analysis, identifier/label renaming.
local U = require("src.util")
local Resolver = {}

local function newScope(parent)
  return { vars = {}, parent = parent }
end

function Resolver.resolve(ast)
  local self = {
    errors = {},
    usedNames = {},
    bindings = {},
    nameSeq = 0,
    labelSeq = 0,
  }

  local function err(node, msg)
    self.errors[#self.errors + 1] = {
      line = node and node.line or 0,
      col = node and node.col or 0,
      msg = msg,
    }
  end

  local function freshName(prefix)
    local nm
    repeat
      self.nameSeq = self.nameSeq + 1
      nm = U.ident(prefix or "_0x") .. U.hex(self.nameSeq)
    until not self.usedNames[nm]
    self.usedNames[nm] = true
    return nm
  end

  local function declare(scope, nameValue, kind, ctx)
    local b = {
      name = nameValue,
      kind = kind,
      newname = freshName("_0x"),
      captured = false,
      func = ctx.func,
    }
    scope.vars[nameValue] = b
    self.bindings[#self.bindings + 1] = b
    return b
  end

  local function findLocal(scope, nameValue)
    while scope do
      local b = scope.vars[nameValue]
      if b then return b end
      scope = scope.parent
    end
    return nil
  end

  local resolveExpr, resolveFunction, resolveBlock, resolveStmt

  -- Returns upvalue index and upvalue descriptor table for ctx.
  local resolveUpvalue
  resolveUpvalue = function(ctx, nameValue)
    -- A local in the lexically enclosing function at the creation point?
    local b = findLocal(ctx.parentScope, nameValue)
    if b then
      for i = 1, #ctx.info.upvals do
        if ctx.info.upvals[i].binding == b then return i, ctx.info.upvals[i] end
      end
      b.captured = true
      local entry = { name = nameValue, binding = b, instack = true }
      ctx.info.upvals[#ctx.info.upvals + 1] = entry
      return #ctx.info.upvals, entry
    end
    if ctx.parent then
      local pidx, pentry = resolveUpvalue(ctx.parent, nameValue)
      if not pidx then return nil end
      for i = 1, #ctx.info.upvals do
        if ctx.info.upvals[i].parentEntry == pentry then return i, ctx.info.upvals[i] end
      end
      local entry = { name = nameValue, instack = false, idx = pidx, parentEntry = pentry }
      ctx.info.upvals[#ctx.info.upvals + 1] = entry
      return #ctx.info.upvals, entry
    end
    return nil
  end

  local function resolveName(node, ctx)
    local b = findLocal(ctx.scope, node.v)
    if b then
      node.binding = b
      return
    end
    local idx = resolveUpvalue(ctx, node.v)
    if idx then
      -- Never cache by name: the same name can bind to different outer
      -- variables at different points in one function body.
      node.binding = { kind = "upval", idx = idx, name = node.v }
      return
    end
    node.global = true
  end

  local function resolveTarget(node, ctx)
    if node.t == "Name" then
      resolveName(node, ctx)
    elseif node.t == "Index" then
      resolveExpr(node.obj, ctx)
      resolveExpr(node.key, ctx)
    else
      err(node, "invalid assignment target")
    end
  end

  resolveExpr = function(node, ctx)
    if not node then return end
    local t = node.t
    if t == "Name" then
      resolveName(node, ctx)
    elseif t == "Index" then
      resolveExpr(node.obj, ctx)
      resolveExpr(node.key, ctx)
    elseif t == "Call" then
      resolveExpr(node.fn, ctx)
      for i = 1, #node.args do resolveExpr(node.args[i], ctx) end
    elseif t == "Func" then
      resolveFunction(node, ctx, ctx.scope)
    elseif t == "Table" then
      for i = 1, #node.fields do
        local f = node.fields[i]
        if f.key then resolveExpr(f.key, ctx) end
        resolveExpr(f.value, ctx)
      end
    elseif t == "Bin" then
      resolveExpr(node.l, ctx)
      resolveExpr(node.r, ctx)
    elseif t == "Un" then
      resolveExpr(node.e, ctx)
    elseif t == "Paren" then
      resolveExpr(node.e, ctx)
    elseif t == "IfExpr" then
      for i = 1, #node.branches do
        resolveExpr(node.branches[i].cond, ctx)
        resolveExpr(node.branches[i].value, ctx)
      end
      resolveExpr(node.orelse, ctx)
    elseif t == "Vararg" then
      if not ctx.vararg then
        err(node, "cannot use '...' outside a vararg function")
      end
    end
  end

  resolveFunction = function(fn, parentCtx, parentScope)
    local info = {
      upvals = {},
      upvalRefs = {},
      labels = {},
      labelList = {},
      gotos = {},
      loopDepth = 0,
      vararg = fn.vararg and true or false,
    }
    fn.info = info
    local fctx = {
      func = fn,
      parent = parentCtx,
      parentScope = parentScope,
      info = info,
      vararg = fn.vararg and true or false,
    }
    local pscope = newScope(nil)
    fctx.paramScope = pscope
    fctx.scope = pscope
    fn.paramBindings = {}
    for i = 1, #fn.params do
      fn.paramBindings[i] = declare(pscope, fn.params[i], "param", fctx)
    end
    local bscope = newScope(pscope)
    fctx.scope = bscope
    resolveBlock(fn.body, bscope, fctx)
    -- Resolve pending gotos against labels of this function.
    for i = 1, #info.gotos do
      local g = info.gotos[i]
      local lab = info.labels[g.name]
      if not lab then
        err(g.node, "no visible label '" .. g.name .. "' for goto")
      else
        g.node.labelObj = lab.node
      end
    end
  end

  local function resolveLoopBlock(block, ctx)
    ctx.info.loopDepth = ctx.info.loopDepth + 1
    local scope = newScope(ctx.scope)
    resolveBlock(block, scope, ctx)
    ctx.info.loopDepth = ctx.info.loopDepth - 1
  end

  resolveStmt = function(st, ctx)
    if not st then return end
    local t = st.t
    if t == "Local" then
      for i = 1, #st.exprs do resolveExpr(st.exprs[i], ctx) end
      for i = 1, #st.names do
        st.bindings = st.bindings or {}
        st.bindings[i] = declare(ctx.scope, st.names[i], "local", ctx)
      end
    elseif t == "Assign" then
      for i = 1, #st.targets do resolveTarget(st.targets[i], ctx) end
      for i = 1, #st.exprs do resolveExpr(st.exprs[i], ctx) end
    elseif t == "LocalFunction" then
      local b = declare(ctx.scope, st.name, "local", ctx)
      st.binding = b
      resolveFunction(st.func, ctx, ctx.scope)
    elseif t == "FunctionStat" then
      resolveTarget(st.target, ctx)
      resolveFunction(st.func, ctx, ctx.scope)
    elseif t == "CallStat" then
      resolveExpr(st.call, ctx)
    elseif t == "Do" then
      local scope = newScope(ctx.scope)
      resolveBlock(st.block, scope, ctx)
    elseif t == "While" then
      resolveExpr(st.cond, ctx)
      resolveLoopBlock(st.block, ctx)
    elseif t == "Repeat" then
      ctx.info.loopDepth = ctx.info.loopDepth + 1
      local scope = newScope(ctx.scope)
      resolveBlock(st.block, scope, ctx)
      -- The until-expression runs in the body scope, so body locals are visible.
      local prev = ctx.scope
      ctx.scope = scope
      resolveExpr(st.cond, ctx)
      ctx.scope = prev
      ctx.info.loopDepth = ctx.info.loopDepth - 1
    elseif t == "If" then
      for i = 1, #st.branches do
        local br = st.branches[i]
        resolveExpr(br.cond, ctx)
        local scope = newScope(ctx.scope)
        resolveBlock(br.block, scope, ctx)
      end
      if st.orelse then
        local scope = newScope(ctx.scope)
        resolveBlock(st.orelse, scope, ctx)
      end
    elseif t == "NumFor" then
      resolveExpr(st.from, ctx)
      resolveExpr(st.to, ctx)
      if st.step then resolveExpr(st.step, ctx) end
      ctx.info.loopDepth = ctx.info.loopDepth + 1
      local scope = newScope(ctx.scope)
      st.binding = declare(scope, st.var, "local", ctx)
      resolveBlock(st.block, scope, ctx)
      ctx.info.loopDepth = ctx.info.loopDepth - 1
    elseif t == "GenFor" then
      for i = 1, #st.exprs do resolveExpr(st.exprs[i], ctx) end
      ctx.info.loopDepth = ctx.info.loopDepth + 1
      local scope = newScope(ctx.scope)
      st.bindings = {}
      for i = 1, #st.names do
        st.bindings[i] = declare(scope, st.names[i], "local", ctx)
      end
      resolveBlock(st.block, scope, ctx)
      ctx.info.loopDepth = ctx.info.loopDepth - 1
    elseif t == "Return" then
      for i = 1, #st.exprs do resolveExpr(st.exprs[i], ctx) end
    elseif t == "Break" then
      if ctx.info.loopDepth <= 0 then err(st, "break outside a loop") end
    elseif t == "Continue" then
      if ctx.info.loopDepth <= 0 then err(st, "continue outside a loop") end
    elseif t == "Label" then
      if ctx.info.labels[st.name] then
        err(st, "label '" .. st.name .. "' already defined")
      else
        ctx.info.labelSeq = (ctx.info.labelSeq or 0) + 1
        local lab = { name = st.name, node = st, newname = freshName("_0xL") .. ctx.info.labelSeq }
        ctx.info.labels[st.name] = lab
      end
    elseif t == "Goto" then
      ctx.info.gotos[#ctx.info.gotos + 1] = { node = st, name = st.name }
    end
  end

  resolveBlock = function(block, scope, ctx)
    local previous = ctx.scope
    ctx.scope = scope
    for i = 1, #block do
      if block[i] then resolveStmt(block[i], ctx) end
    end
    ctx.scope = previous
  end

  local main = {
    t = "Func",
    name = "<chunk>",
    params = {},
    vararg = true,
    body = ast.block,
    isMain = true,
    line = 0,
    col = 0,
  }
  local info = {
    upvals = {}, upvalRefs = {}, labels = {}, labelList = {}, gotos = {},
    loopDepth = 0, vararg = true,
  }
  main.info = info
  local rootCtx = { func = main, parent = nil, parentScope = nil, info = info, vararg = true }
  local rootScope = newScope(nil)
  resolveBlock(ast.block, rootScope, rootCtx)
  for i = 1, #info.gotos do
    local g = info.gotos[i]
    local lab = info.labels[g.name]
    if not lab then
      err(g.node, "no visible label '" .. g.name .. "' for goto")
    else
      g.node.labelObj = lab.node
    end
  end

  return {
    main = main,
    errors = self.errors,
    bindings = self.bindings,
    mainInfo = info,
  }
end

return Resolver
