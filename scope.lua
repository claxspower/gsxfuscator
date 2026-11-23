-- scope.lua -- lexical scope analysis and collision-free renaming (layer 2).
--
-- Pipeline position:
--   parser -> ast.normalize -> scope.analyze -> scope.apply -> flatten ...
--
-- analyze() never mutates names. It annotates the tree in place so later
-- passes know what every identifier means:
--
--   Name            .bindingId, .refKind ("local" | "upvalue" | "global")
--   Local           .bindingIds[i]  (aligned with .names)
--   Function        .bindingIds[i]  (aligned with .params, "self" included)
--   LocalFunction   .bindingId
--   NumericFor      .bindingId      (the loop variable)
--   GenericFor      .bindingIds[i]  (aligned with .names)
--   Label / Goto    .bindingId      (goto points at its target label)
--
-- apply() then rewrites declarations and references to the generated names.
-- Globals are never renamed (they are the host API), and `_ENV` / `_G` keep
-- their spelling even when a program shadows them with a local.
--
-- Lua rules implemented here:
--   * `local x = x` -- the initializer sees the *outer* x.
--   * `local function f` -- f is visible inside its own body.
--   * repeat/until -- body locals are visible in the condition.
--   * loop variables are scoped to the loop body.
--   * upvalues follow the transitive chain through every intermediate function.
--   * labels are scoped to their block, visible in nested blocks, never across
--     a function boundary; break/continue must sit inside a loop.
local Ast = require("src.ast")

local Scope = {}

local ALWAYS_RESERVED = { ["_ENV"] = true, ["_G"] = true }

local function addToList(result, value)
  result[#result + 1] = value
end

-- Reserve every identifier that appears anywhere in the source so a generated
-- name can never accidentally collide with user code or a global it calls.
local function collectReserved(ast, opts)
  local taken = {}
  for name in pairs(ALWAYS_RESERVED) do taken[name] = true end
  if opts.reserved then
    if opts.reserved[1] ~= nil then
      for i = 1, #opts.reserved do taken[opts.reserved[i]] = true end
    else
      for name in pairs(opts.reserved) do taken[name] = true end
    end
  end

  local function take(name)
    if type(name) == "string" and name ~= "" then taken[name] = true end
  end

  Ast.walk(ast, function(node)
    local t = node.type
    if t == "Name" then
      take(node.value)
    elseif t == "Local" then
      for i = 1, #(node.names or {}) do take(node.names[i]) end
    elseif t == "Function" then
      for i = 1, #(node.params or {}) do take(node.params[i]) end
    elseif t == "LocalFunction" then
      take(node.name)
    elseif t == "NumericFor" then
      take(node.var)
    elseif t == "GenericFor" then
      for i = 1, #(node.names or {}) do take(node.names[i]) end
    elseif t == "Label" or t == "Goto" then
      take(node.name)
    end
  end)
  return taken
end

-- Seeds arrive as floats on 5.3+ (os.clock) and math.floor may keep the float
-- subtype (Fengari does), which `%x` rejects. Digits are picked by hand.
local HEXDIGITS = {
  "0", "1", "2", "3", "4", "5", "6", "7",
  "8", "9", "a", "b", "c", "d", "e", "f",
}

local function hex8(n)
  n = math.floor(tonumber(n) or 0) % 4294967296
  local out = {}
  for i = 8, 1, -1 do
    local digit = n % 16
    out[i] = HEXDIGITS[digit + 1]
    n = (n - digit) / 16
  end
  return table.concat(out)
end

-- LCG: state = state * 1664525 + 1013904223 (mod 2^32). All intermediates stay
-- below 2^53, so this is exact on every Lua version and on Luau.
local function makeGenerator(seed, prefix, taken)
  local state = math.floor(math.abs(seed or 0x5EED1234)) % 4294967296
  local collisions = 0
  return function()
    while true do
      state = (state * 1664525 + 1013904223) % 4294967296
      local name = prefix .. hex8(state)
      if not taken[name] then
        taken[name] = true
        return name
      end
      collisions = collisions + 1
    end
  end, function() return collisions end
end

function Scope.analyze(ast, opts)
  opts = opts or {}
  local prefix = opts.prefix or "_0x"
  if not prefix:match("^[%a_][%w_]*$") then prefix = "_0x" end

  local result = {
    ast = ast,
    bindings = {},
    functions = {},
    scopes = {},
    globals = {},
    globalRefs = 0,
    errors = {},
    renames = {},
    stats = {},
  }
  local taken = collectReserved(ast, opts)

  local function addError(node, msg)
    addToList(result.errors, {
      line = (node and node.line) or 0,
      col = (node and node.col) or 0,
      msg = msg,
    })
  end

  local function newScope(kind, parent, functionId)
    local scope = {
      id = #result.scopes + 1,
      parent = parent,
      kind = kind,
      functionId = functionId,
      vars = {},
      labels = {},
    }
    result.scopes[scope.id] = scope
    return scope
  end

  local rootFunction = {
    id = 1, parentId = nil, node = ast,
    upvalues = {}, upvalueSet = {}, paramBindingIds = {},
  }
  result.functions[1] = rootFunction
  local rootScope = newScope("chunk", nil, 1)
  rootFunction.scopeId = rootScope.id

  local function declare(scope, name, kind, node)
    local binding = {
      id = #result.bindings + 1,
      name = name,
      kind = kind,
      scopeId = scope.id,
      ownerFunctionId = scope.functionId,
      captured = false,
      refCount = 0,
      line = (node and node.line) or 0,
      col = (node and node.col) or 0,
      reserved = ALWAYS_RESERVED[name] == true,
      newName = nil,
    }
    addToList(result.bindings, binding)
    if kind ~= "label" then scope.vars[name] = binding end
    if kind == "param" then
      addToList(result.functions[scope.functionId].paramBindingIds, binding.id)
    end
    return binding
  end

  -- Variables follow the whole lexical chain, including outer functions: that is
  -- what makes a capture an upvalue. Labels are different and stop at the
  -- function boundary (see resolveLabel).
  local function resolveVar(scope, name)
    local s = scope
    while s do
      local binding = s.vars[name]
      if binding then return binding end
      s = s.parent
    end
    return nil
  end

  local function resolveLabel(scope, name)
    local s = scope
    while s and s.functionId == scope.functionId do
      local binding = s.labels[name]
      if binding then return binding end
      s = s.parent
    end
    return nil
  end

  local function noteReference(scope, node)
    local binding = resolveVar(scope, node.value)
    if not binding then
      node.refKind = "global"
      node.bindingId = nil
      result.globals[node.value] = (result.globals[node.value] or 0) + 1
      result.globalRefs = result.globalRefs + 1
      return
    end
    binding.refCount = binding.refCount + 1
    node.bindingId = binding.id
    if binding.ownerFunctionId == scope.functionId then
      node.refKind = "local"
      return
    end
    node.refKind = "upvalue"
    binding.captured = true
    local fn = result.functions[scope.functionId]
    while fn and fn.id ~= binding.ownerFunctionId do
      if not fn.upvalueSet[binding.id] then
        fn.upvalueSet[binding.id] = true
        addToList(fn.upvalues, binding.id)
      end
      fn = result.functions[fn.parentId]
    end
  end

  local walkExpr, walkStmt, walkBlock

  local function enterFunction(node, parentScope)
    local fn = {
      id = #result.functions + 1,
      parentId = parentScope.functionId,
      node = node,
      upvalues = {}, upvalueSet = {}, paramBindingIds = {},
    }
    result.functions[fn.id] = fn
    local scope = newScope("function", parentScope, fn.id)
    fn.scopeId = scope.id

    local params = node.params or {}
    node.bindingIds = {}
    for i = 1, #params do
      node.bindingIds[i] = declare(scope, params[i], "param", node).id
    end
    walkBlock(node.children, scope, 0)
  end

  walkBlock = function(list, scope, loopDepth, from, to)
    from = from or 1
    to = to or #list
    -- Labels first: a goto may appear before the label it targets.
    for i = from, to do
      local st = list[i]
      if st and st.type == "Label" then
        if scope.labels[st.name] then
          addError(st, "duplicate label '" .. tostring(st.name) .. "'")
        else
          scope.labels[st.name] = declare(scope, st.name, "label", st)
        end
      end
    end
    for i = from, to do
      local st = list[i]
      if st then walkStmt(st, scope, loopDepth) end
    end
  end

  walkStmt = function(node, scope, loopDepth)
    local t = node.type
    if t == "Local" then
      for i = 1, #node.children do walkExpr(node.children[i], scope) end
      node.bindingIds = {}
      local names = node.names or {}
      for i = 1, #names do
        node.bindingIds[i] = declare(scope, names[i], "local", node).id
      end
    elseif t == "Assign" then
      for i = 1, #node.children do walkExpr(node.children[i], scope) end
    elseif t == "CallStatement" then
      walkExpr(node.children[1], scope)
    elseif t == "Do" then
      walkBlock(node.children, newScope("block", scope, scope.functionId), loopDepth)
    elseif t == "While" then
      walkExpr(node.children[1], scope)
      local inner = newScope("loop", scope, scope.functionId)
      walkBlock(node.children, inner, loopDepth + 1, 2)
    elseif t == "Repeat" then
      local inner = newScope("loop", scope, scope.functionId)
      local n = #node.children
      walkBlock(node.children, inner, loopDepth + 1, 1, n - 1)
      walkExpr(node.children[n], inner)
    elseif t == "If" then
      local index = 1
      local branches = node.branches or {}
      for i = 1, #branches do
        local branch = branches[i]
        walkExpr(node.children[index], scope)
        local inner = newScope("block", scope, scope.functionId)
        walkBlock(node.children, inner, loopDepth, index + 1, index + branch.count)
        index = index + 1 + branch.count
      end
      if (node.elseCount or 0) > 0 then
        local inner = newScope("block", scope, scope.functionId)
        walkBlock(node.children, inner, loopDepth, index, index + node.elseCount - 1)
      end
    elseif t == "NumericFor" then
      walkExpr(node.children[1], scope)
      walkExpr(node.children[2], scope)
      local start = 3
      if node.hasStep then
        walkExpr(node.children[3], scope)
        start = 4
      end
      local inner = newScope("loop", scope, scope.functionId)
      node.bindingId = declare(inner, node.var, "loop", node).id
      walkBlock(node.children, inner, loopDepth + 1, start, #node.children)
    elseif t == "GenericFor" then
      local exprCount = node.exprCount or 0
      for i = 1, exprCount do walkExpr(node.children[i], scope) end
      local inner = newScope("loop", scope, scope.functionId)
      node.bindingIds = {}
      local names = node.names or {}
      for i = 1, #names do
        node.bindingIds[i] = declare(inner, names[i], "loop", node).id
      end
      walkBlock(node.children, inner, loopDepth + 1, exprCount + 1, #node.children)
    elseif t == "FunctionDeclaration" then
      walkExpr(node.children[1], scope)
      enterFunction(node.children[2], scope)
    elseif t == "LocalFunction" then
      local binding = declare(scope, node.name, "local", node)
      node.bindingId = binding.id
      enterFunction(node.children[1], scope)
    elseif t == "Return" then
      for i = 1, #node.children do walkExpr(node.children[i], scope) end
    elseif t == "Break" or t == "Continue" then
      if loopDepth <= 0 then
        addError(node, "'" .. t:lower() .. "' outside a loop")
      end
    elseif t == "Goto" then
      local target = resolveLabel(scope, node.name)
      if target then
        target.refCount = target.refCount + 1
        node.bindingId = target.id
      else
        addError(node, "no visible label '" .. tostring(node.name) .. "' for goto")
      end
    elseif t == "Label" then
      local binding = scope.labels[node.name]
      if binding then node.bindingId = binding.id end
    else
      addError(node, "unhandled statement type '" .. tostring(t) .. "'")
    end
  end

  walkExpr = function(node, scope)
    local t = node.type
    if t == "Name" then
      noteReference(scope, node)
    elseif t == "Function" then
      enterFunction(node, scope)
    elseif t == "Index" or t == "Call" or t == "BinaryOp" or t == "UnaryOp" or
           t == "Parenthesized" or t == "Table" or t == "TableField" or
           t == "IfExpression" then
      for i = 1, #node.children do walkExpr(node.children[i], scope) end
    elseif t == "Number" or t == "String" or t == "Boolean" or t == "Nil" or
           t == "Vararg" then
      -- Literals carry no bindings.
    else
      addError(node, "unexpected expression type '" .. tostring(t) .. "'")
    end
  end

  walkBlock(ast.children, rootScope, 0)

  local nextName, getCollisions = makeGenerator(opts.seed, prefix, taken)
  for i = 1, #result.bindings do
    local binding = result.bindings[i]
    if binding.reserved then
      binding.newName = binding.name
    else
      binding.newName = nextName()
      addToList(result.renames, {
        bindingId = binding.id,
        from = binding.name,
        to = binding.newName,
        kind = binding.kind,
        line = binding.line,
        col = binding.col,
      })
    end
  end

  local stats = {
    scopes = #result.scopes,
    functions = #result.functions,
    bindings = #result.bindings,
    locals = 0, params = 0, loops = 0, labels = 0,
    captured = 0, upvalues = 0,
    globals = 0, globalRefs = result.globalRefs,
    renamed = 0, reservedBindings = 0,
    collisions = getCollisions(),
  }
  for i = 1, #result.bindings do
    local binding = result.bindings[i]
    if binding.kind == "local" then stats.locals = stats.locals + 1
    elseif binding.kind == "param" then stats.params = stats.params + 1
    elseif binding.kind == "loop" then stats.loops = stats.loops + 1
    elseif binding.kind == "label" then stats.labels = stats.labels + 1 end
    if binding.captured then stats.captured = stats.captured + 1 end
    if binding.reserved then
      stats.reservedBindings = stats.reservedBindings + 1
    else
      stats.renamed = stats.renamed + 1
    end
  end
  for i = 1, #result.functions do
    stats.upvalues = stats.upvalues + #result.functions[i].upvalues
  end
  for _ in pairs(result.globals) do stats.globals = stats.globals + 1 end
  result.stats = stats

  return result
end

-- Rewrite the annotated tree in place. Safe to call once per analyze() result.
function Scope.apply(result)
  local bindings = result.bindings
  Ast.walk(result.ast, function(node)
    local t = node.type
    if t == "Name" then
      if node.bindingId then
        node.value = bindings[node.bindingId].newName
      end
    elseif t == "Local" then
      local ids = node.bindingIds or {}
      for i = 1, #ids do
        node.names[i] = bindings[ids[i]].newName
      end
    elseif t == "Function" then
      local ids = node.bindingIds or {}
      for i = 1, #ids do
        node.params[i] = bindings[ids[i]].newName
      end
    elseif t == "LocalFunction" then
      if node.bindingId then
        node.name = bindings[node.bindingId].newName
      end
    elseif t == "NumericFor" then
      if node.bindingId then
        node.var = bindings[node.bindingId].newName
      end
    elseif t == "GenericFor" then
      local ids = node.bindingIds or {}
      for i = 1, #ids do
        node.names[i] = bindings[ids[i]].newName
      end
    elseif t == "Label" or t == "Goto" then
      if node.bindingId then
        node.name = bindings[node.bindingId].newName
      end
    end
  end)
  return result.ast
end

return Scope
