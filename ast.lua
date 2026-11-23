-- ast.lua -- normalized AST contract for the v2 pipeline.
--
-- The parser produces a compact AST whose node kind lives in `t` and whose
-- structural fields have short names (`l`, `r`, `e`). Every later module sees
-- only the shape produced here:
--
--   { type = "BinaryOp", children = { left, right }, line = 12, col = 7, op = "+" }
--
-- Children are ordered as they appear in the source. Scalar metadata (names,
-- operator spelling, parameter lists) stays on the node.
local Ast = {}

local RENAME = {
  Bin = "BinaryOp",
  Un = "UnaryOp",
  True = "Boolean",
  False = "Boolean",
  CallStat = "CallStatement",
  Func = "Function",
  NumFor = "NumericFor",
  GenFor = "GenericFor",
  FunctionStat = "FunctionDeclaration",
  IfExpr = "IfExpression",
  Paren = "Parenthesized",
}
Ast.RENAME = RENAME

Ast.TYPES = {
  Chunk = true, Local = true, Assign = true, CallStatement = true,
  Do = true, While = true, Repeat = true, If = true,
  NumericFor = true, GenericFor = true, FunctionDeclaration = true,
  LocalFunction = true, Return = true, Break = true, Continue = true,
  Goto = true, Label = true,
  Name = true, Number = true, String = true, Boolean = true, Nil = true,
  Vararg = true, Index = true, Call = true, Function = true, Table = true,
  TableField = true, BinaryOp = true, UnaryOp = true, Parenthesized = true,
  IfExpression = true,
}

-- Structural fields are converted into `children`; everything else is copied.
local STRUCTURAL = {
  block = true, exprs = true, targets = true, call = true, cond = true,
  branches = true, orelse = true, from = true, to = true, step = true,
  target = true, func = true, obj = true, key = true, fn = true, args = true,
  l = true, r = true, e = true, fields = true,
}

-- Arrays of plain strings stay on the node.
local SCALAR_ARRAYS = { params = true, names = true, attrs = true }

local function isNode(v)
  return type(v) == "table" and (v.t ~= nil or v.type ~= nil)
end

local function norm(n)
  if n == nil then return nil end
  if not isNode(n) then return nil end
  local kind = n.t or n.type
  local typ = RENAME[kind] or kind or "Unknown"
  local out = { type = typ, line = n.line or 0, col = n.col or 0, children = {} }

  for k, v in pairs(n) do
    if k ~= "t" and k ~= "type" and k ~= "line" and k ~= "col" and
       k ~= "children" and k ~= "v" and not STRUCTURAL[k] then
      if type(v) ~= "table" then
        out[k] = v
      elseif SCALAR_ARRAYS[k] then
        local copy = {}
        for i = 1, #v do copy[i] = v[i] end
        out[k] = copy
      end
    end
  end
  if n.v ~= nil then out.value = n.v end
  if kind == "True" then out.value = true
  elseif kind == "False" then out.value = false end

  local kids = out.children
  local function add(x)
    local c = norm(x)
    if c then kids[#kids + 1] = c end
  end
  local function addList(list)
    if type(list) ~= "table" then return end
    for i = 1, #list do add(list[i]) end
  end

  if typ == "Chunk" then
    addList(n.block)
  elseif typ == "Local" then
    addList(n.exprs)
  elseif typ == "Assign" then
    out.targetCount = #(n.targets or {})
    addList(n.targets)
    addList(n.exprs)
  elseif typ == "CallStatement" then
    add(n.call)
  elseif typ == "Do" then
    addList(n.block)
  elseif typ == "While" then
    add(n.cond)
    addList(n.block)
  elseif typ == "Repeat" then
    addList(n.block)
    add(n.cond)
  elseif typ == "If" then
    out.branches = {}
    for i = 1, #(n.branches or {}) do
      local br = n.branches[i]
      out.branches[i] = { cond = #kids + 1, count = #(br.block or {}) }
      add(br.cond)
      addList(br.block)
    end
    out.elseCount = #(n.orelse or {})
    addList(n.orelse)
  elseif typ == "NumericFor" then
    out.hasStep = n.step ~= nil
    add(n.from)
    add(n.to)
    add(n.step)
    addList(n.block)
  elseif typ == "GenericFor" then
    out.exprCount = #(n.exprs or {})
    addList(n.exprs)
    addList(n.block)
  elseif typ == "FunctionDeclaration" then
    add(n.target)
    add(n.func)
  elseif typ == "LocalFunction" then
    add(n.func)
  elseif typ == "Return" then
    addList(n.exprs)
  elseif typ == "Index" then
    add(n.obj)
    add(n.key)
  elseif typ == "Call" then
    add(n.fn)
    addList(n.args)
  elseif typ == "Function" then
    addList(n.body)
  elseif typ == "Table" then
    local fields = n.fields or {}
    for i = 1, #fields do
      local f = fields[i]
      local value = norm(f.value)
      local field = {
        type = "TableField",
        kind = f.kind or "array",
        line = (value and value.line) or out.line,
        col = (value and value.col) or out.col,
        children = {},
      }
      if f.key then
        local key = norm(f.key)
        if key then
          field.key = key
          field.children[#field.children + 1] = key
        end
      end
      if value then field.children[#field.children + 1] = value end
      kids[#kids + 1] = field
    end
  elseif typ == "BinaryOp" then
    add(n.l)
    add(n.r)
  elseif typ == "UnaryOp" or typ == "Parenthesized" then
    add(n.e)
  elseif typ == "IfExpression" then
    out.branches = {}
    for i = 1, #(n.branches or {}) do
      local br = n.branches[i]
      out.branches[i] = { cond = #kids + 1, value = #kids + 2 }
      add(br.cond)
      add(br.value)
    end
    out.elseIndex = #kids + 1
    add(n.orelse)
  end

  return out
end

-- Convert a parser AST (root: { block = ... }) into the public contract.
function Ast.normalize(root)
  local src = root or {}
  return norm({ t = "Chunk", block = src.block or {}, line = 1, col = 1 })
end

function Ast.isNode(v)
  return type(v) == "table" and type(v.type) == "string" and
    type(v.children) == "table"
end

-- Depth-first walk; callback(node, depth, parent).
function Ast.walk(root, fn)
  local function visit(node, depth, parent)
    fn(node, depth, parent)
    for i = 1, #node.children do visit(node.children[i], depth + 1, node) end
  end
  if Ast.isNode(root) then visit(root, 0, nil) end
end

function Ast.find(root, typ)
  local hits = {}
  Ast.walk(root, function(node)
    if node.type == typ then hits[#hits + 1] = node end
  end)
  return hits
end

function Ast.count(root)
  local stats = { nodes = 0, maxDepth = 0, leaves = 0, byType = {} }
  Ast.walk(root, function(node, depth)
    stats.nodes = stats.nodes + 1
    if depth > stats.maxDepth then stats.maxDepth = depth end
    if #node.children == 0 then stats.leaves = stats.leaves + 1 end
    stats.byType[node.type] = (stats.byType[node.type] or 0) + 1
  end)
  return stats
end

-- Returns a list of contract violations; an empty list means the tree is sound.
function Ast.validate(root)
  local errors = {}
  local seen = {}
  local function fail(msg)
    if #errors < 50 then errors[#errors + 1] = msg end
  end
  local function visit(node, path)
    if type(node) ~= "table" then
      fail(path .. ": not a table")
      return
    end
    if seen[node] then
      fail(path .. ": cycle detected")
      return
    end
    seen[node] = true
    if type(node.type) ~= "string" or node.type == "" then
      fail(path .. ": missing type")
    elseif not Ast.TYPES[node.type] then
      fail(path .. ": unknown type '" .. tostring(node.type) .. "'")
    end
    if type(node.children) ~= "table" then
      fail(path .. ": missing children")
      return
    end
    if type(node.line) ~= "number" or node.line < 0 then
      fail(path .. ": invalid line")
    end
    if type(node.col) ~= "number" or node.col < 0 then
      fail(path .. ": invalid col")
    end
    if node.t ~= nil then
      fail(path .. ": legacy 't' field leaked")
    end
    for i = 1, #node.children do
      local child = node.children[i]
      if type(child) ~= "table" then
        fail(path .. "/" .. i .. ": child is not a node")
      else
        visit(child, path .. "/" .. i)
      end
    end
  end
  visit(root, "root")
  return errors
end

-- Human-readable tree, used by the module tests and the parse-only tooling.
function Ast.toText(root)
  local lines = {}
  Ast.walk(root, function(node, depth)
    local extra = ""
    if node.op then extra = extra .. " op=" .. tostring(node.op) end
    if node.name then extra = extra .. " name=" .. tostring(node.name) end
    if node.value ~= nil and node.type ~= "Boolean" then
      extra = extra .. " value=" .. tostring(node.value)
    end
    lines[#lines + 1] = string.rep("  ", depth) .. node.type ..
      " [" .. node.line .. ":" .. node.col .. "]" .. extra
  end)
  return table.concat(lines, "\n")
end

return Ast
