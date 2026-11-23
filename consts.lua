-- consts.lua -- number / boolean / nil hiding (layer 5).
--
-- Pipeline position:
--   analyze -> consts -> flatten -> opaque -> compiler
--
-- Constant hiding runs on the renamed AST *before* the structural passes. That
-- is the only order that keeps the build small: flatten and opaque synthesize
-- their own structural constants (state ids, router comparisons, predicate
-- seeds) which never reach the Lua output anyway -- they are compiled into
-- encrypted bytecode by M7/M9. Hiding them here would multiply the tree for no
-- gain. Layer 5 therefore owns every literal that came from the source.
--
-- Numbers are rewritten as mixed boolean-arithmetic splits that never contain
-- the original value: for `12345` one build may emit `(12340) + (5)`, another
-- `((4115) * 3) + (0)`, another `((12350) - (7)) + (2)`. The parts are computed
-- at build time on paper; the runtime only adds, subtracts and multiplies
-- small integers. Properties the templates guarantee:
--
--   * only `+ - *` are used, so Lua 5.1 hosts (no bitwise operators) work;
--   * every part and intermediate value stays inside 2^52, where doubles,
--     Lua 5.3 integers and Lua 5.4 integers all represent and compute exactly;
--   * no literal equal to the hidden value appears anywhere in the result;
--   * the expression is pure and side-effect free.
--
-- Non-integral numbers (0.1, 2.75, ...) use power-of-two scaling instead:
-- `n/2 + n/2`, `(n/2) * 2`, `n/4 * 4`. Halving and doubling are exact for every
-- normal double, so the round trip is bit-identical and `0.1 + 0.2 == 0.3`
-- keeps evaluating to false.
--
-- Booleans become integer comparisons (`(4 == 4)`, `(2 ~= 5)`, `(a * 0 ~= 0)`);
-- nil becomes an index of an empty string or table (`("")[1]`). Index and
-- comparison expressions always yield exactly one value, so a hidden nil in a
-- multi-value position (`f(1, nil)`, `return nil`) keeps its arity.
--
-- The module creates no identifiers (M2 is the single naming authority). Every
-- generated subtree is marked `synthetic = true`; the pass never descends into
-- such a subtree, so running it twice is a no-op.
local Ast = require("src.ast")

local Consts = {}

local DEFAULTS = {
  seed = 0x0C057A,
  enabled = true,
  numbers = true,
  booleans = true,
  nils = true,
  floats = true,
  prob = 1.0,
  intLimit = 4503599627370496, -- 2^52, exact in doubles and in 64-bit integers
  minFloat = 1e-300,
}

-- ---------------------------------------------------------------- AST helpers

local function node(typ, line, col, children)
  return { type = typ, line = line or 0, col = col or 0, children = children or {} }
end

-- Fengari's `%` returns the float subtype even for integer operands, so the
-- build-side LCGs hand back integral floats. An integral literal must keep the
-- integer subtype or the VM decodes it as a float and `tostring` prints
-- "55.0" where the host prints "55". Genuine float shapes opt out.
local tointeger = math.tointeger
local function intValue(value)
  if tointeger then
    local i = tointeger(value)
    if i ~= nil then return i end
  end
  return value
end

local function num(value, line, col, keepFloat)
  local n = node("Number", line, col)
  if not keepFloat then value = intValue(value) end
  n.value = value
  if value % 1 == 0 and math.abs(value) < 2 ^ 62 then
    -- %.0f: %d overflows the C integer range on 5.1/5.2 for large doubles.
    n.raw = string.format("%.0f", value)
  else
    n.raw = string.format("%.17g", value)
  end
  return n
end

local function str(value, line, col)
  local n = node("String", line, col)
  n.value = value
  return n
end

local function bin(op, a, b, line, col)
  local n = node("BinaryOp", line, col, { a, b })
  n.op = op
  return n
end

local function un(op, a, line, col)
  local n = node("UnaryOp", line, col, { a })
  n.op = op
  return n
end

-- Portable LCG: every intermediate stays below 2^53, so the sequence is
-- identical on 5.1 doubles and on 5.3/5.4 integers.
local function makeRng(seed)
  local state = (math.floor(math.abs(seed)) + 0x2545F491) % 4294967296
  return function(n)
    state = (state * 1664525 + 1013904223) % 4294967296
    return (state % n) + 1
  end
end

-- ------------------------------------------------------------------- integer
-- Each builder returns an expression tree whose evaluation equals `n` on every
-- host. Parts are chosen so the tree never contains `n` itself; the driver
-- rejects a shape if a random part happens to collide with the value.

local function offset(rng)
  local o = rng(127) - 64
  if o == 0 then o = 1 end
  return o
end

local INTEGER_SHAPES = {
  { id = "split-add", build = function(n, rng, l, c)
    local o = offset(rng)
    return bin("+", num(n + o, l, c), num(-o, l, c))
  end },
  { id = "split-sub", build = function(n, rng, l, c)
    local o = offset(rng)
    return bin("-", num(n + o, l, c), num(o, l, c))
  end },
  { id = "triple-add", build = function(n, rng, l, c)
    local o1, o2 = offset(rng), offset(rng)
    return bin("+", bin("+", num(n + o1 + o2, l, c), num(-o1, l, c)), num(-o2, l, c))
  end },
  { id = "triple-sub", build = function(n, rng, l, c)
    local o1, o2 = offset(rng), offset(rng)
    return bin("-", bin("-", num(n + o1, l, c), num(o1 + o2, l, c)), num(-o2, l, c))
  end },
  { id = "nested-add-sub", build = function(n, rng, l, c)
    local o1, o2 = offset(rng), offset(rng)
    return bin("+", num(n + o1, l, c), bin("-", num(o2, l, c), num(o1 + o2, l, c)))
  end },
  { id = "product-add", build = function(n, rng, l, c)
    local b = 2 + rng(8)
    local a = math.floor(n / b)
    return bin("+", bin("*", num(a, l, c), num(b, l, c)), num(n - a * b, l, c))
  end },
  { id = "product-sub", build = function(n, rng, l, c)
    local b = 2 + rng(8)
    local a = math.floor(n / b) + 1
    return bin("-", bin("*", num(a, l, c), num(b, l, c)), num(a * b - n, l, c))
  end },
  { id = "double-add", build = function(n, rng, l, c)
    local a = math.floor(n / 2)
    return bin("+", bin("*", num(a, l, c), num(2, l, c)), num(n - a * 2, l, c))
  end },
  { id = "quad-add", build = function(n, rng, l, c)
    local o1, o2 = offset(rng), offset(rng)
    return bin("+", bin("+", num(n + o1, l, c), num(-o1, l, c)),
      bin("+", num(o2, l, c), num(-o2, l, c)))
  end },
  { id = "sub-pair", build = function(n, rng, l, c)
    local o1, o2 = offset(rng), offset(rng)
    return bin("+", bin("-", num(n + o1, l, c), num(o1, l, c)),
      bin("-", num(o2, l, c), num(o2, l, c)))
  end },
  { id = "offset-chain", build = function(n, rng, l, c)
    local o1, o2 = offset(rng), offset(rng)
    return bin("+", bin("-", num(n + o1, l, c), num(o1 + o2, l, c)), num(o2, l, c))
  end },
  { id = "right-nested", build = function(n, rng, l, c)
    local o1, o2 = offset(rng), offset(rng)
    return bin("+", num(n + o1, l, c),
      bin("-", bin("-", num(o2, l, c), num(o2, l, c)), num(o1, l, c)))
  end },
}

-- --------------------------------------------------------------------- float
-- Halving/doubling and quartering are exact for normal doubles, so the value
-- survives the round trip bit for bit. The original literal never appears.

local FLOAT_SHAPES = {
  { id = "half-double-add", build = function(n, rng, l, c)
    local a = n / 2
    return bin("+", num(a, l, c, true), num(a, l, c, true))
  end },
  { id = "half-times-two", build = function(n, rng, l, c)
    local a = n / 2
    return bin("*", num(a, l, c, true), num(2, l, c, true))
  end },
  { id = "half-minus-negative", build = function(n, rng, l, c)
    local a = n / 2
    return bin("-", num(a, l, c, true), num(-a, l, c, true))
  end },
  { id = "quarter-times-four", build = function(n, rng, l, c)
    local a = n / 4
    return bin("*", num(a, l, c, true), num(4, l, c, true))
  end },
  { id = "negated-pair", build = function(n, rng, l, c)
    local a = -n / 2
    return un("-", bin("+", num(a, l, c, true), num(a, l, c, true)))
  end },
}

-- ------------------------------------------------------------------- boolean
-- Comparisons always evaluate to a real boolean.

local TRUE_SHAPES = {
  { id = "self-eq", build = function(rng, l, c)
    local a = rng(19) - 9
    return bin("==", num(a, l, c), num(a, l, c))
  end },
  { id = "diff-ne", build = function(rng, l, c)
    local a = rng(9)
    return bin("~=", num(a, l, c), num(a + 1 + rng(4), l, c))
  end },
  { id = "zero-product", build = function(rng, l, c)
    local a = rng(17) - 8
    return bin("==", bin("*", num(a, l, c), num(0, l, c)), num(0, l, c))
  end },
  { id = "less", build = function(rng, l, c)
    local a = rng(9) - 5
    return bin("<", num(a, l, c), num(a + 1 + rng(3), l, c))
  end },
  { id = "square-nonneg", build = function(rng, l, c)
    local a = rng(9) - 5
    return bin(">=", bin("*", num(a, l, c), num(a, l, c)), num(0, l, c))
  end },
}

local FALSE_SHAPES = {
  { id = "diff-eq", build = function(rng, l, c)
    local a = rng(9)
    return bin("==", num(a, l, c), num(a + 1, l, c))
  end },
  { id = "self-ne", build = function(rng, l, c)
    local a = rng(19) - 9
    return bin("~=", num(a, l, c), num(a, l, c))
  end },
  { id = "zero-product-ne", build = function(rng, l, c)
    local a = rng(9)
    return bin("~=", bin("*", num(a, l, c), num(0, l, c)), num(0, l, c))
  end },
  { id = "greater", build = function(rng, l, c)
    local a = rng(9) - 5
    return bin(">", num(a, l, c), num(a + 1 + rng(3), l, c))
  end },
  { id = "square-neg", build = function(rng, l, c)
    local a = rng(9) - 5
    return bin("<", bin("*", num(a, l, c), num(a, l, c)), num(0, l, c))
  end },
}

-- ----------------------------------------------------------------------- nil
-- Index expressions yield exactly one value (nil), so arity is preserved in
-- call arguments, return lists and table constructors.

local NIL_SHAPES = {
  { id = "empty-string-index", build = function(rng, l, c)
    return node("Index", l, c, { str("", l, c), num(1, l, c) })
  end },
  { id = "empty-table-index", build = function(rng, l, c)
    return node("Index", l, c, { node("Table", l, c, {}), num(1, l, c) })
  end },
  { id = "empty-string-zero", build = function(rng, l, c)
    return node("Index", l, c, { str("", l, c), num(0, l, c) })
  end },
  { id = "empty-table-key", build = function(rng, l, c)
    return node("Index", l, c, { node("Table", l, c, {}), str("", l, c) })
  end },
}

Consts.INTEGER_SHAPES = INTEGER_SHAPES
Consts.FLOAT_SHAPES = FLOAT_SHAPES
Consts.TRUE_SHAPES = TRUE_SHAPES
Consts.FALSE_SHAPES = FALSE_SHAPES
Consts.NIL_SHAPES = NIL_SHAPES

-- -------------------------------------------------------------------- build

local function containsValue(expr, value)
  local hit = false
  Ast.walk(expr, function(n)
    if n.type == "Number" and n.value == value then hit = true end
  end)
  return hit
end

local function buildInteger(n, rng, line, col)
  for _ = 1, 16 do
    local shape = INTEGER_SHAPES[rng(#INTEGER_SHAPES)]
    local expr = shape.build(n, rng, line, col)
    if expr and not containsValue(expr, n) then return expr, shape.id end
  end
  -- Deterministic fallback: no part equals n for any integer n.
  if n >= 2 then
    return bin("+", num(n - 1, line, col), num(1, line, col)), "fallback-add"
  elseif n <= -2 then
    return bin("-", num(n + 1, line, col), num(1, line, col)), "fallback-sub"
  elseif n == 1 then
    return bin("-", num(3, line, col), num(2, line, col)), "fallback-one"
  elseif n == -1 then
    return bin("-", num(1, line, col), num(2, line, col)), "fallback-minus-one"
  end
  return bin("-", num(2, line, col), num(2, line, col)), "fallback-zero"
end

local function buildFloat(n, rng, line, col)
  local shape = FLOAT_SHAPES[rng(#FLOAT_SHAPES)]
  return shape.build(n, rng, line, col), shape.id
end

-- ----------------------------------------------------------------- transform

local function hideNumber(literal, ctx)
  local value = literal.value
  local line, col = literal.line or 0, literal.col or 0

  if type(value) ~= "number" or value ~= value or
     value == math.huge or value == -math.huge then
    ctx.stats.skipped.unsupported = ctx.stats.skipped.unsupported + 1
    return nil
  end

  -- Any arithmetic rewrite of -0.0 may land on +0.0, and `1/x` observes the
  -- difference, so the literal is left alone.
  if value == 0 and 1 / value < 0 then
    ctx.stats.skipped.unsupported = ctx.stats.skipped.unsupported + 1
    return nil
  end

  local raw = literal.raw
  -- The AST is host-independent: the literal text decides whether an integral
  -- value must stay a float, so a build on 5.1 still yields 5.3+ subtype
  -- behaviour.
  local isFloat
  if type(raw) == "string" and raw ~= "" then
    if raw:find("^0[xX]") then
      isFloat = raw:find("[pP%.]") ~= nil
    else
      isFloat = raw:find("[%.eE]") ~= nil
    end
  else
    isFloat = math.type ~= nil and math.type(value) == "float"
  end

  local function hideFloat()
    if not ctx.cfg.floats then
      ctx.stats.skipped.float = ctx.stats.skipped.float + 1
      return nil
    end
    local expr, id = buildFloat(value, ctx.rng, line, col)
    ctx.stats.shapes[id] = (ctx.stats.shapes[id] or 0) + 1
    return expr
  end

  if value % 1 == 0 then
    if value < -ctx.cfg.intLimit or value > ctx.cfg.intLimit then
      ctx.stats.skipped.huge = ctx.stats.skipped.huge + 1
      return nil
    end
    -- A float literal such as 2.0 must stay a float: the integer shapes would
    -- change the subtype on 5.3+ and therefore tostring output.
    if isFloat then return hideFloat() end
    local expr, id = buildInteger(value, ctx.rng, line, col)
    ctx.stats.shapes[id] = (ctx.stats.shapes[id] or 0) + 1
    return expr
  end

  if math.abs(value) < ctx.cfg.minFloat then
    ctx.stats.skipped.float = ctx.stats.skipped.float + 1
    return nil
  end
  return hideFloat()
end

local function decorate(expr)
  expr.synthetic = true
  return expr
end

local function passesGate(ctx)
  if ctx.cfg.prob >= 1 then return true end
  if ctx.rng(1000) > ctx.cfg.prob * 1000 then
    ctx.stats.skipped.prob = ctx.stats.skipped.prob + 1
    return false
  end
  return true
end

local function visit(parent, ctx)
  local kids = parent.children
  for i = 1, #kids do
    local child = kids[i]
    local t = child.type

    if child.synthetic then
      -- Produced by this pass earlier; never re-hide.
    elseif t == "Number" then
      if ctx.cfg.numbers and passesGate(ctx) then
        local repl = hideNumber(child, ctx)
        if repl then
          local old = kids[i]
          kids[i] = decorate(repl)
          if parent.type == "TableField" and i == 1 and parent.key == old then
            parent.key = kids[i]
          end
          ctx.stats.numbers = ctx.stats.numbers + 1
          ctx.stats.total = ctx.stats.total + 1
          ctx.stats.added = ctx.stats.added + Ast.count(repl).nodes - 1
        end
      end
    elseif t == "Boolean" then
      if ctx.cfg.booleans and passesGate(ctx) then
        local shapes = child.value and TRUE_SHAPES or FALSE_SHAPES
        local shape = shapes[ctx.rng(#shapes)]
        local repl = decorate(shape.build(ctx.rng, child.line or 0, child.col or 0))
        kids[i] = repl
        ctx.stats.booleans = ctx.stats.booleans + 1
        ctx.stats.total = ctx.stats.total + 1
        ctx.stats.shapes[shape.id] = (ctx.stats.shapes[shape.id] or 0) + 1
        ctx.stats.added = ctx.stats.added + Ast.count(repl).nodes - 1
      end
    elseif t == "Nil" then
      if ctx.cfg.nils and passesGate(ctx) then
        local shape = NIL_SHAPES[ctx.rng(#NIL_SHAPES)]
        local repl = decorate(shape.build(ctx.rng, child.line or 0, child.col or 0))
        kids[i] = repl
        ctx.stats.nils = ctx.stats.nils + 1
        ctx.stats.total = ctx.stats.total + 1
        ctx.stats.shapes[shape.id] = (ctx.stats.shapes[shape.id] or 0) + 1
        ctx.stats.added = ctx.stats.added + Ast.count(repl).nodes - 1
      end
    else
      visit(child, ctx)
    end
  end
end

-- ----------------------------------------------------------------------- run

function Consts.run(ast, opts)
  local cfg = {}
  for k, v in pairs(DEFAULTS) do cfg[k] = v end
  for k, v in pairs(opts or {}) do cfg[k] = v end

  local stats = {
    numbers = 0,
    booleans = 0,
    nils = 0,
    total = 0,
    added = 0,
    shapes = {},
    skipped = { disabled = 0, prob = 0, float = 0, huge = 0, unsupported = 0 },
  }

  if not cfg.enabled or not Ast.isNode(ast) then
    stats.skipped.disabled = 1
    return stats
  end

  local ctx = { cfg = cfg, stats = stats, rng = makeRng(cfg.seed) }

  visit(ast, ctx)
  return stats
end

return Consts
