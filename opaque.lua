-- opaque.lua -- MBA opaque predicates (layer 4).
--
-- Pipeline position:
--   flatten.run -> opaque.run -> consts -> strings -> ...
--
-- run() wraps every condition position (if / elseif, while, repeat-until and
-- Luau if-expressions) with a mixed boolean-arithmetic identity that is
-- constant by construction:
--
--   if (cond) and ((v * (v + 1)) % 2 == 0) then      -- always-true guard
--   if (cond) or  ((v * v - v) % 2 ~= 0) then        -- always-false guard
--   if not (not (cond) or ((v * 3 + 7) % 3 == 2)) then
--
-- `v` is a generated integer local, declared once per function (or the main
-- chunk) that owns at least one rewritten condition. The identities only use
-- + - * % == ~= on that integer: they hold for every integer (including
-- negative ones, where Lua's `%` is a floor modulus) and on every supported
-- host, and they avoid the bitwise operators Lua 5.1 does not have.
--
-- Why this is safe:
--   * only truthiness is taken from a condition, so all wrappers preserve
--     "truthy stays truthy, falsy stays falsy" (0 and "" are truthy in Lua);
--   * the original condition is evaluated exactly once, first, so side
--     effects and short-circuits are unchanged;
--   * predicates are pure arithmetic on a local, never on user data, so no
--     NaN / float / overflow behaviour can leak into the program;
--   * one extra local per owner stays inside the 200-local register budget;
--     owners already near the limit are skipped.
--
-- Conditions are not evaluated at build time: the tables are checked by the
-- acceptance suite across a range of positive and negative `v` values.
local Ast = require("src.ast")

local Opaque = {}

-- Seeds can arrive as floats (os.clock on 5.3+) and math.floor may keep the
-- float subtype (Fengari does), which `%x` and `%d` reject. Format by hand.
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

local function numberRaw(value)
  value = tonumber(value) or 0
  if value % 1 == 0 and math.abs(value) < 2 ^ 62 then
    return string.format("%.0f", value)
  end
  return string.format("%.17g", value)
end

local DEFAULTS = {
  seed = 0x0FA0DE,
  prefix = "_0x",
  enabled = true,
  prob = 1.0,
  maxLocals = 190,
  -- A predicate wrapped around a loop condition is re-evaluated on every
  -- iteration, and inside the VM each extra operator is another interpreted
  -- instruction. Presets keep the wrap on non-loop conditions only.
  loopConditions = true,
}

-- ---------------------------------------------------------------- AST helpers

local function node(typ, line, col, children)
  return { type = typ, line = line or 0, col = col or 0, children = children or {} }
end

-- Fengari's `%%` returns the float subtype even for integer operands, so the
-- build-side LCGs hand back integral floats. Normalise them: these passes only
-- synthesize integers, and a float-typed one would decode as a float in the VM
-- and change `tostring` output.
local tointeger = math.tointeger
local function intValue(value)
  if tointeger then
    local i = tointeger(value)
    if i ~= nil then return i end
  end
  return value
end

local function num(value, line, col)
  local n = node("Number", line, col)
  n.value = intValue(value)
  n.raw = numberRaw(n.value)
  return n
end

local function nam(value, line, col)
  local n = node("Name", line, col)
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

-- ------------------------------------------------------------------- templates
-- Every builder creates fresh nodes (the AST validator rejects shared nodes)
-- and is an identity over the integers.

local function vv(v, l, c)
  return nam(v, l, c)
end

local function T(id, build)
  return { id = id, truth = true, build = build }
end

local function F(id, build)
  return { id = id, truth = false, build = build }
end

local TRUE_TEMPLATES = {
  T("parity-idempotent", function(v, l, c)
    return bin("==",
      bin("*", bin("%", vv(v, l, c), num(2, l, c)), bin("%", vv(v, l, c), num(2, l, c))),
      bin("%", vv(v, l, c), num(2, l, c)))
  end),
  T("consecutive-even", function(v, l, c)
    return bin("==",
      bin("%", bin("*", vv(v, l, c), bin("+", vv(v, l, c), num(1, l, c))), num(2, l, c)),
      num(0, l, c))
  end),
  T("even-difference", function(v, l, c)
    return bin("==",
      bin("%", bin("-", bin("*", vv(v, l, c), vv(v, l, c)), vv(v, l, c)), num(2, l, c)),
      num(0, l, c))
  end),
  T("mod3-shift", function(v, l, c)
    return bin("==",
      bin("%", bin("+", bin("*", vv(v, l, c), num(3, l, c)), num(7, l, c)), num(3, l, c)),
      num(1, l, c))
  end),
  T("three-product", function(v, l, c)
    local prod = bin("*",
      bin("*", vv(v, l, c), bin("+", vv(v, l, c), num(1, l, c))),
      bin("+", vv(v, l, c), num(2, l, c)))
    return bin("==", bin("%", prod, num(6, l, c)), num(0, l, c))
  end),
  T("square-expand", function(v, l, c)
    local lhs = bin("-",
      bin("-",
        bin("*", bin("+", vv(v, l, c), num(1, l, c)), bin("+", vv(v, l, c), num(1, l, c))),
        bin("*", vv(v, l, c), vv(v, l, c))),
      bin("*", vv(v, l, c), num(2, l, c)))
    return bin("==", lhs, num(1, l, c))
  end),
  T("mod4-nonresidue", function(v, l, c)
    local m = bin("%", vv(v, l, c), num(4, l, c))
    return bin("~=", bin("%", bin("*", m, bin("%", vv(v, l, c), num(4, l, c))), num(4, l, c)),
      num(3, l, c))
  end),
  T("double-identity", function(v, l, c)
    return bin("==",
      bin("-",
        bin("*", vv(v, l, c), bin("+", vv(v, l, c), num(1, l, c))),
        bin("*", vv(v, l, c), bin("-", vv(v, l, c), num(1, l, c)))),
      bin("*", vv(v, l, c), num(2, l, c)))
  end),
  T("square-parity", function(v, l, c)
    return bin("==",
      bin("%", bin("*", vv(v, l, c), vv(v, l, c)), num(2, l, c)),
      bin("%", vv(v, l, c), num(2, l, c)))
  end),
  T("odd-guard", function(v, l, c)
    local even = bin("+", bin("*", vv(v, l, c), vv(v, l, c)), vv(v, l, c))
    return bin("==", bin("%", bin("+", even, num(1, l, c)), num(2, l, c)), num(1, l, c))
  end),
  T("mod4-square", function(v, l, c)
    return bin("~=",
      bin("%", bin("*", vv(v, l, c), vv(v, l, c)), num(4, l, c)),
      num(3, l, c))
  end),
}

local FALSE_TEMPLATES = {
  F("parity-flip", function(v, l, c)
    return bin("==",
      bin("%", bin("*", vv(v, l, c), bin("+", vv(v, l, c), num(1, l, c))), num(2, l, c)),
      num(1, l, c))
  end),
  F("even-diff-nonzero", function(v, l, c)
    return bin("~=",
      bin("%", bin("-", bin("*", vv(v, l, c), vv(v, l, c)), vv(v, l, c)), num(2, l, c)),
      num(0, l, c))
  end),
  F("square-expand-plus", function(v, l, c)
    local lhs = bin("-",
      bin("-",
        bin("*", bin("+", vv(v, l, c), num(1, l, c)), bin("+", vv(v, l, c), num(1, l, c))),
        bin("*", vv(v, l, c), vv(v, l, c))),
      bin("*", vv(v, l, c), num(2, l, c)))
    return bin("==", lhs, num(2, l, c))
  end),
  F("mod3-miss", function(v, l, c)
    return bin("==",
      bin("%", bin("+", bin("*", vv(v, l, c), num(3, l, c)), num(7, l, c)), num(3, l, c)),
      num(2, l, c))
  end),
  F("mod4-residue", function(v, l, c)
    local m = bin("%", vv(v, l, c), num(4, l, c))
    return bin("==", bin("%", bin("*", m, bin("%", vv(v, l, c), num(4, l, c))), num(4, l, c)),
      num(3, l, c))
  end),
  F("three-product-miss", function(v, l, c)
    local prod = bin("*",
      bin("*", vv(v, l, c), bin("+", vv(v, l, c), num(1, l, c))),
      bin("+", vv(v, l, c), num(2, l, c)))
    return bin("==", bin("%", prod, num(6, l, c)), num(3, l, c))
  end),
  F("double-identity-plus", function(v, l, c)
    return bin("==",
      bin("-",
        bin("*", vv(v, l, c), bin("+", vv(v, l, c), num(1, l, c))),
        bin("*", vv(v, l, c), bin("-", vv(v, l, c), num(1, l, c)))),
      bin("+", bin("*", vv(v, l, c), num(2, l, c)), num(1, l, c)))
  end),
  F("square-parity-flip", function(v, l, c)
    return bin("==",
      bin("%", bin("*", vv(v, l, c), vv(v, l, c)), num(2, l, c)),
      bin("%", bin("+", vv(v, l, c), num(1, l, c)), num(2, l, c)))
  end),
  F("odd-guard-miss", function(v, l, c)
    local even = bin("+", bin("*", vv(v, l, c), vv(v, l, c)), vv(v, l, c))
    return bin("==", bin("%", bin("+", even, num(1, l, c)), num(2, l, c)), num(0, l, c))
  end),
  F("mod4-square-miss", function(v, l, c)
    return bin("==",
      bin("%", bin("*", vv(v, l, c), vv(v, l, c)), num(4, l, c)),
      num(3, l, c))
  end),
}

Opaque.TRUE_TEMPLATES = TRUE_TEMPLATES
Opaque.FALSE_TEMPLATES = FALSE_TEMPLATES

-- Truthiness-preserving ways to attach a guard to a condition. Each builder
-- consumes the condition exactly once and never changes when it is evaluated.
local WRAPPERS = {
  { id = "and-true", build = function(C, T)
    return bin("and", C, T)
  end },
  { id = "or-false", build = function(C, T, F)
    return bin("or", C, F)
  end },
  { id = "not-not-or", build = function(C, T, F)
    return un("not", bin("or", un("not", C), F))
  end },
  { id = "and-true-or-false", build = function(C, T, F)
    return bin("or", bin("and", C, T), F)
  end },
  { id = "not-false-or-not", build = function(C, T, F)
    return un("not", bin("or", F, un("not", C)))
  end },
  { id = "or-false-and-true", build = function(C, T, F)
    return bin("and", bin("or", C, F), T)
  end },
  { id = "not-not-and", build = function(C, T, F)
    return un("not", bin("and", un("not", C), T))
  end },
}

Opaque.WRAPPERS = WRAPPERS

-- ---------------------------------------------------------------- primitives

local function collectTaken(ast)
  local taken = { ["_ENV"] = true, ["_G"] = true }
  local function take(v)
    if type(v) == "string" and v ~= "" then taken[v] = true end
  end
  Ast.walk(ast, function(n)
    local t = n.type
    if t == "Name" then
      take(n.value)
    elseif t == "Local" then
      for i = 1, #(n.names or {}) do take(n.names[i]) end
    elseif t == "Function" then
      for i = 1, #(n.params or {}) do take(n.params[i]) end
    elseif t == "LocalFunction" then
      take(n.name)
    elseif t == "NumericFor" then
      take(n.var)
    elseif t == "GenericFor" then
      for i = 1, #(n.names or {}) do take(n.names[i]) end
    elseif t == "Label" or t == "Goto" then
      take(n.name)
    end
  end)
  return taken
end

local function makeNameFactory(seed, prefix, taken)
  local state = math.floor(math.abs(seed)) % 4294967296
  local function step()
    state = (state * 1664525 + 1013904223) % 4294967296
    return math.floor(state)
  end
  return function()
    while true do
      local name = prefix .. hex8(step()) .. hex8(step())
      if not taken[name] then
        taken[name] = true
        return name
      end
    end
  end
end

local function makeRng(seed)
  local state = (math.floor(math.abs(seed)) + 0x2545F491) % 4294967296
  return function(n)
    state = (state * 1103515245 + 12345) % 4294967296
    return (state % n) + 1
  end
end

-- Conservative local count for one function, ignoring nested functions.
local function countLocals(owner)
  local count = 0
  if owner.type == "Function" then count = #(owner.params or {}) end
  local function walk(n)
    local t = n.type
    if t == "Function" then return end
    if t == "Local" then
      count = count + #(n.names or {})
    elseif t == "LocalFunction" then
      count = count + 1
    elseif t == "NumericFor" then
      count = count + 1
    elseif t == "GenericFor" then
      count = count + #(n.names or {})
    end
    for i = 1, #n.children do walk(n.children[i]) end
  end
  for i = 1, #owner.children do walk(owner.children[i]) end
  return count
end

-- ------------------------------------------------------------------ transform

-- Declared first: eachCondition's walk reaches nested functions through it, so
-- the pair is mutually recursive.
local processOwner

-- Predicates guarding a condition that runs on every loop iteration are
-- computed once per owner instead of once per iteration: the identity is
-- hoisted into `local P = <template>` and the hot wrapper tests that boolean.
-- The per-iteration cost drops from the full MBA expression (multiply,
-- modulo, compare) to a single local read, which matters a lot in the
-- obfuscated VM where every iteration is interpreted.
local MAX_HOT_PREDS = 2

local function eachCondition(owner, ctx, state)
  local cfg = ctx.cfg
  local stats = ctx.stats

  local function pickPred()
    local list = state.preds
    if not list then
      list = {}
      state.preds = list
    end
    if #list < MAX_HOT_PREDS and (#list == 0 or ctx.rng(2) == 1) then
      local tplT = TRUE_TEMPLATES[ctx.rng(#TRUE_TEMPLATES)]
      local tplF = FALSE_TEMPLATES[ctx.rng(#FALSE_TEMPLATES)]
      local pred = {
        name = ctx.newName(),
        tplTrue = tplT,
        tplFalse = tplF,
        expr = tplT.build(state.name, 0, 0),
      }
      list[#list + 1] = pred
      return pred
    end
    return list[ctx.rng(#list)]
  end

  local function transform(cond, kind, hot)
    if cond == nil then return cond end
    if not state.active then return cond end
    if cfg.prob < 1 and ctx.rng(1000) > cfg.prob * 1000 then
      stats.skipped.prob = stats.skipped.prob + 1
      return cond
    end
    if not state.name then
      state.name = ctx.newName()
      state.value = ctx.rng(1999) - 1000
      if state.value == 0 then state.value = 1 end
    end

    local tplTrue = TRUE_TEMPLATES[ctx.rng(#TRUE_TEMPLATES)]
    local tplFalse = FALSE_TEMPLATES[ctx.rng(#FALSE_TEMPLATES)]
    local wrapper = WRAPPERS[ctx.rng(#WRAPPERS)]
    local line, col = cond.line or 0, cond.col or 0
    local t, f
    if hot then
      local pred = pickPred()
      tplTrue, tplFalse = pred.tplTrue, pred.tplFalse
      t = nam(pred.name, line, col)
      f = un("not", nam(pred.name, line, col), line, col)
    else
      t = tplTrue.build(state.name, line, col)
      f = tplFalse.build(state.name, line, col)
    end
    local wrapped = wrapper.build(cond, t, f, line, col)

    state.count = state.count + 1
    stats.conditions = stats.conditions + 1
    stats.predicates = stats.predicates + 2
    stats.templates[tplTrue.id] = (stats.templates[tplTrue.id] or 0) + 1
    stats.templates[tplFalse.id] = (stats.templates[tplFalse.id] or 0) + 1
    stats.wrappers[wrapper.id] = (stats.wrappers[wrapper.id] or 0) + 1
    stats.list[#stats.list + 1] = {
      line = line,
      kind = kind,
      wrapper = wrapper.id,
      template = tplTrue.id,
      falseTemplate = tplFalse.id,
    }
    return wrapped
  end

  local walk
  walk = function(n, st)
    local t = n.type
    if t == "Function" then
      -- Nested functions get their own predicate variable and budget.
      processOwner(n, ctx)
      return
    end
    if st.active then
      if t == "If" then
        if ctx.cfg.loopConditions or st.depth == 0 then
          local branches = n.branches or {}
          for i = 1, #branches do
            local idx = branches[i].cond
            if idx then n.children[idx] = transform(n.children[idx], "if", st.depth > 0) end
          end
        end
      elseif t == "While" then
        if ctx.cfg.loopConditions and n.children[1] then
          n.children[1] = transform(n.children[1], "while", true)
        end
      elseif t == "Repeat" then
        local last = #n.children
        if ctx.cfg.loopConditions and last >= 1 then
          n.children[last] = transform(n.children[last], "repeat", true)
        end
      elseif t == "IfExpression" then
        if ctx.cfg.loopConditions or st.depth == 0 then
          local branches = n.branches or {}
          for i = 1, #branches do
            local idx = branches[i].cond
            if idx then
              n.children[idx] = transform(n.children[idx], "if-expression", st.depth > 0)
            end
          end
        end
      end
    end
    if t == "While" or t == "Repeat" or t == "NumericFor" or t == "GenericFor" then
      for i = 1, #n.children do
        walk(n.children[i], { active = st.active, depth = st.depth + 1 })
      end
      return
    end
    for i = 1, #n.children do walk(n.children[i], st) end
  end

  for i = 1, #owner.children do walk(owner.children[i], { active = state.active, depth = 0 }) end
  return state
end

processOwner = function(owner, ctx)
  local declared = countLocals(owner)
  local active = declared < ctx.cfg.maxLocals
  local state = {
    owner = owner,
    active = active,
    count = 0,
    name = nil,
    value = nil,
  }
  if not active then
    ctx.stats.skipped.locals = ctx.stats.skipped.locals + 1
  end
  eachCondition(owner, ctx, state)

  if state.count > 0 and state.name then
    local first = owner.children[1]
    local line = (first and first.line) or owner.line or 0
    local col = (first and first.col) or owner.col or 0
    local decl = node("Local", line, col, { num(state.value, line, col) })
    decl.names = { state.name }
    table.insert(owner.children, 1, decl)
    if state.preds then
      for i = 1, #state.preds do
        local pred = state.preds[i]
        local pdecl = node("Local", line, col, { pred.expr })
        pdecl.names = { pred.name }
        table.insert(owner.children, 1 + i, pdecl)
        ctx.stats.hotPreds = (ctx.stats.hotPreds or 0) + 1
      end
    end
    ctx.stats.owners = ctx.stats.owners + 1
    ctx.stats.variables = ctx.stats.variables + 1
    ctx.stats.decls[#ctx.stats.decls + 1] = {
      name = state.name,
      value = state.value,
      conditions = state.count,
      line = line,
    }
  end
end

function Opaque.run(ast, opts)
  local cfg = {}
  for k, v in pairs(DEFAULTS) do cfg[k] = v end
  for k, v in pairs(opts or {}) do cfg[k] = v end

  local stats = {
    conditions = 0,
    predicates = 0,
    owners = 0,
    variables = 0,
    skipped = { disabled = 0, locals = 0, prob = 0 },
    templates = {},
    wrappers = {},
    decls = {},
    list = {},
  }

  if not cfg.enabled or not Ast.isNode(ast) then
    stats.skipped.disabled = 1
    return stats
  end

  local prefix = cfg.prefix
  if type(prefix) ~= "string" or not prefix:match("^[%a_][%w_]*$") then prefix = "_0x" end

  local ctx = {
    cfg = cfg,
    stats = stats,
    rng = makeRng(cfg.seed),
    newName = makeNameFactory(cfg.seed, prefix, collectTaken(ast)),
  }

  processOwner(ast, ctx)
  return stats
end

return Opaque
