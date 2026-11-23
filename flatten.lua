-- flatten.lua -- control-flow flattening (layer 3).
--
-- Pipeline position:
--   scope.analyze -> scope.apply -> flatten.run -> opaque -> ...
--
-- run() rewrites every eligible block (main chunk body, function bodies and
-- loop bodies) into a state machine:
--
--   local <hoisted locals>
--   local s = 21
--   while true do
--     if s < 13 then
--       if s == 7 then
--         <statements>
--         s = 21
--       else
--         s = 0
--       end
--     else
--       ...
--     end
--     if s <= 0 then break end
--   end
--   if s == -1 then break end      -- only when the body contained `break`
--
-- Design notes:
--   * dispatch is a balanced binary search tree over the state ids: O(log n)
--     comparisons per step, never a linear elseif chain;
--   * state ids are a per-build Fisher-Yates permutation, so the emitted shape
--     changes with the seed;
--   * locals declared in a flattened region are hoisted to the top of that
--     region's machine. scope.apply has already given every binding a unique
--     name, so hoisting can neither merge nor shadow bindings. Inside a loop
--     body the machine (and therefore its prelude) is re-entered on every
--     iteration, so per-iteration locals and closures keep their identity;
--   * `break` / `continue` become sentinel transitions (-1 / -2) and are
--     re-issued after the machine, so they still act on the enclosing loop;
--   * `repeat` bodies are safe to flatten: the hoisted locals sit directly in
--     the repeat block, so the `until` condition still sees them;
--   * regions containing goto/labels, to-be-closed/const attributes, `_ENV`
--     or `_G` locals, duplicate local names (i.e. an AST that has not been
--     through scope.apply) are left untouched.
local Ast = require("src.ast")

local Flatten = {}

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

-- Sentinel transitions. State ids are positive, so `s <= 0` is the single
-- "leave the machine" test in the dispatcher.
local EXIT = 0
local BREAK = -1
local CONTINUE = -2
Flatten.EXIT = EXIT
Flatten.BREAK = BREAK
Flatten.CONTINUE = CONTINUE

local DEFAULTS = {
  seed = 0x5F1A77E,
  prefix = "_0x",
  minStatements = 3,
  minIfs = 1,
  maxHoisted = 160,
  maxLocals = 185,
  enabled = true,
  -- Hardening switches stay off by default so direct Flatten.run callers keep
  -- the historic shape; the obfuscator presets turn them on.
  shapes = false,
  split = false,
  decoys = false,
  stateOffset = false,
  maxStates = 320,
  -- Loop bodies are the hot path once the script runs inside the VM: a state
  -- machine there costs several interpreted branches per source iteration.
  -- Direct callers keep the historic behaviour; the presets flatten the
  -- function and chunk bodies only.
  flattenLoops = true,
}

-- ---------------------------------------------------------------- utilities

local function node(typ, line, col, children)
  return { type = typ, line = line or 0, col = col or 0, children = children or {} }
end

local function nameNode(value, line, col)
  local n = node("Name", line, col)
  n.value = value
  return n
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

local function numberNode(value, line, col)
  local n = node("Number", line, col)
  n.value = intValue(value)
  n.raw = numberRaw(n.value)
  return n
end

local function boolNode(value, line, col)
  local n = node("Boolean", line, col)
  n.value = value
  return n
end

local function binary(op, a, b, line, col)
  local n = node("BinaryOp", line, col, { a, b })
  n.op = op
  return n
end

local function makeIf(cond, thenList, elseList, line, col)
  local children = { cond }
  for i = 1, #thenList do children[#children + 1] = thenList[i] end
  for i = 1, #elseList do children[#children + 1] = elseList[i] end
  local n = node("If", line, col, children)
  n.branches = { { cond = 1, count = #thenList } }
  n.elseCount = #elseList
  return n
end

local function makeLocal(names, line, col)
  local n = node("Local", line, col)
  local copy = {}
  for i = 1, #names do copy[i] = names[i] end
  n.names = copy
  return n
end

local function makeLocalInit(name, value, line, col)
  local n = node("Local", line, col, { numberNode(value, line, col) })
  n.names = { name }
  return n
end

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

-- 16 hex digits, so machine names can never collide with layer 2's 8-digit
-- names; the taken set still guards against a literal source identifier.
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
  local state = (math.floor(math.abs(seed)) + 0x9E3779B9) % 4294967296
  return function(n)
    state = (state * 1103515245 + 12345) % 4294967296
    return (state % n) + 1
  end
end

-- ------------------------------------------------------------- region scan

local function addHoist(info, name)
  if name == "_ENV" or name == "_G" then info.reserved = true end
  if info.seen[name] then info.duplicate = true end
  info.seen[name] = true
  info.hoistCount = info.hoistCount + 1
end

local function scanList(list, info)
  for i = 1, #list do
    local st = list[i]
    local t = st.type
    info.statements = info.statements + 1
    if t == "Local" then
      info.hasLocals = true
      if not st.bindingIds then info.unscoped = true end
      local names = st.names or {}
      for k = 1, #names do addHoist(info, names[k]) end
      if st.attrs then
        for k = 1, #names do
          if st.attrs[k] then info.attrs = true end
        end
      end
    elseif t == "LocalFunction" then
      info.hasLocals = true
      if not st.bindingId then info.unscoped = true end
      addHoist(info, st.name)
    elseif t == "Do" then
      scanList(st.children, info)
    elseif t == "If" then
      info.ifs = info.ifs + 1
      local branches = st.branches or {}
      local cursor = 1
      for bi = 1, #branches do
        local br = branches[bi]
        local body = {}
        for k = 1, br.count do body[k] = st.children[br.cond + k] end
        scanList(body, info)
        cursor = br.cond + br.count + 1
      end
      local elseBody = {}
      for k = 1, (st.elseCount or 0) do elseBody[k] = st.children[cursor + k - 1] end
      scanList(elseBody, info)
    elseif t == "Goto" or t == "Label" then
      info.hasGoto = true
    elseif t == "Break" then
      info.breaks = true
    elseif t == "Continue" then
      info.continues = true
    end
  end
end

local function scan(list)
  local info = {
    statements = 0, ifs = 0, hoistCount = 0, hasLocals = false,
    unscoped = false, attrs = false, hasGoto = false, breaks = false,
    continues = false, reserved = false, duplicate = false, seen = {},
  }
  scanList(list, info)
  return info
end

-- -------------------------------------------------------------- hoisting
-- Converts every Local/LocalFunction in the region into a plain assignment
-- (their names are declared once at the top of the machine) and inlines `do`
-- blocks so the state builder only sees flat statement lists.

local function localToAssign(st)
  local a = node("Assign", st.line, st.col)
  a.targetCount = #st.names
  local children = {}
  for i = 1, #st.names do
    children[#children + 1] = nameNode(st.names[i], st.line, st.col)
  end
  for i = 1, #st.children do children[#children + 1] = st.children[i] end
  a.children = children
  return a
end

local function localFunctionToAssign(st)
  local a = node("Assign", st.line, st.col)
  a.targetCount = 1
  a.children = { nameNode(st.name, st.line, st.col), st.children[1] }
  return a
end

local prepare

local function prepareIf(st, names)
  local branches = st.branches or {}
  local children, newBranches = {}, {}
  local cursor = 1
  for bi = 1, #branches do
    local br = branches[bi]
    children[#children + 1] = st.children[br.cond]
    local body = {}
    for k = 1, br.count do body[k] = st.children[br.cond + k] end
    local tbody = prepare(body, names)
    newBranches[bi] = { cond = #children, count = #tbody }
    for k = 1, #tbody do children[#children + 1] = tbody[k] end
    cursor = br.cond + br.count + 1
  end
  local elseBody = {}
  for k = 1, (st.elseCount or 0) do elseBody[k] = st.children[cursor + k - 1] end
  local telse = prepare(elseBody, names)
  for k = 1, #telse do children[#children + 1] = telse[k] end
  local n = node("If", st.line, st.col, children)
  n.branches = newBranches
  n.elseCount = #telse
  return n
end

prepare = function(list, names)
  local out = {}
  for i = 1, #list do
    local st = list[i]
    local t = st.type
    if t == "Do" then
      local inner = prepare(st.children, names)
      for k = 1, #inner do out[#out + 1] = inner[k] end
    elseif t == "Local" then
      for k = 1, #(st.names or {}) do names[#names + 1] = st.names[k] end
      -- A declaration without initializers only needs the hoisted `local`.
      if #st.children > 0 then out[#out + 1] = localToAssign(st) end
    elseif t == "LocalFunction" then
      names[#names + 1] = st.name
      out[#out + 1] = localFunctionToAssign(st)
    elseif t == "If" then
      out[#out + 1] = prepareIf(st, names)
    else
      out[#out + 1] = st
    end
  end
  return out
end

-- ------------------------------------------------------------ state builder

local function buildStates(list, sName, inLoop)
  local states = {}
  local usesBreak, usesContinue = false, false

  local function newState(body, line, col)
    local st = {
      index = #states + 1,
      body = body or {},
      line = line or 0,
      col = col or 0,
    }
    states[#states + 1] = st
    return st
  end

  local buildSeq, buildIf

  buildIf = function(ifNode, after)
    local branches = ifNode.branches or {}
    local entries = {}
    local cursor = 1
    for bi = 1, #branches do
      local br = branches[bi]
      local body = {}
      for k = 1, br.count do body[k] = ifNode.children[br.cond + k] end
      entries[bi] = {
        cond = ifNode.children[br.cond],
        entry = buildSeq(body, 1, #body, after),
      }
      cursor = br.cond + br.count + 1
    end
    local elseBody = {}
    for k = 1, (ifNode.elseCount or 0) do
      elseBody[k] = ifNode.children[cursor + k - 1]
    end
    local nextEntry = buildSeq(elseBody, 1, #elseBody, after)
    for bi = #entries, 1, -1 do
      local test = newState({}, ifNode.line, ifNode.col)
      test.test = {
        cond = entries[bi].cond,
        thenRef = entries[bi].entry,
        elseRef = nextEntry,
      }
      nextEntry = test
    end
    return nextEntry
  end

  buildSeq = function(seq, from, to, cont)
    local body = {}
    local i = from
    while i <= to do
      local st = seq[i]
      local t = st.type
      if t == "If" then
        local after = buildSeq(seq, i + 1, to, cont)
        local entry = buildIf(st, after)
        if #body == 0 then return entry end
        local state = newState(body, body[1].line, body[1].col)
        state.next = entry
        return state
      elseif t == "Return" then
        body[#body + 1] = st
        local state = newState(body, st.line, st.col)
        return state
      elseif t == "Break" then
        if not inLoop then return nil end
        usesBreak = true
        local state = newState(body, st.line, st.col)
        state.next = BREAK
        return state
      elseif t == "Continue" then
        if not inLoop then return nil end
        usesContinue = true
        local state = newState(body, st.line, st.col)
        state.next = CONTINUE
        return state
      else
        body[#body + 1] = st
        i = i + 1
      end
    end
    if #body == 0 then return cont end
    local state = newState(body, body[1].line, body[1].col)
    state.next = cont
    return state
  end

  local entry = buildSeq(list, 1, #list, EXIT)
  return entry, states, usesBreak, usesContinue
end

-- ------------------------------------------------------------- flatten pass

local function flattenRegion(list, inLoop, ctx, budget)
  local cfg = ctx.cfg
  local info = scan(list)

  local reason
  if info.hasGoto then reason = "goto"
  elseif info.attrs then reason = "attrs"
  elseif info.unscoped then reason = "unscoped"
  elseif (info.breaks or info.continues) and not inLoop then reason = "break"
  elseif info.reserved then reason = "reserved"
  elseif info.duplicate then reason = "shadow"
  elseif info.ifs < cfg.minIfs then reason = "noif"
  elseif info.statements < cfg.minStatements then reason = "small"
  elseif info.hoistCount > cfg.maxHoisted then reason = "locals"
  end
  if reason then return nil, false, reason, 0 end

  local names = {}
  local prepared = prepare(list, names)
  if #names > cfg.maxHoisted or #names + 1 > budget then
    return nil, false, "locals", 0
  end

  local line = (list[1] and list[1].line) or 0
  local col = (list[1] and list[1].col) or 0
  local sName = ctx.newName()
  local entry, states, usesBreak, usesContinue = buildStates(prepared, sName, inLoop)
  if type(entry) ~= "table" or #states == 0 then
    return nil, false, "empty", 0
  end

  -- Random state splitting: a long straight-line body becomes two states joined
  -- by a transition, so the recovered CFG has more nodes than the source ever
  -- had and no state maps cleanly onto a source line.
  if cfg.split and #states < cfg.maxStates then
    local idx = 1
    while idx <= #states and #states < cfg.maxStates do
      local st = states[idx]
      local bl = #st.body
      if st.next ~= nil and bl >= 4 and ctx.rng(3) <= 2 then
        local cut = 1 + ctx.rng(bl - 2)
        local rest = {}
        for k = cut + 1, bl do rest[#rest + 1] = st.body[k] end
        for k = cut + 1, bl do st.body[k] = nil end
        local tail = {
          index = #states + 1, body = rest, line = st.line, col = st.col,
          next = st.next,
        }
        states[#states + 1] = tail
        st.next = tail
      end
      idx = idx + 1
    end
  end

  -- Unreachable inert states: they are routed like every other state but no
  -- transition ever targets them, so they only cost a benchmark comparison for
  -- a CFG reconstructor that has to prove them dead.
  if cfg.decoys and #states >= 4 then
    local extra = ctx.rng(2)
    for _ = 1, extra do
      states[#states + 1] = {
        index = #states + 1, body = {}, line = line, col = col, next = EXIT,
      }
    end
  end

  local n = #states
  local ids = {}
  for i = 1, n do ids[i] = i end
  for i = n, 2, -1 do
    local j = ctx.rng(i)
    ids[i], ids[j] = ids[j], ids[i]
  end
  for i = 1, n do states[i].id = ids[i] end

  -- Per-machine state-id bias: comparisons and transitions carry `id + off`,
  -- so the ids a dumper extracts are not the small 1..n range the builder used.
  local off = 0
  if cfg.stateOffset then off = 1000 + ctx.rng(900000) end

  local sorted = {}
  for i = 1, n do sorted[i] = states[i] end
  table.sort(sorted, function(a, b) return a.id < b.id end)

  local function refValue(ref)
    if type(ref) == "table" then return ref.id end
    return ref
  end

  local function transition(ref, l, c)
    local v = refValue(ref)
    if v > 0 then v = v + off end
    local a = node("Assign", l or line, c or col, {
      nameNode(sName, l or line, c or col),
      numberNode(v, l or line, c or col),
    })
    a.targetCount = 1
    return a
  end

  local function leafStatements(st)
    local stmts = {}
    for k = 1, #st.body do stmts[k] = st.body[k] end
    if st.test then
      stmts[#stmts + 1] = makeIf(
        st.test.cond,
        { transition(st.test.thenRef, st.line, st.col) },
        { transition(st.test.elseRef, st.line, st.col) },
        st.line, st.col)
    elseif st.next ~= nil then
      stmts[#stmts + 1] = transition(st.next, st.line, st.col)
    end
    return stmts
  end

  local maxDepth = 0
  local buildRouter
  buildRouter = function(from, to, depth)
    if depth > maxDepth then maxDepth = depth end
    if from == to then
      local st = sorted[from]
      local idv = numberNode(st.id + off, st.line, st.col)
      local sref = nameNode(sName, st.line, st.col)
      local cond
      if ctx.rng(3) == 1 then
        cond = binary("==", idv, sref, st.line, st.col)
      else
        cond = binary("==", sref, idv, st.line, st.col)
      end
      return makeIf(cond, leafStatements(st),
        { transition(EXIT, st.line, st.col) }, st.line, st.col)
    end
    -- Every internal node stays at the balanced midpoint, so the router is
    -- still O(log n) and the emitted depth is bounded. The comparison itself is
    -- drawn from three equivalent spellings (all integer-exact) and the two
    -- subtrees swap sides for one of them, so a reconstructed tree no longer
    -- has one uniform `<`-on-the-left shape.
    local mid = math.floor((from + to) / 2)
    local pivot = sorted[mid + 1].id + off
    local sref = nameNode(sName)
    local left = { buildRouter(from, mid, depth + 1) }
    local right = { buildRouter(mid + 1, to, depth + 1) }
    local variant = ctx.rng(3)
    local cond
    if variant == 1 then
      cond = binary("<", sref, numberNode(pivot))
    elseif variant == 2 then
      cond = binary("<=", sref, numberNode(pivot - 1))
    else
      -- `pivot <= s` is the negated split, so the branches swap with it.
      cond = binary("<=", numberNode(pivot), sref)
      left, right = right, left
    end
    return makeIf(cond, left, right, sorted[from].line, sorted[from].col)
  end

  local function exitTest(mode, l, c)
    if mode == 2 then
      return binary("<", nameNode(sName, l, c), numberNode(1, l, c), l, c)
    elseif mode == 3 then
      return binary(">=", numberNode(0, l, c), nameNode(sName, l, c), l, c)
    end
    return binary("<=", nameNode(sName, l, c), numberNode(0, l, c), l, c)
  end

  local router = buildRouter(1, n, 1)
  -- Five equivalent dispatch shells, picked per machine: a `while true` with a
  -- trailing exit test, a test-first `while true`, a positive-condition
  -- `while`, a `repeat..until`, or a test-first `repeat..until false`. They
  -- compile to different code shapes while running the same machine, and the
  -- exit comparison itself is drawn from three equivalent spellings.
  local shape = 1
  if cfg.shapes then shape = ctx.rng(5) end
  local mode = 1
  if cfg.shapes then mode = ctx.rng(3) end
  local whileNode
  if shape == 1 then
    local breakCheck = makeIf(exitTest(mode, line, col),
      { node("Break") }, {})
    whileNode = node("While", line, col, { boolNode(true), router, breakCheck })
  elseif shape == 2 then
    whileNode = node("While", line, col, {
      binary(">", nameNode(sName), numberNode(0)), router,
    })
  elseif shape == 3 then
    whileNode = node("Repeat", line, col, {
      router, exitTest(mode, line, col),
    })
  elseif shape == 4 then
    local head = makeIf(exitTest(mode, line, col), { node("Break") }, {})
    whileNode = node("While", line, col, { boolNode(true), head, router })
  else
    local head = makeIf(exitTest(mode, line, col), { node("Break") }, {})
    whileNode = node("Repeat", line, col, { head, router, boolNode(false) })
  end

  local prelude = {}
  if #names > 0 then prelude[#prelude + 1] = makeLocal(names, line, col) end
  prelude[#prelude + 1] = makeLocalInit(sName, entry.id + off, line, col)
  prelude[#prelude + 1] = whileNode
  if usesBreak then
    prelude[#prelude + 1] = makeIf(
      binary("==", nameNode(sName), numberNode(BREAK)), { node("Break") }, {})
  end
  if usesContinue then
    prelude[#prelude + 1] = makeIf(
      binary("==", nameNode(sName), numberNode(CONTINUE)), { node("Continue") }, {})
  end

  ctx.stats.states = ctx.stats.states + n
  ctx.stats.hoisted = ctx.stats.hoisted + #names
  local machine = {
    name = sName,
    states = n,
    hoisted = #names,
    depth = maxDepth,
    loop = inLoop and true or false,
    line = line,
  }
  ctx.stats.machines[#ctx.stats.machines + 1] = machine

  return prelude, true, nil, #names + 1
end

-- ---------------------------------------------------------------- traversal

local processOwner, processNode

local function bodyBounds(owner)
  local t = owner.type
  if t == "While" then return 2, #owner.children end
  if t == "Repeat" then return 1, #owner.children - 1 end
  if t == "NumericFor" then return (owner.hasStep and 4 or 3), #owner.children end
  if t == "GenericFor" then return (owner.exprCount or 0) + 1, #owner.children end
  return 1, #owner.children
end

processOwner = function(owner, ctx, budget, inLoop)
  local from, to = bodyBounds(owner)

  for i = 1, from - 1 do
    budget = processNode(owner.children[i], ctx, budget)
  end
  for i = to + 1, #owner.children do
    budget = processNode(owner.children[i], ctx, budget)
  end
  for i = from, to do
    budget = processNode(owner.children[i], ctx, budget)
  end

  local body = {}
  for i = from, to do body[#body + 1] = owner.children[i] end

  ctx.stats.regions = ctx.stats.regions + 1
  local replacement, changed, reason, used = flattenRegion(body, inLoop, ctx, budget)
  if not changed then
    ctx.stats.skipped[reason] = (ctx.stats.skipped[reason] or 0) + 1
    return budget
  end

  local kids = {}
  for i = 1, from - 1 do kids[#kids + 1] = owner.children[i] end
  for i = 1, #replacement do kids[#kids + 1] = replacement[i] end
  for i = to + 1, #owner.children do kids[#kids + 1] = owner.children[i] end
  owner.children = kids

  ctx.stats.flattened = ctx.stats.flattened + 1
  return budget - used
end

processNode = function(n, ctx, budget)
  local t = n.type
  if t == "Function" then
    local params = #(n.params or {})
    processOwner(n, ctx, ctx.cfg.maxLocals - params, false)
    return budget
  end
  if t == "While" or t == "Repeat" or t == "NumericFor" or t == "GenericFor" then
    if not ctx.cfg.flattenLoops then
      -- Still descend so functions declared inside a loop are flattened.
      for i = 1, #n.children do
        budget = processNode(n.children[i], ctx, budget)
      end
      return budget
    end
    return processOwner(n, ctx, budget, true)
  end
  for i = 1, #n.children do
    budget = processNode(n.children[i], ctx, budget)
  end
  return budget
end

function Flatten.run(ast, opts)
  local cfg = {}
  for k, v in pairs(DEFAULTS) do cfg[k] = v end
  for k, v in pairs(opts or {}) do cfg[k] = v end

  local stats = {
    regions = 0,
    flattened = 0,
    states = 0,
    hoisted = 0,
    skipped = {},
    machines = {},
  }

  if not cfg.enabled or not Ast.isNode(ast) then return stats end

  local prefix = cfg.prefix
  if type(prefix) ~= "string" or not prefix:match("^[%a_][%w_]*$") then prefix = "_0x" end

  local ctx = {
    cfg = cfg,
    stats = stats,
    rng = makeRng(cfg.seed),
    newName = makeNameFactory(cfg.seed, prefix, collectTaken(ast)),
  }

  processOwner(ast, ctx, cfg.maxLocals, false)
  return stats
end

return Flatten
