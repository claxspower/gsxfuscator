-- transforms.lua -- AST-level passes that run before bytecode generation.
local U = require("src.util")
local T = {}

-------------------------------------------------------------------------------
-- Dead code injection
-------------------------------------------------------------------------------
-- Inserts blocks that can never run. They reference only generated locals and
-- harmless library calls, so they inflate the bytecode without changing output.
local function num(v) return { t = "Number", v = v, line = 0, col = 0 } end
local function str(v) return { t = "String", v = v, line = 0, col = 0 } end
local function name(v) return { t = "Name", v = v, line = 0, col = 0 } end
local function bin(op, l, r)
  return { t = "Bin", op = op, l = l, r = r, line = 0, col = 0 }
end
local function stmt(t) return { t = t, line = 0, col = 0 } end

local deadSeq = 0
local function deadName(prefix)
  deadSeq = deadSeq + 1
  return "_0x$" .. prefix .. deadSeq
end

-- One plausible-looking but unreachable block. The whole thing is guarded by
-- a never-true condition, so nothing inside can affect program behavior.
local function makeJunk()
  local a = deadName("d")
  local b = deadName("d")
  local f = deadName("f")
  local block = {}

  local declA = stmt("Local")
  declA.names = { a }
  declA.exprs = { bin("+", num(U.randomInt(1, 9999)), num(U.randomInt(0, 999))) }
  block[#block + 1] = declA

  local declB = stmt("Local")
  declB.names = { b }
  declB.exprs = { str(U.ident("s")) }
  block[#block + 1] = declB

  local fakeFn = stmt("LocalFunction")
  fakeFn.name = f
  fakeFn.func = {
    t = "Func", params = { deadName("p") }, vararg = false, line = 0, col = 0,
    body = {
      {
        t = "Return", line = 0, col = 0,
        exprs = { bin("*", name(a), num(U.randomInt(2, 9))) },
      },
    },
  }
  block[#block + 1] = fakeFn

  -- Never true, but not a literal false: keeps the branch in the bytecode.
  local never = bin("<", { t = "Un", op = "#", e = str("x"), line = 0, col = 0 }, num(-1))
  local ifst = stmt("If")
  ifst.branches = { {
    cond = never,
    block = {
      {
        t = "Assign", line = 0, col = 0, targets = { name(a) },
        exprs = { bin("+", name(a), { t = "Un", op = "#", e = name(b), line = 0, col = 0 }) },
      },
      {
        t = "CallStat", line = 0, col = 0,
        call = {
          t = "Call", line = 0, col = 0,
          fn = {
            t = "Index", line = 0, col = 0,
            obj = name("string"), key = str("reverse"),
          },
          args = { name(b) },
        },
      },
    },
  } }
  block[#block + 1] = ifst

  local loop = stmt("While")
  loop.cond = bin("<", name(a), num(0))
  loop.block = {
    {
      t = "Assign", line = 0, col = 0, targets = { name(a) },
      exprs = { bin("+", name(a), num(1)) },
    },
  }
  block[#block + 1] = loop

  local guard = stmt("If")
  guard.branches = { { cond = never, block = block } }
  guard.dead = true
  return guard
end

local function injectBlock(block, density)
  local out = {}
  for i = 1, #block do
    local st = block[i]
    if st then
      if U.chance(math.min(70, math.floor(14 * density))) then
        out[#out + 1] = makeJunk()
      end
      out[#out + 1] = st
    end
  end
  if U.chance(math.min(90, math.floor(35 * density))) and #out > 0 then
    out[#out + 1] = makeJunk()
  end
  return out
end

local function walkStmt(st, density)
  if not st or st.dead then return end
  if st.t == "Do" or st.t == "While" or st.t == "Repeat" or st.t == "NumFor" or st.t == "GenFor" then
    st.block = injectBlock(st.block, density)
    for i = 1, #st.block do walkStmt(st.block[i], density) end
  elseif st.t == "If" then
    for i = 1, #st.branches do
      local br = st.branches[i]
      br.block = injectBlock(br.block, density)
      for j = 1, #br.block do walkStmt(br.block[j], density) end
    end
    if st.orelse then
      st.orelse = injectBlock(st.orelse, density)
      for i = 1, #st.orelse do walkStmt(st.orelse[i], density) end
    end
  elseif st.t == "LocalFunction" or st.t == "FunctionStat" then
    local fn = st.func
    fn.body = injectBlock(fn.body, density)
    for i = 1, #fn.body do walkStmt(fn.body[i], density) end
  elseif st.t == "Local" or st.t == "Assign" then
    local exprs = st.exprs or {}
    for i = 1, #exprs do
      local e = exprs[i]
      if e and e.t == "Func" then
        e.body = injectBlock(e.body, density)
        for j = 1, #e.body do walkStmt(e.body[j], density) end
      end
    end
  end
end

-- opts.density scales the amount of injected junk (1 = default).
function T.deadcode(ast, opts)
  local density = tonumber(opts and opts.density) or 1
  if density <= 0 then return ast end
  ast.block = injectBlock(ast.block, density)
  for i = 1, #ast.block do walkStmt(ast.block[i], density) end
  return ast
end

-------------------------------------------------------------------------------
-- Portable constant obfuscation (MBA-style arithmetic identities)
-------------------------------------------------------------------------------
-- Returns source text that evaluates to n. Only +, -, * and integer literals
-- are used so the result keeps the integer subtype where the host has one.
function T.hideNumber(n, depth)
  depth = depth or 0
  if n ~= math.floor(n) or math.abs(n) > 4503599627370496 or depth > 2 then
    return U.formatNumber(n)
  end
  local mode = U.randomInt(1, 4)
  if mode == 1 then
    local b = U.randomInt(1, 100000)
    return "(" .. U.formatNumber(n + b) .. "-" .. U.formatNumber(b) .. ")"
  elseif mode == 2 then
    local b = U.randomInt(2, 9)
    local a = math.floor(n / b)
    local c = n - a * b
    return "(" .. U.formatNumber(a) .. "*" .. U.formatNumber(b) .. "+" .. U.formatNumber(c) .. ")"
  elseif mode == 3 then
    local x = U.randomInt(1, 65535)
    return "((" .. U.formatNumber(n - x) .. ")+" .. U.formatNumber(x) .. ")"
  else
    local x = U.randomInt(1, 4096)
    return "(" .. U.formatNumber(x) .. "+(" .. U.formatNumber(n - x) .. "))"
  end
end

return T
