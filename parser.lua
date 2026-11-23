-- parser.lua -- recursive-descent + Pratt parser for Lua 5.1/5.3/5.4 and Luau.
-- Produces a plain-table AST. Syntax errors are collected, never thrown at the caller.
local Lexer = require("src.lexer")

local Parser = {}

local BINPRI = {
  ["or"] = { 1, 1 }, ["and"] = { 2, 2 },
  ["<"] = { 3, 3 }, [">"] = { 3, 3 }, ["<="] = { 3, 3 }, [">="] = { 3, 3 },
  ["~="] = { 3, 3 }, ["=="] = { 3, 3 },
  ["|"] = { 4, 4 }, ["~"] = { 5, 5 }, ["&"] = { 6, 6 },
  ["<<"] = { 7, 7 }, [">>"] = { 7, 7 },
  [".."] = { 8, 7 },
  ["+"] = { 9, 9 }, ["-"] = { 9, 9 },
  ["*"] = { 10, 10 }, ["/"] = { 10, 10 }, ["//"] = { 10, 10 }, ["%"] = { 10, 10 },
  ["^"] = { 12, 11 },
}
Parser.BINPRI = BINPRI

local UNARY = { ["not"] = true, ["-"] = true, ["#"] = true, ["~"] = true }

local BLOCK_END = { ["end"] = true, ["else"] = true, ["elseif"] = true, ["until"] = true, ["eof"] = true }
local STMT_START = {
  ["local"] = true, ["if"] = true, ["while"] = true, ["for"] = true, ["repeat"] = true,
  ["do"] = true, ["function"] = true, ["return"] = true, ["break"] = true, ["goto"] = true,
  ["::"] = true, [";"] = true,
}
local COMPOUND = {
  ["+="] = "+", ["-="] = "-", ["*="] = "*", ["/="] = "/", ["%="] = "%", ["^="] = "^",
  ["..="] = "..", ["//="] = "//",
}
local TYPE_STMT_KEYWORDS = { ["local"] = true, ["if"] = true, ["while"] = true, ["for"] = true,
  ["repeat"] = true, ["do"] = true, ["function"] = true, ["return"] = true, ["break"] = true,
  ["end"] = true, ["else"] = true, ["elseif"] = true, ["until"] = true, ["goto"] = true,
  ["::"] = true, ["export"] = true, ["continue"] = true, ["nil"] = true, ["true"] = true,
  ["false"] = true, ["not"] = true, ["local"] = true }

local function node(t, line, col)
  return { t = t, line = line or 0, col = col or 0 }
end

local function parseError(msg, tok)
  error({ __parse = true, msg = msg, line = tok and tok.line or 0, col = tok and tok.col or 0 }, 0)
end

-- Split a Luau interpolated-string body into literal and expression segments.
local function splitInterpolation(raw)
  local parts = {}
  local lit = {}
  local i = 1
  local n = #raw
  local function flush()
    if #lit > 0 then
      parts[#parts + 1] = { type = "lit", value = table.concat(lit) }
      lit = {}
    end
  end
  while i <= n do
    local c = raw:sub(i, i)
    if c == "\\" then
      local nxt = raw:sub(i + 1, i + 1)
      lit[#lit + 1] = nxt
      i = i + 2
    elseif c == "{" then
      flush()
      local depth = 1
      local j = i + 1
      local exprStart = j
      local quote = nil
      while j <= n and depth > 0 do
        local ch = raw:sub(j, j)
        if quote then
          if ch == "\\" then j = j + 1
          elseif ch == quote then quote = nil end
        elseif ch == "'" or ch == '"' or ch == "`" then
          quote = ch
        elseif ch == "{" then depth = depth + 1
        elseif ch == "}" then depth = depth - 1 end
        j = j + 1
      end
      if depth ~= 0 then return nil, "unfinished interpolation expression" end
      parts[#parts + 1] = { type = "expr", source = raw:sub(exprStart, j - 2) }
      i = j
    else
      lit[#lit + 1] = c
      i = i + 1
    end
  end
  flush()
  return parts
end
Parser.splitInterpolation = splitInterpolation

function Parser.parse(src, filename)
  local tokens, lexErrors = Lexer.lex(src, filename)
  local self = {
    tokens = tokens,
    pos = 1,
    errors = {},
    filename = filename or "<input>",
    depth = 0,
    generated = 0,
  }

  local function peek(off)
    local p = self.pos + (off or 0)
    if p > #self.tokens then p = #self.tokens end
    return self.tokens[p]
  end

  local function cur() return peek(0) end
  local function nextTok()
    local t = cur()
    if self.pos < #self.tokens then self.pos = self.pos + 1 end
    return t
  end
  local function check(t) return cur().t == t end
  local function accept(t)
    if check(t) then return nextTok() end
    return nil
  end
  local function expect(t, what)
    if check(t) then return nextTok() end
    parseError("'" .. t .. "' expected" .. (what and (" near " .. what) or ""), cur())
  end

  local function addError(msg, line, col)
    self.errors[#self.errors + 1] = { line = line or 0, col = col or 0, msg = msg, filename = self.filename }
  end

  local parseBlock, parseStatement, parseExpr, parseExprList

  local function U_copy(v)
    if type(v) ~= "table" then return v end
    local t = {}
    for k, val in pairs(v) do t[k] = U_copy(val) end
    return t
  end

  local function enter()
    self.depth = self.depth + 1
    if self.depth > 220 then
      parseError("chunk is nested too deeply", cur())
    end
  end
  local function leave() self.depth = self.depth - 1 end

  local function skipBalanced(open, close)
    expect(open)
    local depth = 1
    while depth > 0 and not check("eof") do
      local t = nextTok().t
      if t == open then depth = depth + 1
      elseif t == close then depth = depth - 1 end
    end
  end

  local function skipGenerics()
    if check("<") then
      local save = self.pos
      local depth = 0
      local ok = false
      while not check("eof") do
        local t = nextTok().t
        if t == "<" then depth = depth + 1
        elseif t == ">" then
          depth = depth - 1
          if depth == 0 then ok = true; break end
        elseif t == "end" or t == "do" or t == "then" then
          break
        end
      end
      if not ok then self.pos = save else self.pos = self.pos end
    end
  end

  -- Consume a Luau type annotation. Depth-aware and newline aware so that
  -- "local x: number" followed by a new statement does not swallow it.
  local function skipType(stops, context)
    local depth = 0
    local startLine = cur().line
    local consumedPrimary = false
    while not check("eof") do
      local tk = cur()
      local tt = tk.t
      if depth == 0 and stops[tt] then break end
      if depth == 0 and tt == ";" then break end
      if depth == 0 and tt == "->" then
        nextTok(); consumedPrimary = false
      elseif depth == 0 and tk.line > startLine and consumedPrimary and
             (TYPE_STMT_KEYWORDS[tt] or (tt == "name" and tk.line > startLine and context == "return")) then
        -- A new statement began on a new line and the type already has a body.
        break
      elseif depth == 0 and tk.line > startLine and tt == "name" and consumedPrimary and context == "local" then
        break
      else
        if tt == "(" or tt == "[" or tt == "{" then depth = depth + 1
        elseif tt == ")" or tt == "]" or tt == "}" then
          if depth == 0 then break end
          depth = depth - 1
        end
        nextTok()
        if tt == "name" or tt == "string" or tt == "}" or tt == ")" or tt == "]" or tt == "?" then
          consumedPrimary = true
        end
        if tt == "|" or tt == "&" or tt == "->" or tt == "," then consumedPrimary = false end
        if depth > 60 then parseError("type annotation is too complex", tk) end
      end
    end
  end

  local function parseTypeAlias()
    -- "type Name<T> = <type>" is parsed and discarded.
    nextTok()
    expect("name")
    if check("<") then skipBalanced("<", ">") end
    expect("=")
    skipType({}, "alias")
    while not check("eof") and not check(";") do
      local tk = cur()
      if tk.line > self.tokens[self.pos - 1].line and TYPE_STMT_KEYWORDS[tk.t] then break end
      if tk.line > self.tokens[self.pos - 1].line and tk.t == "name" then break end
      nextTok()
    end
    accept(";")
  end

  local function parseFunctionBody(isMethod, name)
    local fn = node("Func", cur().line, cur().col)
    fn.params = {}
    fn.vararg = false
    fn.body = {}
    fn.isMethod = isMethod or false
    fn.name = name
    if check("<") then skipGenerics() end
    expect("(")
    if isMethod then fn.params[#fn.params + 1] = "self" end
    if not check(")") then
      repeat
        if check("...") then
          nextTok(); fn.vararg = true
          if check(":") then nextTok(); skipType({ [","] = true, [")"] = true }, "param") end
          break
        end
        local nm = expect("name")
        fn.params[#fn.params + 1] = nm.v
        if check(":") then nextTok(); skipType({ [","] = true, [")"] = true }, "param") end
      until not accept(",")
    end
    expect(")")
    if check(":") then nextTok(); skipType({ ["local"] = true, ["if"] = true, ["while"] = true,
      ["for"] = true, ["repeat"] = true, ["do"] = true, ["function"] = true, ["return"] = true,
      ["end"] = true, [";"] = true, ["break"] = true, ["::"] = true }, "return") end
    fn.body = parseBlock({ ["end"] = true })
    expect("end")
    return fn
  end

  local function parseTable()
    local t = node("Table", cur().line, cur().col)
    t.fields = {}
    expect("{")
    while not check("}") do
      if check("[") then
        nextTok()
        local key = parseExpr()
        expect("]")
        expect("=")
        local value = parseExpr()
        t.fields[#t.fields + 1] = { kind = "key", key = key, value = value }
      elseif check("name") and peek(1).t == "=" then
        local nm = nextTok()
        nextTok()
        local value = parseExpr()
        t.fields[#t.fields + 1] = { kind = "name", key = node("String", nm.line, nm.col), value = value }
        t.fields[#t.fields].key.v = nm.v
      else
        local value = parseExpr()
        t.fields[#t.fields + 1] = { kind = "array", value = value }
      end
      if not (accept(",") or accept(";")) then break end
    end
    expect("}")
    return t
  end

  local function parseInterpolated(tok)
    local parts, err = splitInterpolation(tok.v)
    if not parts then parseError(err, tok) end
    local exprs = {}
    for i = 1, #parts do
      local part = parts[i]
      if part.type == "lit" then
        local s = node("String", tok.line, tok.col)
        s.v = part.value
        exprs[#exprs + 1] = s
      else
        local subTokens, subErrors = Lexer.lex(part.source, self.filename)
        for i2 = 1, #subErrors do
          addError("in interpolation: " .. subErrors[i2].msg, tok.line, tok.col)
        end
        subTokens[#subTokens].t = "eof"
        local sub = {
          tokens = subTokens, pos = 1, errors = {}, filename = self.filename, depth = 0, generated = 0,
        }
        local expr = Parser._exprFrom(sub, parseBlock, parseFunctionBody)
        for i2 = 1, #sub.errors do
          addError("in interpolation: " .. sub.errors[i2].msg, tok.line, tok.col)
        end
        if expr then
          local call = node("Call", tok.line, tok.col)
          call.fn = node("Name", tok.line, tok.col); call.fn.v = "tostring"
          call.args = { expr }
          exprs[#exprs + 1] = call
        end
      end
    end
    if #exprs == 0 then
      local s = node("String", tok.line, tok.col); s.v = ""; return s
    end
    if #exprs == 1 then return exprs[1] end
    local acc = exprs[1]
    for i = 2, #exprs do
      local b = node("Bin", tok.line, tok.col)
      b.op = ".."; b.l = acc; b.r = exprs[i]
      acc = b
    end
    return acc
  end

  local function parsePrimary()
    local tk = cur()
    local tt = tk.t
    enter()
    local result
    if tt == "nil" then
      nextTok(); result = node("Nil", tk.line, tk.col)
    elseif tt == "true" then
      nextTok(); result = node("True", tk.line, tk.col)
    elseif tt == "false" then
      nextTok(); result = node("False", tk.line, tk.col)
    elseif tt == "number" then
      nextTok(); result = node("Number", tk.line, tk.col); result.v = tk.v; result.raw = tk.raw
    elseif tt == "string" then
      nextTok(); result = node("String", tk.line, tk.col); result.v = tk.v
    elseif tt == "interp" then
      nextTok(); result = parseInterpolated(tk)
    elseif tt == "..." then
      nextTok(); result = node("Vararg", tk.line, tk.col)
    elseif tt == "function" then
      nextTok(); result = parseFunctionBody(false, nil)
    elseif tt == "{" then
      result = parseTable()
    elseif tt == "(" then
      nextTok()
      local inner = parseExpr()
      expect(")")
      result = node("Paren", tk.line, tk.col)
      result.e = inner
    elseif tt == "if" then
      -- Luau if-expression: if cond then a elseif cond then b else c
      nextTok()
      local branches = {}
      local cond = parseExpr()
      expect("then")
      local val = parseExpr()
      branches[#branches + 1] = { cond = cond, value = val }
      while accept("elseif") do
        local c2 = parseExpr()
        expect("then")
        local v2 = parseExpr()
        branches[#branches + 1] = { cond = c2, value = v2 }
      end
      expect("else")
      local other = parseExpr()
      result = node("IfExpr", tk.line, tk.col)
      result.branches = branches
      result.orelse = other
    elseif tt == "name" then
      nextTok(); result = node("Name", tk.line, tk.col); result.v = tk.v
    else
      parseError("unexpected symbol '" .. tostring(tk.v) .. "'", tk)
    end
    leave()
    return result
  end

  local function parseArgs()
    local args = {}
    local tk = cur()
    if tk.t == "(" then
      nextTok()
      if not check(")") then args = parseExprList() end
      expect(")")
    elseif tk.t == "{" then
      args[1] = parseTable()
    elseif tk.t == "string" then
      nextTok()
      local s = node("String", tk.line, tk.col); s.v = tk.v
      args[1] = s
    elseif tk.t == "interp" then
      nextTok(); args[1] = parseInterpolated(tk)
    else
      parseError("function arguments expected", tk)
    end
    return args
  end

  -- A '::' right after an expression is a Luau type assertion only when it is
  -- on the same line and is not shaped like a label (":: name ::"), otherwise
  -- it starts the next statement's label.
  local function isTypeAssert()
    local it = cur()
    local prev = self.tokens[self.pos - 1]
    if not prev or prev.line ~= it.line then return false end
    local t1 = peek(1)
    local t2 = peek(2)
    if t1.t == "name" and t2.t == "::" then return false end
    return true
  end

  local function parseSuffixed()
    local e = parsePrimary()
    while true do
      local tk = cur()
      if tk.t == "." then
        nextTok()
        local nm = expect("name")
        local idx = node("Index", tk.line, tk.col)
        idx.obj = e
        local key = node("String", nm.line, nm.col); key.v = nm.v
        idx.key = key
        idx.dot = true
        e = idx
      elseif tk.t == "[" then
        nextTok()
        local key = parseExpr()
        expect("]")
        local idx = node("Index", tk.line, tk.col)
        idx.obj = e; idx.key = key; idx.dot = false
        e = idx
      elseif tk.t == ":" then
        nextTok()
        local nm = expect("name")
        local args = parseArgs()
        local call = node("Call", tk.line, tk.col)
        call.fn = e; call.method = nm.v; call.args = args
        e = call
      elseif tk.t == "(" or tk.t == "{" or tk.t == "string" or tk.t == "interp" then
        local args = parseArgs()
        local call = node("Call", tk.line, tk.col)
        call.fn = e; call.args = args
        e = call
      elseif tk.t == "::" and isTypeAssert() then
        -- Luau type assertion: value :: T
        nextTok()
        skipType({ [","] = true, [")"] = true, ["]"] = true, ["}"] = true, [";"] = true,
          ["="] = true, ["then"] = true, ["do"] = true, ["end"] = true, ["else"] = true,
          ["elseif"] = true, ["until"] = true, ["or"] = true, ["and"] = true, ["+"] = true,
          ["-"] = true, ["*"] = true, ["/"] = true, [".."] = true, ["=="] = true, ["~="] = true,
          ["<"] = true, [">"] = true, ["<="] = true, [">="] = true }, "assert")
      elseif tk.t == "<" then
        -- Luau generic call f<T>(...): only consume when a matching '>' is
        -- followed by '('.
        local save = self.pos
        local depth = 0
        local ok = false
        while not check("eof") do
          local t = nextTok().t
          if t == "<" then depth = depth + 1
          elseif t == ">" then
            depth = depth - 1
            if depth == 0 then ok = check("("); break end
          elseif t == "end" or t == "do" or t == "then" or t == "=" then break end
        end
        if not ok then self.pos = save; break end
      else
        break
      end
    end
    return e
  end

  local function parseSub(limit)
    enter()
    local tk = cur()
    local e
    if UNARY[tk.t] then
      nextTok()
      local operand = parseSub(11)
      e = node("Un", tk.line, tk.col)
      e.op = tk.t
      e.e = operand
    else
      e = parseSuffixed()
    end
    while true do
      local opTok = cur()
      local pri = BINPRI[opTok.t]
      if not pri or pri[1] <= limit then break end
      nextTok()
      local rhs = parseSub(pri[2])
      local b = node("Bin", opTok.line, opTok.col)
      b.op = opTok.t; b.l = e; b.r = rhs
      e = b
    end
    leave()
    return e
  end
  parseExpr = function() return parseSub(0) end

  parseExprList = function()
    local list = { parseExpr() }
    while accept(",") do list[#list + 1] = parseExpr() end
    return list
  end

  local function expressionStarts(t)
    return t == "name" or t == "number" or t == "string" or t == "interp" or t == "nil" or
      t == "true" or t == "false" or t == "function" or t == "{" or t == "(" or t == "..." or
      t == "if" or UNARY[t] == true
  end

  local function parseAssignmentOrCall()
    local startTok = cur()
    local target = parseSuffixed()
    if COMPOUND[cur().t] then
      local opTok = nextTok()
      local op = COMPOUND[opTok.t]
      local value = parseExpr()
      local st = node("Do", startTok.line, startTok.col)
      st.block = {}
      if target.t == "Name" then
        local rhs = node("Bin", opTok.line, opTok.col)
        rhs.op = op; rhs.l = U_copy(target); rhs.r = value
        local as = node("Assign", startTok.line, startTok.col)
        as.targets = { target }; as.exprs = { rhs }
        st.block[1] = as
      elseif target.t == "Index" then
        self.generated = self.generated + 1
        local tn = "_0x$t" .. self.generated
        local kn = "_0x$k" .. self.generated
        local dt = node("Local", startTok.line, startTok.col)
        dt.names = { tn, kn }; dt.exprs = { target.obj, target.key }
        local tnode = node("Name", startTok.line, startTok.col); tnode.v = tn
        local knode = node("Name", startTok.line, startTok.col); knode.v = kn
        local lhsIndex = node("Index", startTok.line, startTok.col)
        lhsIndex.obj = tnode; lhsIndex.key = knode
        local getIndex = node("Index", startTok.line, startTok.col)
        getIndex.obj = U_copy(tnode); getIndex.key = U_copy(knode)
        local rhs = node("Bin", opTok.line, opTok.col)
        rhs.op = op; rhs.l = getIndex; rhs.r = value
        local as = node("Assign", startTok.line, startTok.col)
        as.targets = { lhsIndex }; as.exprs = { rhs }
        st.block[1] = dt
        st.block[2] = as
      else
        parseError("cannot assign to this expression", cur())
      end
      return st
    end
    if check("=") or check(",") then
      local targets = { target }
      while accept(",") do targets[#targets + 1] = parseSuffixed() end
      for i = 1, #targets do
        local tt = targets[i].t
        if tt ~= "Name" and tt ~= "Index" then
          parseError("cannot assign to this expression", startTok)
        end
      end
      expect("=")
      local exprs = parseExprList()
      local as = node("Assign", startTok.line, startTok.col)
      as.targets = targets; as.exprs = exprs
      return as
    end
    if target.t ~= "Call" then
      parseError("syntax error near '" .. tostring(cur().v) .. "'", cur())
    end
    local st = node("CallStat", startTok.line, startTok.col)
    st.call = target
    return st
  end

  -- Local helper used by compound assignment to duplicate a tiny AST node.
  parseStatement = function()
    local tk = cur()
    local tt = tk.t
    if tt == ";" then nextTok(); return nil end
    if tt == "::" then
      nextTok()
      local nm = expect("name")
      expect("::")
      local st = node("Label", tk.line, tk.col)
      st.name = nm.v
      return st
    end
    if tt == "break" then
      nextTok()
      return node("Break", tk.line, tk.col)
    end
    if tt == "goto" then
      nextTok()
      local nm = expect("name")
      local st = node("Goto", tk.line, tk.col)
      st.name = nm.v
      return st
    end
    if tt == "do" then
      nextTok()
      local st = node("Do", tk.line, tk.col)
      st.block = parseBlock({ ["end"] = true })
      expect("end")
      return st
    end
    if tt == "while" then
      nextTok()
      local st = node("While", tk.line, tk.col)
      st.cond = parseExpr()
      expect("do")
      st.block = parseBlock({ ["end"] = true })
      expect("end")
      return st
    end
    if tt == "repeat" then
      nextTok()
      local st = node("Repeat", tk.line, tk.col)
      st.block = parseBlock({ ["until"] = true })
      expect("until")
      st.cond = parseExpr()
      return st
    end
    if tt == "if" then
      nextTok()
      local st = node("If", tk.line, tk.col)
      st.branches = {}
      local cond = parseExpr()
      expect("then")
      local blk = parseBlock({ ["elseif"] = true, ["else"] = true, ["end"] = true })
      st.branches[1] = { cond = cond, block = blk }
      while accept("elseif") do
        local c2 = parseExpr()
        expect("then")
        local b2 = parseBlock({ ["elseif"] = true, ["else"] = true, ["end"] = true })
        st.branches[#st.branches + 1] = { cond = c2, block = b2 }
      end
      if accept("else") then
        st.orelse = parseBlock({ ["end"] = true })
      end
      expect("end")
      return st
    end
    if tt == "for" then
      nextTok()
      local first = expect("name")
      if check("=") then
        nextTok()
        local st = node("NumFor", tk.line, tk.col)
        st.var = first.v
        st.from = parseExpr()
        expect(",")
        st.to = parseExpr()
        if accept(",") then st.step = parseExpr() end
        expect("do")
        st.block = parseBlock({ ["end"] = true })
        expect("end")
        return st
      end
      local names = { first.v }
      if check(":") then nextTok(); skipType({ [","] = true, ["in"] = true }, "param") end
      while accept(",") do
        local nm = expect("name")
        names[#names + 1] = nm.v
        if check(":") then nextTok(); skipType({ [","] = true, ["in"] = true }, "param") end
      end
      expect("in")
      local exprs = parseExprList()
      expect("do")
      local st = node("GenFor", tk.line, tk.col)
      st.names = names
      st.exprs = exprs
      st.block = parseBlock({ ["end"] = true })
      expect("end")
      return st
    end
    if tt == "function" then
      nextTok()
      local base = node("Name", tk.line, tk.col)
      local nm = expect("name")
      base.v = nm.v
      local target = base
      local isMethod = false
      local fname = nm.v
      while accept(".") do
        local part = expect("name")
        local idx = node("Index", part.line, part.col)
        idx.obj = target
        local key = node("String", part.line, part.col); key.v = part.v
        idx.key = key; idx.dot = true
        target = idx
        fname = fname .. "." .. part.v
      end
      if accept(":") then
        local part = expect("name")
        local idx = node("Index", part.line, part.col)
        idx.obj = target
        local key = node("String", part.line, part.col); key.v = part.v
        idx.key = key; idx.dot = true
        target = idx
        isMethod = true
        fname = fname .. ":" .. part.v
      end
      local fn = parseFunctionBody(isMethod, fname)
      local st = node("FunctionStat", tk.line, tk.col)
      st.target = target
      st.func = fn
      return st
    end
    if tt == "local" then
      nextTok()
      if accept("function") then
        local nm = expect("name")
        local fn = parseFunctionBody(false, nm.v)
        local st = node("LocalFunction", tk.line, tk.col)
        st.name = nm.v; st.func = fn
        return st
      end
      local names = {}
      local attrs = {}
      repeat
        local nm = expect("name")
        names[#names + 1] = nm.v
        attrs[#names] = nil
        if check("<") then
          nextTok()
          local at = expect("name")
          expect(">")
          attrs[#names] = at.v
        end
        if check(":") then nextTok(); skipType({ [","] = true, ["="] = true, [";"] = true }, "local") end
      until not accept(",")
      local st = node("Local", tk.line, tk.col)
      st.names = names
      st.attrs = attrs
      st.exprs = {}
      if accept("=") then st.exprs = parseExprList() end
      return st
    end
    if tt == "return" then
      nextTok()
      local st = node("Return", tk.line, tk.col)
      st.exprs = {}
      if not BLOCK_END[cur().t] and not check(";") and expressionStarts(cur().t) then
        st.exprs = parseExprList()
      end
      accept(";")
      return st
    end
    if tt == "name" and tk.v == "continue" then
      local nxt = peek(1)
      if nxt.line > tk.line or BLOCK_END[nxt.t] or STMT_START[nxt.t] or nxt.t == ";" then
        nextTok()
        return node("Continue", tk.line, tk.col)
      end
    end
    if tt == "name" and tk.v == "type" and peek(1).t == "name" then
      local after = peek(2).t
      if after == "=" or after == "<" then
        parseTypeAlias()
        return nil
      end
    end
    if tt == "name" and tk.v == "export" and peek(1).t == "name" and peek(1).v == "type" then
      nextTok()
      parseTypeAlias()
      return nil
    end
    return parseAssignmentOrCall()
  end

  local function sync()
    local depth = 0
    local first = true
    local prevLine = cur().line
    while not check("eof") do
      local t = cur().t
      local line = cur().line
      if depth == 0 then
        if BLOCK_END[t] then return end
        -- A bare name starting a fresh line is an assignment or a call, i.e.
        -- the beginning of the next statement; stop skipping there.
        if not first and (STMT_START[t] or (t == "name" and line > prevLine)) then
          return
        end
      end
      if t == "(" or t == "{" or t == "[" then depth = depth + 1
      elseif t == ")" or t == "}" or t == "]" then
        if depth > 0 then depth = depth - 1 end
      end
      prevLine = line
      nextTok()
      first = false
    end
  end

  parseBlock = function(terminators)
    local block = {}
    while not check("eof") and not terminators[cur().t] do
      local startPos = self.pos
      local ok, err
      enter()
      ok, err = pcall(parseStatement)
      leave()
      if not ok then
        if type(err) == "table" and err.__parse then
          addError(err.msg, err.line, err.col)
        else
          addError("internal parser error: " .. tostring(err), cur().line, cur().col)
        end
        sync()
        if self.pos == startPos then nextTok() end
        if #self.errors > 40 then break end
      else
        block[#block + 1] = err
      end
    end
    return block
  end

  -- Exposed for interpolation sub-parsing.
  Parser._exprFrom = function(sub, _, _)
    local saved = {}
    -- Reuse this record's parseExpr by temporarily swapping the state fields.
    local outer = self
    local function subPeek(off)
      local p = sub.pos + (off or 0)
      if p > #sub.tokens then p = #sub.tokens end
      return sub.tokens[p]
    end
    local function subNext()
      local t = subPeek()
      if sub.pos < #sub.tokens then sub.pos = sub.pos + 1 end
      return t
    end
    local function subCheck(t) return subPeek().t == t end
    local function subExpect(t)
      if subCheck(t) then return subNext() end
      parseError("'" .. t .. "' expected", subPeek())
    end

    local function subPrimary()
      local tk = subPeek()
      local tt = tk.t
      local e
      if tt == "nil" then subNext(); e = node("Nil", tk.line, tk.col)
      elseif tt == "true" then subNext(); e = node("True", tk.line, tk.col)
      elseif tt == "false" then subNext(); e = node("False", tk.line, tk.col)
      elseif tt == "number" then subNext(); e = node("Number", tk.line, tk.col); e.v = tk.v; e.raw = tk.raw
      elseif tt == "string" then subNext(); e = node("String", tk.line, tk.col); e.v = tk.v
      elseif tt == "..." then subNext(); e = node("Vararg", tk.line, tk.col)
      elseif tt == "name" then subNext(); e = node("Name", tk.line, tk.col); e.v = tk.v
      elseif tt == "function" then
        subNext()
        -- Interpolation rarely contains functions; reject gracefully.
        parseError("function literals inside interpolated strings are unsupported", tk)
      elseif tt == "{" then
        -- Balanced table literal copy.
        subNext()
        local t = node("Table", tk.line, tk.col); t.fields = {}
        while not subCheck("}") and not subCheck("eof") do subNext() end
        subExpect("}")
        e = t
      elseif tt == "(" then
        subNext()
        local inner = Parser._exprFrom(sub, nil, nil)
        subExpect(")")
        e = node("Paren", tk.line, tk.col); e.e = inner
      else
        parseError("unexpected symbol inside interpolation", tk)
      end
      -- Suffix chain: index/dot/call.
      while true do
        local tk2 = subPeek()
        if tk2.t == "." then
          subNext(); local nm = subExpect("name")
          local idx = node("Index", tk2.line, tk2.col); idx.obj = e
          local key = node("String", nm.line, nm.col); key.v = nm.v
          idx.key = key; idx.dot = true; e = idx
        elseif tk2.t == "[" then
          subNext(); local k2 = Parser._exprFrom(sub, nil, nil); subExpect("]")
          local idx = node("Index", tk2.line, tk2.col); idx.obj = e; idx.key = k2; e = idx
        elseif tk2.t == ":" then
          subNext(); local nm = subExpect("name")
          if not subCheck("(") then parseError("function arguments expected", subPeek()) end
          subNext()
          local args = {}
          if not subCheck(")") then
            args[1] = Parser._exprFrom(sub, nil, nil)
            while subCheck(",") do subNext(); args[#args + 1] = Parser._exprFrom(sub, nil, nil) end
          end
          subExpect(")")
          local call = node("Call", tk2.line, tk2.col); call.fn = e; call.method = nm.v; call.args = args
          e = call
        elseif tk2.t == "(" then
          subNext()
          local args = {}
          if not subCheck(")") then
            args[1] = Parser._exprFrom(sub, nil, nil)
            while subCheck(",") do subNext(); args[#args + 1] = Parser._exprFrom(sub, nil, nil) end
          end
          subExpect(")")
          local call = node("Call", tk2.line, tk2.col); call.fn = e; call.args = args
          e = call
        else
          break
        end
      end
      return e
    end

    local function subBin(limit)
      local tk = subPeek()
      local e
      if UNARY[tk.t] then
        subNext()
        local operand = subBin(11)
        e = node("Un", tk.line, tk.col); e.op = tk.t; e.e = operand
      else
        e = subPrimary()
      end
      while true do
        local op = subPeek()
        local pri = BINPRI[op.t]
        if not pri or pri[1] <= limit then break end
        subNext()
        local rhs = subBin(pri[2])
        local b = node("Bin", op.line, op.col); b.op = op.t; b.l = e; b.r = rhs
        e = b
      end
      return e
    end

    local ok, res = pcall(subBin, 0)
    if not ok then
      if type(res) == "table" and res.__parse then
        sub.errors[#sub.errors + 1] = { msg = res.msg, line = res.line, col = res.col }
      else
        sub.errors[#sub.errors + 1] = { msg = tostring(res), line = 0, col = 0 }
      end
      return nil
    end
    return res
  end

  local ast = {}
  ast.block = parseBlock({})
  if not check("eof") then
    addError("unexpected token '" .. tostring(cur().v) .. "' at top level", cur().line, cur().col)
  end

  -- Merge lexer diagnostics first; sort by line so the CLI can show context.
  local all = {}
  for i = 1, #lexErrors do all[#all + 1] = lexErrors[i] end
  for i = 1, #self.errors do all[#all + 1] = self.errors[i] end
  for i = 1, #all do all[i].filename = self.filename end
  table.sort(all, function(a, b)
    if a.line == b.line then return (a.col or 0) < (b.col or 0) end
    return a.line < b.line
  end)
  return ast, all, tokens
end

return Parser
