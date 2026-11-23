-- lexer.lua -- Lua 5.1/5.3/5.4 + Luau tokenizer with recoverable diagnostics.
local Lexer = {}

local KEYWORDS = {
  ["and"] = true, ["break"] = true, ["do"] = true, ["else"] = true, ["elseif"] = true,
  ["end"] = true, ["false"] = true, ["for"] = true, ["function"] = true, ["goto"] = true,
  ["if"] = true, ["in"] = true, ["local"] = true, ["nil"] = true, ["not"] = true,
  ["or"] = true, ["repeat"] = true, ["return"] = true, ["then"] = true, ["true"] = true,
  ["until"] = true, ["while"] = true,
}
Lexer.KEYWORDS = KEYWORDS

local OPS = {
  "...", "//=", "..=", "<<", ">>", "//", "==", "~=", "<=", ">=", "::", "->",
  "+=", "-=", "*=", "/=", "%=", "^=", "..",
  "+", "-", "*", "/", "%", "^", "#", "&", "~", "|", "<", ">", "=", "(", ")",
  "{", "}", "[", "]", ";", ":", ",", ".", "?",
}

local function utf8Encode(cp)
  if cp < 0x80 then return string.char(cp) end
  if cp < 0x800 then
    return string.char(0xC0 + math.floor(cp / 0x40), 0x80 + (cp % 0x40))
  end
  if cp < 0x10000 then
    return string.char(0xE0 + math.floor(cp / 0x1000),
      0x80 + (math.floor(cp / 0x40) % 0x40), 0x80 + (cp % 0x40))
  end
  return string.char(0xF0 + math.floor(cp / 0x40000),
    0x80 + (math.floor(cp / 0x1000) % 0x40),
    0x80 + (math.floor(cp / 0x40) % 0x40), 0x80 + (cp % 0x40))
end

local function parseHexFloat(text)
  local negative = false
  if text:sub(1, 1) == "-" then negative = true; text = text:sub(2) end
  text = text:gsub("^0[xX]", "")
  local mant, exp = text:match("^([%x%.]+)[pP]([+-]?%d+)$")
  if not mant then mant, exp = text, "0" end
  local ipart, fpart = mant:match("^(%x*)%.?(%x*)$")
  local v = 0
  for i = 1, #ipart do v = v * 16 + tonumber(ipart:sub(i, i), 16) end
  local scale = 1 / 16
  for i = 1, #fpart do
    v = v + tonumber(fpart:sub(i, i), 16) * scale
    scale = scale / 16
  end
  v = v * (2 ^ tonumber(exp))
  if negative then v = -v end
  return v
end

local function parseNumber(raw)
  local s = raw:gsub("_", "")
  local neg = false
  if s:sub(1, 1) == "-" then neg = true; s = s:sub(2) end
  local value
  if s:match("^0[xX]") then
    if s:match("[pP]") or s:match("%.") then
      value = parseHexFloat((neg and "-" or "") .. s)
    else
      value = tonumber(s)
    end
  elseif s:match("^0[bB]") then
    local digits = s:sub(3):gsub("[^01]", "")
    value = 0
    for i = 1, #digits do value = value * 2 + (digits:sub(i, i) == "1" and 1 or 0) end
  else
    value = tonumber(s)
  end
  if value == nil then return nil end
  if neg and value > 0 then value = -value end
  return value
end

function Lexer.lex(src, filename)
  local self = {
    src = src or "",
    len = #(src or ""),
    pos = 1,
    line = 1,
    col = 1,
    tokens = {},
    errors = {},
    filename = filename,
  }

  local function peek(off)
    local p = self.pos + (off or 0)
    if p > self.len then return nil end
    return self.src:sub(p, p)
  end

  local function advance(n)
    n = n or 1
    local chunk = self.src:sub(self.pos, self.pos + n - 1)
    for i = 1, #chunk do
      if chunk:sub(i, i) == "\n" then
        self.line = self.line + 1
        self.col = 1
      else
        self.col = self.col + 1
      end
    end
    self.pos = self.pos + n
  end

  local function addError(msg, line, col)
    self.errors[#self.errors + 1] = {
      line = line or self.line,
      col = col or self.col,
      msg = msg,
    }
  end

  -- Long bracket opener: returns level and length, or nil.
  local function longBracketAt(p)
    if self.src:sub(p, p) ~= "[" then return nil end
    local q = p + 1
    local eq = 0
    while self.src:sub(q, q) == "=" do eq = eq + 1; q = q + 1 end
    if self.src:sub(q, q) == "[" then return eq, q - p + 1 end
    return nil
  end

  local function readLongString(level, openerLen, isComment)
    local startLine, startCol = self.line, self.col
    advance(openerLen)
    local close = "]" .. string.rep("=", level) .. "]"
    local bodyStart = self.pos
    local closeAt = self.src:find(close, self.pos, true)
    local body, endPos
    if closeAt then
      body = self.src:sub(bodyStart, closeAt - 1)
      endPos = closeAt + #close
      advance(endPos - self.pos)
    else
      body = self.src:sub(bodyStart)
      advance(self.len - self.pos + 1)
      addError("unfinished long " .. (isComment and "comment" or "string") ..
        " (starting at line " .. startLine .. ")", startLine, startCol)
    end
    if body:sub(1, 1) == "\r" then body = body:sub(2) end
    if body:sub(1, 1) == "\n" then body = body:sub(2) end
    if not isComment then
      self.tokens[#self.tokens + 1] = {
        t = "string", v = body, raw = self.src:sub(bodyStart - openerLen, self.pos - 1),
        line = startLine, col = startCol,
      }
    end
  end

  local function readShortString(quote)
    local startLine, startCol = self.line, self.col
    advance(1)
    local out = {}
    local closed = false
    while self.pos <= self.len do
      local c = peek()
      if c == quote then
        advance(1)
        closed = true
        break
      elseif c == "\n" or c == "\r" then
        addError("unfinished string", startLine, startCol)
        break
      elseif c == "\\" then
        advance(1)
        local e = peek()
        if e == nil then
          addError("unfinished string escape", startLine, startCol)
          break
        elseif e == "a" then out[#out + 1] = "\7"; advance(1)
        elseif e == "b" then out[#out + 1] = "\8"; advance(1)
        elseif e == "f" then out[#out + 1] = "\12"; advance(1)
        elseif e == "n" then out[#out + 1] = "\n"; advance(1)
        elseif e == "r" then out[#out + 1] = "\r"; advance(1)
        elseif e == "t" then out[#out + 1] = "\t"; advance(1)
        elseif e == "v" then out[#out + 1] = "\11"; advance(1)
        elseif e == "\\" then out[#out + 1] = "\\"; advance(1)
        elseif e == "\"" then out[#out + 1] = "\""; advance(1)
        elseif e == "'" then out[#out + 1] = "'"; advance(1)
        elseif e == "\n" then out[#out + 1] = "\n"; advance(1)
        elseif e == "\r" then out[#out + 1] = "\n"; advance(1); if peek() == "\n" then advance(1) end
        elseif e == "z" then
          advance(1)
          while peek() and peek():match("%s") do advance(1) end
        elseif e == "x" then
          advance(1)
          local hx = self.src:sub(self.pos, self.pos + 1)
          if hx:match("^%x%x$") then
            out[#out + 1] = string.char(tonumber(hx, 16)); advance(2)
          else
            addError("hexadecimal digit expected", self.line, self.col)
          end
        elseif e == "u" then
          advance(1)
          if peek() == "{" then
            advance(1)
            local hs = self.src:match("^([%x]+)}", self.pos)
            if hs then
              out[#out + 1] = utf8Encode(tonumber(hs, 16))
              advance(#hs + 1)
            else
              addError("invalid unicode escape", self.line, self.col)
            end
          else
            addError("missing '{' in unicode escape", self.line, self.col)
          end
        elseif e:match("%d") then
          local ds = self.src:match("^(%d%d?%d?)", self.pos)
          local v = tonumber(ds)
          if v > 255 then
            addError("decimal escape too large", self.line, self.col)
            v = 255
          end
          out[#out + 1] = string.char(v)
          advance(#ds)
        else
          addError("invalid escape sequence '\\" .. e .. "'", self.line, self.col)
          out[#out + 1] = e
          advance(1)
        end
      else
        out[#out + 1] = c
        advance(1)
      end
    end
    if not closed then addError("unfinished string", startLine, startCol) end
    self.tokens[#self.tokens + 1] = {
      t = "string", v = table.concat(out), line = startLine, col = startCol,
    }
  end

  local function readInterp()
    local startLine, startCol = self.line, self.col
    advance(1)
    local out = {}
    local closed = false
    while self.pos <= self.len do
      local c = peek()
      if c == "`" then advance(1); closed = true; break end
      if c == "\\" then
        local nxt = peek(1)
        if nxt == "`" then out[#out + 1] = "`"; advance(2)
        elseif nxt == "\\" then out[#out + 1] = "\\"; advance(2)
        elseif nxt == "{" then out[#out + 1] = "{"; advance(2)
        else out[#out + 1] = c; advance(1) end
      else
        out[#out + 1] = c
        advance(1)
      end
    end
    if not closed then addError("unfinished interpolated string", startLine, startCol) end
    self.tokens[#self.tokens + 1] = {
      t = "interp", v = table.concat(out), line = startLine, col = startCol,
    }
  end

  if self.src:sub(1, 3) == "\239\187\191" then advance(3) end
  if self.src:sub(1, 2) == "#!" then
    local e = self.src:find("\n", self.pos, true) or (self.len + 1)
    advance(e - self.pos)
  end

  while self.pos <= self.len do
    local c = peek()
    local c2 = peek(1)
    local startLine, startCol = self.line, self.col

    if c:match("%s") then
      advance(1)
    elseif c == "-" and c2 == "-" then
      advance(2)
      local lbLevel, lbLen = longBracketAt(self.pos)
      if lbLevel then
        readLongString(lbLevel, lbLen, true)
      else
        local e = self.src:find("\n", self.pos, true) or (self.len + 1)
        advance(e - self.pos)
      end
    elseif c == "[" and longBracketAt(self.pos) then
      local level, openerLen = longBracketAt(self.pos)
      readLongString(level, openerLen, false)
    elseif c == "\"" or c == "'" then
      readShortString(c)
    elseif c == "`" then
      readInterp()
    elseif c:match("%d") or (c == "." and c2 and c2:match("%d")) then
      local start = self.pos
      if c == "0" and (c2 == "x" or c2 == "X") then
        advance(2)
        while peek() and (peek():match("[%x_%.]")) do advance(1) end
        if peek() and (peek() == "p" or peek() == "P") then
          advance(1)
          if peek() == "+" or peek() == "-" then advance(1) end
          while peek() and peek():match("%d") do advance(1) end
        end
      elseif c == "0" and (c2 == "b" or c2 == "B") then
        advance(2)
        while peek() and peek():match("[01_]") do advance(1) end
      else
        while peek() and peek():match("[%d_]") do advance(1) end
        if peek() == "." and peek(1) ~= "." then
          advance(1)
          while peek() and peek():match("[%d_]") do advance(1) end
        end
        if peek() and (peek() == "e" or peek() == "E") then
          advance(1)
          if peek() == "+" or peek() == "-" then advance(1) end
          while peek() and peek():match("%d") do advance(1) end
        end
      end
      local raw = self.src:sub(start, self.pos - 1)
      local value = parseNumber(raw)
      if value == nil then
        addError("malformed number '" .. raw .. "'", startLine, startCol)
        value = 0
      end
      self.tokens[#self.tokens + 1] = {
        t = "number", v = value, raw = raw, line = startLine, col = startCol,
      }
    elseif c:match("[%a_]") then
      local start = self.pos
      while peek() and peek():match("[%w_]") do advance(1) end
      local word = self.src:sub(start, self.pos - 1)
      self.tokens[#self.tokens + 1] = {
        t = KEYWORDS[word] and word or "name",
        v = word, line = startLine, col = startCol,
      }
    else
      local matched = nil
      for i = 1, #OPS do
        local op = OPS[i]
        if self.src:sub(self.pos, self.pos + #op - 1) == op then
          matched = op
          break
        end
      end
      if matched then
        advance(#matched)
        self.tokens[#self.tokens + 1] = {
          t = matched, v = matched, line = startLine, col = startCol,
        }
      else
        addError("unexpected character '" .. c .. "'", startLine, startCol)
        advance(1)
      end
    end
  end

  self.tokens[#self.tokens + 1] = {
    t = "eof", v = "<eof>", line = self.line, col = self.col,
  }
  return self.tokens, self.errors
end

return Lexer
