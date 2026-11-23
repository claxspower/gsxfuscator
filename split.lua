-- split.lua -- top-level chunking for very large inputs.
--
-- The full pipeline keeps a whole program in memory as an AST, which is fine
-- for ordinary scripts but not for multi-megabyte files inside a browser VM.
-- This module cuts a source file at top-level statement boundaries so each
-- piece can go through the pipeline on its own, then rewrites chunk-level
-- `local` declarations into environment assignments so values still cross the
-- piece boundaries.
--
-- Safety rules:
--   * a cut is only made at a newline/semicolon outside strings, comments,
--     brackets and every block opener;
--   * the token before the cut must be able to end a statement and the next
--     token must be able to start one;
--   * top-level gotos/labels and attributed locals disable the fast path (the
--     caller then builds the file as one unit).
--
-- The rewrite is intentionally limited to `local` at block depth zero. Locals
-- inside functions and control-flow blocks are never touched.

local Split = {}

local function isIdentStart(c)
  return c ~= nil and (c:match("[%a_]") ~= nil)
end

local function isIdentChar(c)
  return c ~= nil and (c:match("[%w_]") ~= nil)
end

local STARTERS = {
  ["local"] = true, ["function"] = true, ["if"] = true, ["for"] = true,
  ["while"] = true, ["repeat"] = true, ["do"] = true, ["return"] = true,
  ["break"] = true, ["goto"] = true,
}

local OPENER = {
  ["function"] = true, ["if"] = true, ["for"] = true, ["while"] = true,
  ["do"] = true, ["repeat"] = true,
}

-- Skip a quoted string; returns the position after the closing quote.
local function skipQuoted(src, i, n, quote)
  i = i + 1
  while i <= n do
    local c = src:sub(i, i)
    if c == "\\" then
      i = i + 2
    elseif c == quote then
      return i + 1
    elseif c == "\n" or c == "\r" then
      return i
    else
      i = i + 1
    end
  end
  return n + 1
end

-- Long bracket opener at i: returns level or nil (i points at "[").
local function longLevel(src, i, n)
  if src:sub(i, i) ~= "[" then return nil end
  local j = i + 1
  while j <= n and src:sub(j, j) == "=" do j = j + 1 end
  if src:sub(j, j) == "[" then return j - i - 1 end
  return nil
end

-- Skip a long bracket body starting at the "["; returns position after close.
local function skipLong(src, i, n, level)
  local close = "]" .. string.rep("=", level) .. "]"
  local at = src:find(close, i, true)
  if at then return at + #close end
  return n + 1
end

-- Skip whitespace and comments starting at i; returns the next code position.
local function skipTrivia(src, i, n)
  while i <= n do
    local c = src:sub(i, i)
    if c == " " or c == "\t" or c == "\r" or c == "\n" or c == "\v" or
       c == "\f" then
      i = i + 1
    elseif c == "-" and src:sub(i + 1, i + 1) == "-" then
      local level = longLevel(src, i + 2, n)
      if level then
        i = skipLong(src, i + 2, n, level)
      else
        local e = src:find("\n", i + 2, true)
        i = e and (e + 1) or (n + 1)
      end
    else
      return i
    end
  end
  return i
end

-- Reads one identifier at i; returns word and the position after it.
local function readName(src, i, n)
  local j = i + 1
  while j <= n and isIdentChar(src:sub(j, j)) do j = j + 1 end
  return src:sub(i, j - 1), j
end

-- What can start a statement at top level?
local function startsStatement(src, i, n)
  i = skipTrivia(src, i, n)
  if i > n then return false end
  local c = src:sub(i, i)
  if c == ";" then return true end
  if c == ":" and src:sub(i + 1, i + 1) == ":" then return true end
  if not isIdentStart(c) then return false end
  local word = readName(src, i, n)
  if STARTERS[word] then return true end
  return word ~= "end" and word ~= "else" and word ~= "elseif" and
    word ~= "until" and word ~= "then" and word ~= "in" and
    word ~= "and" and word ~= "or" and word ~= "not"
end

-- Walks the whole source once and returns top-level statement boundaries.
-- Returns: ranges, unsafe, hasReturn
local function scan(src, opts)
  local n = #src
  local target = opts.chunkBytes or 196608
  local ranges = {}
  local segStart = 1
  local depth = 0
  local paren = 0
  local pendingDo = false
  local lastTerminal = false
  local atStart = true
  local unsafe = false
  local hasReturn = false
  local i = 1

  local function cut(at, include)
    local stop = include and at or (at - 1)
    if stop >= segStart then
      local text = src:sub(segStart, stop)
      if text:find("%S") then
        ranges[#ranges + 1] = { from = segStart, to = stop }
      end
      segStart = stop + 1
    end
    if hasReturn then
      -- tracked below; the flag is reset by the caller for the last range
    end
  end

  while i <= n do
    local c = src:sub(i, i)
    if c == " " or c == "\t" or c == "\r" or c == "\v" or c == "\f" then
      i = i + 1
    elseif c == "\n" then
      if depth == 0 and paren == 0 and lastTerminal and
         #src - segStart >= 0 and (i - segStart) >= target and
         startsStatement(src, i + 1, n) then
        cut(i, true)
      end
      atStart = atStart or (depth == 0 and paren == 0)
      i = i + 1
    elseif c == "-" and src:sub(i + 1, i + 1) == "-" then
      local level = longLevel(src, i + 2, n)
      if level then
        i = skipLong(src, i + 2, n, level)
      else
        local e = src:find("\n", i + 2, true)
        i = e or (n + 1)
      end
    elseif c == "\"" or c == "'" then
      i = skipQuoted(src, i, n, c)
      lastTerminal = true
      atStart = false
    elseif c == "[" and longLevel(src, i, n) then
      i = skipLong(src, i, n, longLevel(src, i, n))
      lastTerminal = true
      atStart = false
    elseif c == "[" then
      paren = paren + 1
      lastTerminal = false
      atStart = false
      i = i + 1
    elseif c == "]" then
      if paren > 0 then paren = paren - 1 end
      lastTerminal = true
      atStart = false
      i = i + 1
    elseif c == "(" then
      paren = paren + 1
      lastTerminal = false
      atStart = false
      i = i + 1
    elseif c == ")" then
      if paren > 0 then paren = paren - 1 end
      lastTerminal = true
      atStart = false
      i = i + 1
    elseif c == "{" then
      paren = paren + 1
      lastTerminal = false
      atStart = false
      i = i + 1
    elseif c == "}" then
      if paren > 0 then paren = paren - 1 end
      lastTerminal = true
      atStart = false
      i = i + 1
    elseif c == ";" then
      if depth == 0 and paren == 0 then
        lastTerminal = true
        if (i - segStart) >= target then cut(i, true) end
        atStart = true
      end
      i = i + 1
    elseif isIdentStart(c) then
      local word, j = readName(src, i, n)
      local wasStart = atStart
      if depth == 0 and paren == 0 and word == "goto" then
        unsafe = true
      end
      if depth == 0 and word == "return" and paren == 0 then
        hasReturn = true
      end
      if word == "end" then
        if depth > 0 then depth = depth - 1 end
        if depth == 0 and paren == 0 then
          atStart = true
          if (j - segStart) >= target and startsStatement(src, j, n) then
            cut(j - 1, true)
          end
        end
        lastTerminal = true
      elseif word == "until" then
        if depth > 0 then depth = depth - 1 end
        -- `until` is followed by the repeat condition, so the statement ends
        -- only at the last token of that expression, never at the keyword.
        atStart = false
        lastTerminal = false
      elseif OPENER[word] then
        if word == "do" and pendingDo then
          pendingDo = false
        else
          depth = depth + 1
          atStart = false
        end
        if word == "for" or word == "while" then pendingDo = true end
        lastTerminal = false
      elseif word == "then" or word == "else" or word == "elseif" or
             word == "in" then
        lastTerminal = false
      elseif word == "true" or word == "false" or word == "nil" or
             word == "break" then
        lastTerminal = true
        atStart = false
      else
        lastTerminal = true
        atStart = false
      end
      if wasStart and depth == 0 and word == "goto" then unsafe = true end
      i = j
    elseif c == ":" and src:sub(i + 1, i + 1) == ":" then
      if depth == 0 and paren == 0 then unsafe = true end
      lastTerminal = true
      atStart = false
      i = i + 2
    elseif c == "=" then
      lastTerminal = false
      atStart = false
      i = i + 1
    else
      if c:match("[%d]") then
        local j = i + 1
        while j <= n and src:sub(j, j):match("[%w_%.]") do j = j + 1 end
        i = j
        lastTerminal = true
      else
        i = i + 1
        lastTerminal = false
      end
      atStart = false
    end
  end

  if segStart <= n then
    local text = src:sub(segStart, n)
    if text:find("%S") then
      ranges[#ranges + 1] = { from = segStart, to = n }
    end
  end

  if #ranges > 0 then
    local last = ranges[#ranges]
    -- A return in the final range is the chunk's own return and must survive.
    local lastText = src:sub(last.from, last.to)
    last.returns = hasReturn and lastText:find("%f[%w_]return%f[^%w_]") ~= nil
  end

  return ranges, unsafe, hasReturn
end

-- Rewrite block-level `local` declarations into environment assignments.
-- Returns text, unsafe.
local function globalize(text)
  local n = #text
  local out = {}
  local copied = 1
  local depth = 0
  local paren = 0
  local pendingDo = false
  local atStart = true
  local unsafe = false
  local i = 1

  local function copyTo(pos)
    if pos > copied then out[#out + 1] = text:sub(copied, pos - 1) end
  end

  while i <= n do
    local c = text:sub(i, i)
    if c == " " or c == "\t" or c == "\r" or c == "\v" or c == "\f" then
      i = i + 1
    elseif c == "\n" then
      if depth == 0 and paren == 0 then atStart = true end
      i = i + 1
    elseif c == "-" and text:sub(i + 1, i + 1) == "-" then
      local level = longLevel(text, i + 2, n)
      if level then
        i = skipLong(text, i + 2, n, level)
      else
        local e = text:find("\n", i + 2, true)
        i = e or (n + 1)
      end
    elseif c == "\"" or c == "'" then
      i = skipQuoted(text, i, n, c)
      atStart = false
    elseif c == "[" and longLevel(text, i, n) then
      i = skipLong(text, i, n, longLevel(text, i, n))
      atStart = false
    elseif c == "[" or c == "(" or c == "{" then
      paren = paren + 1
      atStart = false
      i = i + 1
    elseif c == "]" or c == ")" or c == "}" then
      if paren > 0 then paren = paren - 1 end
      atStart = false
      i = i + 1
    elseif c == ";" then
      if depth == 0 and paren == 0 then atStart = true end
      i = i + 1
    elseif isIdentStart(c) then
      local word, j = readName(text, i, n)
      local wasStart = atStart and depth == 0 and paren == 0
      if word == "local" and wasStart then
        local after = skipTrivia(text, j, n)
        local nxt = after <= n and text:sub(after, after) or ""
        if nxt == "<" then
          unsafe = true
          atStart = false
          i = j
        elseif isIdentStart(nxt) then
          local nword = readName(text, after, n)
          if nword == "function" then
            -- `local function f` -> `function f`; the function token is
            -- scanned again below so it still opens a block.
            out[#out + 1] = text:sub(copied, i - 1)
            copied = j
            atStart = false
            i = j
          else
            -- Walk the name list: Name {',' Name}.
            local lastEnd = select(2, readName(text, after, n))
            local p = lastEnd
            while true do
              local q = skipTrivia(text, p, n)
              local ch = q <= n and text:sub(q, q) or ""
              if ch == "<" then
                unsafe = true
                break
              elseif ch == "," then
                local r = skipTrivia(text, q + 1, n)
                if not isIdentStart(text:sub(r, r)) then break end
                lastEnd = select(2, readName(text, r, n))
                p = lastEnd
              else
                break
              end
            end
            local q = skipTrivia(text, lastEnd, n)
            local ch = q <= n and text:sub(q, q) or ""
            out[#out + 1] = text:sub(copied, i - 1)
            copied = j
            if unsafe then
              -- leave it alone; the caller falls back to a single build
            elseif ch == "=" then
              -- Plain assignment target list; the keyword is simply dropped.
            else
              out[#out + 1] = text:sub(copied, lastEnd - 1)
              out[#out + 1] = " = nil"
              copied = lastEnd
            end
            atStart = false
            i = lastEnd
          end
        else
          atStart = false
          i = j
        end
      elseif word == "end" or word == "until" then
        if depth > 0 then depth = depth - 1 end
        if depth == 0 then atStart = true end
        i = j
      elseif OPENER[word] then
        if word == "do" and pendingDo then
          pendingDo = false
        else
          depth = depth + 1
          atStart = false
        end
        if word == "for" or word == "while" then pendingDo = true end
        i = j
      elseif word == "then" or word == "else" or word == "elseif" or
             word == "in" then
        atStart = false
        i = j
      else
        atStart = false
        i = j
      end
    else
      if c:match("[%d]") then
        local j = i + 1
        while j <= n and text:sub(j, j):match("[%w_%.]") do j = j + 1 end
        i = j
      else
        i = i + 1
      end
      atStart = false
    end
  end

  copyTo(n + 1)
  if unsafe then return text, true end
  return table.concat(out), false
end

-- Split a source into buildable chunks.
--
-- Returns: {
--   chunks = { { text = ..., line = ..., returns = bool }, ... },
--   unsafe = bool,
--   reason = string|nil,
--   split = bool
-- }
function Split.run(src, opts)
  opts = opts or {}
  if type(src) ~= "string" or #src == 0 then
    return { chunks = {}, unsafe = true, reason = "empty", split = false }
  end
  local ranges, unsafe, hasReturn = scan(src, opts)
  if unsafe then
    return { chunks = {}, unsafe = true, reason = "goto", split = false }
  end
  if #ranges <= 1 then
    return {
      chunks = { { text = src, line = 1, returns = hasReturn } },
      unsafe = false, split = false, hasReturn = hasReturn,
    }
  end

  local chunks = {}
  local line = 1
  local offset = 1
  for i = 1, #ranges do
    local r = ranges[i]
    local piece = src:sub(r.from, r.to)
    local text, bad = globalize(piece)
    if bad then
      return { chunks = {}, unsafe = true, reason = "attributed-local",
        split = false }
    end
    local relative = 0
    for _ in src:sub(offset, r.from - 1):gmatch("\n") do relative = relative + 1 end
    chunks[#chunks + 1] = {
      text = text,
      line = line + relative,
      returns = r.returns and true or false,
    }
    line = line + relative
    offset = r.from
  end
  return {
    chunks = chunks,
    unsafe = false,
    split = #chunks > 1,
    hasReturn = hasReturn,
  }
end

Split.globalize = globalize
Split.scan = scan

return Split
