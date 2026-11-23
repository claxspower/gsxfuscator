-- big.lua -- large-input assembly for the browser pipeline.
--
-- A multi-megabyte script cannot be held as one AST + one prototype table
-- inside a browser wasm heap, and one chunk of ~50x expansion cannot be
-- delivered as a single string. This module decides when a source is built in
-- pieces, and provides the wrapper snippets that turn N independent outputs
-- into one program.
--
-- Each piece is a complete chunk of its own (own runtime, own keys), so the
-- assembled file is:
--
--   return (function(...)
--   do local __p=function(...) <piece 1> end __p(...) end
--   ...
--   do local __p=function(...) <piece N> end return __p(...) end
--   end)(...)
--
-- Every piece is wrapped in a vararg function because the compiled artifact
-- reads the host varargs (`return (function(<wall>)<state>={}; return
-- function(...) ... end)(...))`); a plain function body would reject `...` at
-- parse time. Each piece receives the same original arguments, and the last
-- piece forwards the script's return values.
--
-- Piece-level `local` declarations were rewritten to environment assignments
-- by src.split, so values cross piece boundaries the same way the source
-- ordered them. Those assignments must not land in the host globals: sandboxes
-- such as Luau's safe environment freeze the global table, and an executor's
-- global table is shared with every other script. Where `setfenv` exists the
-- pieces therefore run against a private table that reads through to the real
-- environment, so library lookups keep working while cross-piece values stay
-- inside the artifact. Lua 5.2+ dropped `setfenv`; there the pieces fall back
-- to plain globals, which those hosts allow. The per-piece IIFE scopes the
-- generated runtime's own locals, which keeps the finished file under the
-- 200-local function limit.
local Big = {}

-- Above this size the whole-file pipeline stops being memory-safe in a
-- browser wasm heap (2 MB source peaked near 500 MB natively, several times
-- that in an interpreter). Splitting starts well below the worst case.
Big.MIN_SPLIT = 327680

-- Flattening and opaque predicates multiply output by roughly 4x on top of
-- the VM's own ~11x. Below the cap that is affordable and gives the strongest
-- result; above it the VM, self-modifying blocks, anti-debug and integrity
-- layers stay on but the two source-level multipliers are dropped so the
-- artifact only grows ~12x instead of ~50x.
Big.HARD_MAX = 1310720

Big.CHUNK_STRONG = 262144
Big.CHUNK_LITE = 524288

-- Flattening and opaque predicates scale with the largest single body, not the
-- file size: a 200 KB one-line dump can take minutes while 100 KB of ordinary
-- functions builds in seconds. Past these limits the VM, self-modifying
-- bytecode, anti-debug and integrity layers still run; only the two
-- source-level multipliers are dropped so the build stays interactive.
Big.FLATTEN_MAX = 131072
Big.DENSE_BYTES = 32768
Big.DENSE_LINES = 64

function Big.choose(size)
  if size < Big.MIN_SPLIT then return nil end
  local hard = size <= Big.HARD_MAX
  return {
    chunkBytes = hard and Big.CHUNK_STRONG or Big.CHUNK_LITE,
    flatten = hard,
    opaque = hard,
    strong = hard,
  }
end

function Big.header()
  -- Entry wall: same shape as a single-piece build, so the outer wrapper
  -- cannot be told apart from the artifact it carries.
  local names, seen = {}, { ["do"] = true, ["if"] = true, ["in"] = true, ["or"] = true }
  while #names < 34 + math.random(0, 8) do
    local name = string.char(math.random(97, 122))
    if math.random(1, 3) ~= 1 then
      name = name .. string.char(math.random(97, 122))
    end
    if not seen[name] then
      seen[name] = true
      names[#names + 1] = name
    end
  end
  Big._wall = names
  local list = table.concat(names, ",")
  -- Every environment primitive is optional on a locked-down executor: some
  -- hosts ship a getfenv that raises instead of a missing one, and setfenv may
  -- be absent entirely. A bare `getfenv()` here would kill every split build on
  -- those hosts before the first piece runs, so each lookup is type-checked and
  -- each call is made through pcall; when anything is unavailable the pieces
  -- simply run in the chunk environment.
  return "return(function(" .. list .. ",...)" .. names[#names] .. "={};" ..
    "return (function(...)\n" ..
    "local __tr=type local __pc=pcall\n" ..
    "local __E=nil local __src=_ENV\n" ..
    "if __tr(getfenv)==\"function\" then local __ok,__v=__pc(function() return getfenv(1) end) " ..
    "if __ok and __tr(__v)==\"table\" and __tr(__v.string)==\"table\" " ..
    "and __tr(__v.pcall)==\"function\" then __src=__v end end\n" ..
    "if __src==nil and __tr(getgenv)==\"function\" then local __ok,__v=__pc(getgenv) " ..
    "if __ok and __tr(__v)==\"table\" and __tr(__v.string)==\"table\" " ..
    "and __tr(__v.pcall)==\"function\" then __src=__v end end\n" ..
    "if __src==nil and __tr(_G)==\"table\" and __tr(_G.string)==\"table\" " ..
    "and __tr(_G.pcall)==\"function\" then __src=_G end\n" ..
    "if __src~=nil then local __ok,__t=__pc(setmetatable,{},{__index=__src})\n" ..
    "if __ok and __tr(__t)==\"table\" then __E=__t end end\n" ..
    "local _ENV=__E or __src\n" ..
    "local __P=function(f,...) return f(...) end\n"
end

function Big.footer()
  return "end)(...)end)(" .. table.concat(Big._wall or {}, ",") .. ",...)\n"
end

function Big.open()
  return "do local __f=function(...)\n"
end

function Big.close(last, returns)
  if last and returns then return "\nend return __P(__f,...) end\n" end
  return "\nend __P(__f,...) end\n"
end

function Big.seedFor(seed, index)
  return (seed + index * 2654435761 + 1013904223) % 4294967296
end

return Big
