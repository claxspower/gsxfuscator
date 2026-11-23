-- Output minifier for generated Lua; no newline or banner is emitted.
-- Token-aware emission preserves string bytes and syntax separators.
local Lex = require('src.lexer')
local M={}
local function quote(s)
 local out={'"'}
 for i=1,#s do
  local b=s:byte(i)
  if b==34 then out[#out+1]='\\"'
  elseif b==92 then out[#out+1]='\\\\'
  elseif b==10 then out[#out+1]='\\n'
  elseif b==13 then out[#out+1]='\\r'
  elseif b==9 then out[#out+1]='\\t'
  elseif b<32 or b>=127 then out[#out+1]=string.format('\\%03d',b)
  else out[#out+1]=string.char(b) end
 end
 out[#out+1]='"'
 return table.concat(out)
end
function M.compact(src)
 local ts,errors=Lex.lex(src)
 if #errors>0 then return nil,errors[1].msg end
 local out,last,wasNumber={},'',false
 for i=1,#ts do
  local t=ts[i]
  if t.t=='eof' then break end
  local v=t.t=='string' and quote(t.v) or t.raw or t.v
  if type(v)~='string' then return nil,'missing token text' end
  local first=v:sub(1,1)
  local sep=(last:match('[%w_]') and first:match('[%w_]')) or
    (last=='-' and first=='-') or
    (last=='.' and (first=='.' or first:match('%d'))) or
    (wasNumber and first=='.') or
    (last==':' and first==':') or
    (last=='<' and first=='<') or
    (last=='>' and first=='>') or
    (last=='/' and first=='/')
  if sep then out[#out+1]=' ' end
  out[#out+1]=v
  last=v:sub(-1)
  wasNumber=t.t=='number'
 end
 local result=table.concat(out)
 if result:find('[\r\n]') then return nil,'minifier emitted newline' end
 return result
end
return M
