-- clax_alert.lua -- bounded incident response for verified integrity failures.
-- The warning is diagnostic/branding only; no client-side warning prevents
-- reverse engineering. Runtime probes must not call this for mere debugger
-- presence, to avoid false-positive output spam in legitimate environments.
local Alert = {}
Alert.MESSAGE = "GsxFuscator İs The Best Fuck Your Deobfuscator Or Dumper Bot :) Bye Have A Bad Day."
Alert.COUNT = 256
local function literal(s) return string.format('%q', s) end

-- Emit a self-contained Lua 5.1+/Luau closure. It never uses globals until an
-- actual verified integrity trip and it stops permanently after the first trip.
-- Roblox/Luau uses warn; PUC Lua 5.4's warn stream may be disabled by the
-- launcher, so other PUC runtimes use print for a visible fallback.
function Alert.emit(name, reportName)
  assert(type(name) == 'string' and name:match('^[_%a][_%w]*$'), 'bad name')
  if reportName ~= nil then
    assert(type(reportName) == 'string' and reportName:match('^[_%a][_%w]*$'), 'bad reporter')
  end
  local report = reportName or '_clax_report'
  local body = 'local '..report..'=(function() local _sent=false ' ..
    'local _msg='..literal(Alert.MESSAGE)..' ' ..
    'local _log=(type(warn)=="function" and warn) or ' ..
    '(type(print)=="function" and print) ' ..
    'return function() if _sent then return end _sent=true ' ..
    'if _log then for _i=1,'..Alert.COUNT..' do pcall(_log,_msg) end end ' ..
    'end end)() '
  return body .. 'local ' .. name .. '=function() ' .. report .. '() ' ..
    'error("runtime verification failed",0) end; '
end

return Alert
