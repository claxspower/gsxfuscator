-- artifact.lua -- centralized compilation and transport selection.
-- CLI and programmatic callers can inspect the exact bytes to be distributed.
local Obfuscate = require("src.obfuscate")
local Seal = require("src.seal")
local Minify = require("src.minify")
local Release = require("src.release")
local DeadStrings = require("src.deadstrings")
local Artifact = {}

function Artifact.build(source, opts)
  opts = opts or {}
  local result = Obfuscate.run(source, opts)
  if not result.ok then return result end
  local code, err = result.code, nil
  local direct = opts.noSeal == true
  if not direct then
    code, err = Seal.wrap(code, result.seed, {
      blockSize = opts.sealBlockSize,
      compression = opts.sealCompression,
      fragmentSize = opts.fragmentSize,
      fastLoad = true,
      showBanner = opts.showBanner,
      watermark = opts.watermark,
      coroutineWrapper = opts.coroutineWrapper == true,
    })
  end
  if direct and code then
    code, err = Minify.compact(code)
  end
  if direct and code then code = Release.brand(code) end
  if not code or code == "" then
    result.ok, result.stage, result.code = false, "seal", nil
    result.errors = { { msg = err or "empty artifact" } }
    return result
  end
  -- Inject 10,000 seeded mixed dead literals into the final
  -- delivered code (not into individual split/VM compiler passes).
  code = DeadStrings.inject(code, result.seed)
  -- Compiler-side syntax check; does not run in a direct-VM artifact.
  local loader = loadstring or load
  local chunk, syntaxErr = loader(code, "=GsXFuscator output")
  if not chunk then
    result.ok, result.stage, result.code = false, "emit", nil
    result.errors = { { msg = syntaxErr } }
    return result
  end
  result.code = code
  result.deliveryMode = direct and "direct-vm" or "sealed"
  if result.stats then result.stats.bytes = #code end
  return result
end

return Artifact
