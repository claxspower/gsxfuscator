"""Compile one JSON request received on stdin. The request contains source data only."""
import json
import secrets
import sys
from pathlib import Path
from urllib.parse import unquote

from lupa.lua54 import LuaRuntime

ROOT = Path(__file__).resolve().parents[1]
MAX_OUTPUT = 32 * 1024 * 1024
RULE_NAMES = ("flatten", "opaque", "selfmod", "antidebug", "integrity")


def decode_fields(value):
    if isinstance(value, str):
        return unquote(value)
    if isinstance(value, list):
        return [decode_fields(item) for item in value]
    if isinstance(value, dict):
        return {key: decode_fields(item) for key, item in value.items()}
    return value


def compile_source(request):
    lua = LuaRuntime(encoding=None, max_memory=256 * 1024 * 1024,
                     register_eval=False, register_builtins=False)
    env = lua.globals()
    preload = env[b"package"][b"preload"]
    for base, prefix in ((ROOT / "v2/src", "src."), (ROOT / "obfuscator/src", "v1.src.")):
        for path in base.glob("*.lua"):
            if path.stem in {"autofix", "verifier", "cli"}:
                continue
            name = (prefix + path.stem).encode()
            module = path.read_bytes()
            if prefix.startswith("v1."):
                module = module.replace(b'require("src.', b'require("v1.src.')
            preload[name] = lua.compile(module, name=b"@" + name, mode=b"t")
    lua.execute(b"""
        package.searchers = {package.searchers[1]}
        package.path, package.cpath, package.loadlib = "", "", nil
        python, io, debug, dofile, loadfile = nil, nil, nil, nil, nil
        os = {clock=os.clock, time=os.time}
        __PUSH = function(part) __piece = part end
    """)
    # The client never selects a Lua action, supplies Lua assignments, or starts verification.
    env[b"__ACTION"] = b"build"
    env[b"__SRC"] = request["source"].encode("utf-8")
    # Server-authoritative policy; public callers cannot choose weaker presets.
    env[b"__PRESET"] = b"strong"
    env[b"__SEED"] = secrets.randbits(32)
    env[b"__DELIVERY"] = request["delivery"].encode("ascii")
    env[b"__VM_SIZE"] = b"compact"
    env[b"__FAST_LOAD"] = 1
    for name in RULE_NAMES:
        env[("__" + name.upper()).encode()] = 1
    frame = lua.execute((ROOT / "web/v2driver.lua").read_bytes())
    status, size, rest = frame.split(b"\x01", 2)
    size = int(size)
    if rest[size:size + 1] != b"\x01":
        raise ValueError("Invalid compiler response")
    data = decode_fields(json.loads(rest[:size]))
    if status == b"CRASH":
        raise RuntimeError("Compilation failed")
    artifact = rest[size + 1:]
    if data.pop("streamed", False):
        artifact = env[b"__piece"] or b""
    if len(artifact) > MAX_OUTPUT:
        raise ValueError("Output exceeds the 32 MiB build limit")
    return {"status": status.decode("ascii"), "data": data, "code": artifact.decode("utf-8")}


if __name__ == "__main__":
    try:
        result = compile_source(json.load(sys.stdin.buffer))
        sys.stdout.buffer.write(json.dumps(result, ensure_ascii=False, separators=(",", ":")).encode())
    except MemoryError:
        sys.exit(3)
    except Exception:
        sys.exit(2)

