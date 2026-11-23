"""Serve the local dashboard or run the authenticated compiler behind an HTTPS proxy."""
import argparse
import hmac
import json
import os
import socket
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlsplit
from urllib.request import urlopen
import webbrowser

WEB = Path(__file__).resolve().parent
INDEX = WEB.parent / "public" / "index.html"
COMPILER_WORKER = WEB.parent / "public" / "compiler-worker.js"
MAX_BODY = 64 * 1024 * 1024  # JSON transport overhead, not the source file limit
MAX_SOURCE = 10 * 1024 * 1024  # 10 MiB UTF-8 source
RULES = {"flatten", "opaque", "selfmod", "antidebug", "integrity"}
LOOPBACK = {"localhost", "127.0.0.1", "::1"}


class Server(ThreadingHTTPServer):
    allow_reuse_address = os.name != "nt"
    connections = threading.BoundedSemaphore(24)
    builds = threading.BoundedSemaphore(2)

    def server_bind(self):
        if os.name == "nt":
            self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_EXCLUSIVEADDRUSE, 1)
        super().server_bind()

    def get_request(self):
        connection, address = super().get_request()
        connection.settimeout(15)
        return connection, address

    def process_request(self, request, address):
        if not self.connections.acquire(blocking=False):
            self.shutdown_request(request)
            return
        try:
            super().process_request(request, address)
        except Exception:
            self.connections.release()
            raise

    def process_request_thread(self, request, address):
        try:
            super().process_request_thread(request, address)
        finally:
            self.connections.release()


class Handler(BaseHTTPRequestHandler):
    server_version = "GsXFuscator"
    sys_version = ""

    def log_request(self, code="-", size="-"):
        # Keep server access logs minimal.
        self.log_message("%s %s", self.command, code)

    def reply(self, status, body, content_type="application/json; charset=utf-8"):
        if isinstance(body, dict):
            body = json.dumps(body).encode()
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        self.send_header("X-Frame-Options", "SAMEORIGIN")
        self.send_header("Content-Security-Policy", "frame-ancestors 'self'")
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def error(self, status, text):
        self.reply(status, {"error": text})

    def check_local(self):
        host = self.headers.get("Host", "")
        try:
            parsed = urlsplit("//" + host)
            valid = (parsed.hostname in LOOPBACK and not parsed.username and not parsed.password
                     and not parsed.path and parsed.port == self.server.server_port)
            # A browser omits the port in Host when using default HTTP.
            if self.server.server_port == 80:
                valid = host in LOOPBACK or valid
        except ValueError:
            valid = False
        origin = self.headers.get("Origin")
        if not valid or (origin and origin != "http://" + host):
            self.error(403, "This service accepts local, same-origin requests.")
            return False
        return True

    def dispatch(self):
        path = urlsplit(self.path).path
        if self.server.local:
            if not self.check_local():
                return
            if path in {"/", "/index.html"} and self.command in {"GET", "HEAD"}:
                if INDEX.is_file():
                    self.reply(200, INDEX.read_bytes(), "text/html; charset=utf-8")
                else:
                    self.error(503, "Build the dashboard with python web/build12.py.")
                return
            if path == "/compiler-worker.js" and self.command in {"GET", "HEAD"}:
                if COMPILER_WORKER.is_file():
                    self.reply(200, COMPILER_WORKER.read_bytes(), "application/javascript; charset=utf-8")
                else:
                    self.error(503, "Rebuild the dashboard with python web/build12.py.")
                return
        if path != "/api/build":
            self.error(404, "Page not found.")
            return
        if self.command != "POST":
            self.error(405, "Use POST for builds.")
            return
        if not self.server.local:
            auth = self.headers.get("Authorization", "").encode()
            if not hmac.compare_digest(auth, self.server.authorization):
                self.error(403, "Access denied.")
                return
        if self.headers.get_content_type() != "application/json":
            self.error(415, "Send the request as JSON.")
            return
        try:
            length = int(self.headers.get("Content-Length", "-1"))
        except ValueError:
            length = -1
        if length < 0:
            self.error(411, "A content length is required.")
            return
        if length > MAX_BODY:
            self.error(413, "The build request exceeds 64 MiB.")
            return
        if not self.server.builds.acquire(blocking=False):
            self.error(429, "Both build slots are busy. Try again shortly.")
            return
        try:
            body = self.rfile.read(length)
            if len(body) != length:
                self.error(400, "Incomplete build request.")
                return
            try:
                job = json.loads(body.decode("utf-8"))
                validate(job)
            except (ValueError, RecursionError, UnicodeError) as exc:
                self.error(400, str(exc) if type(exc) is ValueError else "Invalid build request.")
                return
            # No secret or uploaded source goes on a command line, into a file, or into logs.
            environment = {key: os.environ[key] for key in ("PATH", "SYSTEMROOT", "WINDIR",
                "TEMP", "TMP", "TMPDIR", "LANG") if key in os.environ}
            # Do not impose an application-level compilation deadline.
            # Resource limits and infrastructure timeouts may still apply.
            result = subprocess.run([sys.executable, str(WEB / "compile_job.py")],
                input=body, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                env=environment, check=False)
            if result.returncode:
                self.error(422, "This build exceeded its memory budget." if result.returncode == 3
                           else "The private compiler could not complete this build.")
                return
            self.reply(200, result.stdout)
        finally:
            self.server.builds.release()

    do_GET = do_HEAD = do_POST = dispatch


def validate(job):
    if not isinstance(job, dict) or set(job) != {"source", "delivery"}:
        raise ValueError("The build request must contain only source and delivery.")
    source = job.get("source")
    if not isinstance(source, str) or not source.strip():
        raise ValueError("Provide nonempty Lua source.")
    if len(source.encode("utf-8")) > MAX_SOURCE:
        raise ValueError("The source exceeds 10 MiB.")
    if job["delivery"] not in ("sealed", "direct-vm"):
        raise ValueError("Unknown delivery mode.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8787)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--origin", action="store_true", help="Serve only the authenticated compiler endpoint")
    parser.add_argument("--open", action="store_true", help="Open the local dashboard in your browser")
    args = parser.parse_args()
    secret = (os.environ.get("GSX_BUILD_TOKEN") or os.environ.get("CLAX_BUILD_TOKEN", ""))
    if args.origin and len(secret) < 32:
        parser.error("Origin mode requires a GSX_BUILD_TOKEN (legacy CLAX_BUILD_TOKEN also accepted) of at least 32 characters.")
    if not args.origin and args.host not in {"127.0.0.1", "localhost"}:
        parser.error("Local mode binds to the loopback interface. Use --origin for hosting.")
    if args.origin and args.open:
        parser.error("--open is available for the local dashboard.")
    try:
        listener = Server((args.host, args.port), Handler)
    except OSError as exc:
        if args.open:
            address = f"http://{args.host}:{args.port}/"
            try:
                with urlopen(address, timeout=2) as existing:
                    if existing.headers.get("Server", "").strip() == Handler.server_version:
                        webbrowser.open(address)
                        return
            except OSError:
                pass
        parser.exit(1, f"Could not start the dashboard on port {args.port}: {exc}\n")
    with listener as server:
        server.local = not args.origin
        server.authorization = ("Bearer " + secret).encode()
        print(f"GsXFuscator {'compiler origin' if args.origin else 'dashboard'} at http://{args.host}:{server.server_port}", flush=True)
        if args.open:
            webbrowser.open(f"http://{args.host}:{server.server_port}/")
        server.serve_forever()


if __name__ == "__main__":
    main()

