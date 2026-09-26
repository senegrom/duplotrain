"""Local HTTP host for the shared track editor.

``duplotrain gui`` serves the packaged HTML, JavaScript and icons on loopback.
It re-exports ``Session`` and ``dispatch_session`` for desktop callers; the
browser worker imports :mod:`duplotrain.editor`.
"""

from __future__ import annotations

import json
import socket
import sys
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from importlib import resources
from time import monotonic
from typing import Any

from .editor import RevisionConflictError, UnknownRouteError
from .editor import Session as Session
from .editor import dispatch_session as dispatch_session
from .validation import MAX_JSON_BYTES, check_json_depth

__all__ = ["Session", "make_server", "run"]

# Only these packaged assets are HTTP routes; never resolve arbitrary request
# paths against the filesystem. Keep icon URLs shared with the static build.
_EDITOR_ASSETS = {
    **{f"/{name}": "text/javascript; charset=utf-8" for name in (
        "editor.js", "editor-geometry.js", "editor-projects.js", "editor-train.js",
        "editor-search.js", "editor-offline.js",
    )},
    "/editor.css": "text/css; charset=utf-8",
    "/manifest.webmanifest": "application/manifest+json",
    "/favicon.ico": "image/x-icon",
    "/apple-touch-icon.png": "image/png",
    "/icons/duplotrain-favicon-v1.ico": "image/x-icon",
    **{
        f"/icons/duplotrain-{name}-v1.png": "image/png"
        for name in (
            "tab-16", "tab-32", "apple-152", "apple-167", "apple-180",
            "app-192", "app-512", "maskable-512",
        )
    },
}


def _handler_for(session: Session) -> type[BaseHTTPRequestHandler]:
    class Handler(BaseHTTPRequestHandler):
        BODY_SECONDS = 10.0

        def setup(self) -> None:
            super().setup()
            self.connection.settimeout(self.BODY_SECONDS)

        def log_message(self, fmt: str, *args: Any) -> None:  # quiet
            pass

        def end_headers(self) -> None:
            # Every response, http.server's own error pages included.
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("X-Frame-Options", "DENY")
            self.send_header("Content-Security-Policy", "frame-ancestors 'none'")
            self.send_header("Cross-Origin-Resource-Policy", "same-origin")
            super().end_headers()

        def _send(self, status: int, payload: bytes, content_type: str) -> None:
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(payload)))
            try:
                self.end_headers()
                self.wfile.write(payload)
            except OSError:
                # The client stopped reading (the write timed out) or went away.
                # Part of this response may be on the wire, so nothing may follow
                # it, least of all an error for a request the session applied.
                self.close_connection = True

        def _json(self, status: int, data: Any) -> None:
            payload = json.dumps(data, separators=(",", ":")).encode("utf-8")
            self._send(status, payload, "application/json")

        #: Discard at most this much of a rejected body, for at most this long.
        DRAIN_BYTES = 64 * 1024
        DRAIN_SECONDS = 0.25

        def _drain_body(self) -> None:
            """Discard a rejected request's body before the connection closes.

            Closing a socket that still holds unread bytes is an abortive close,
            and the reset discards the response written before it, so the
            client reports a connection error instead of reading the refusal.

            Never wait on a body that was promised but not sent: a declared
            length is not evidence that the bytes are coming, so the drain is
            bounded in both size and time and gives up rather than blocking.
            """
            lengths = self.headers.get_all("Content-Length", [])
            if self.headers.get_all("Transfer-Encoding") or len(lengths) != 1:
                return
            raw = lengths[0]
            if not (raw.isascii() and raw.isdigit() and len(raw) <= 10):
                return
            if getattr(self, "_body_read_failed", False):
                return  # A timed-out buffered socket is no longer readable.
            remaining = min(
                max(0, int(raw) - getattr(self, "_body_bytes_read", 0)), self.DRAIN_BYTES
            )
            if not remaining:
                return
            previous = self.connection.gettimeout()
            deadline = monotonic() + self.DRAIN_SECONDS
            try:
                while remaining > 0:
                    time_left = deadline - monotonic()
                    if time_left <= 0:
                        return
                    self.connection.settimeout(time_left)
                    # read() can perform many raw reads as bytes trickle in.
                    # read1() returns after at most one, letting us recheck time.
                    chunk = self.rfile.read1(min(remaining, 4096))
                    if not chunk:
                        return
                    remaining -= len(chunk)
            except OSError:
                return
            finally:
                try:
                    self.connection.settimeout(previous)
                except OSError:
                    pass

        def _reject(self, status: int, message: str) -> bool:
            # Do not reuse a connection with an unread, rejected request body.
            self._drain_body()
            self.close_connection = True
            self._json(status, {"error": message})
            return False

        #: After the response, discard at most this much input for at most this
        #: long while waiting for the client to close.
        LINGER_BYTES = 64 * 1024
        LINGER_SECONDS = 0.5

        def finish(self) -> None:
            """Close gracefully, whatever the request's framing was.

            A close with unread input, or input arriving after the close, resets
            the connection, and on Windows the reset discards a response the
            client has not read yet. The drain above only helps when one valid
            length says how much to expect: it cannot cover a chunked request,
            repeated or malformed lengths, or a body sent with a successful GET.
            So every connection ends the same way: flush the response, send FIN,
            then discard input until the client closes, bounded in size and time.
            A client that has read its response closes at once.
            """
            try:
                self.wfile.flush()
                self.connection.shutdown(socket.SHUT_WR)
                deadline = monotonic() + self.LINGER_SECONDS
                remaining = self.LINGER_BYTES
                while remaining > 0:
                    time_left = deadline - monotonic()
                    if time_left <= 0:
                        break
                    self.connection.settimeout(time_left)
                    chunk = self.connection.recv(min(remaining, 4096))
                    if not chunk:
                        break
                    remaining -= len(chunk)
            except OSError:
                pass
            super().finish()

        def _trusted_request(self) -> bool:
            # Binding to loopback alone does not stop CSRF or DNS rebinding.
            # Compare authorities literally: no suffix matching, DNS resolution,
            # forwarded headers, userinfo, alternative IP spellings or other ports.
            port = self.server.server_port
            allowed_hosts = {f"127.0.0.1:{port}", f"localhost:{port}"}
            if port == 80:
                allowed_hosts.update({"127.0.0.1", "localhost"})
            hosts = self.headers.get_all("Host", [])
            if len(hosts) != 1 or hosts[0].lower() not in allowed_hosts:
                return self._reject(403, "invalid local editor host")
            origins = self.headers.get_all("Origin", [])
            if origins and (len(origins) != 1 or origins[0] != f"http://{hosts[0].lower()}"):
                return self._reject(403, "cross-origin editor request forbidden")
            sites = self.headers.get_all("Sec-Fetch-Site", [])
            if (self.command == "POST" or self.path.startswith("/api/")) and sites:
                if len(sites) != 1 or sites[0] not in ("same-origin", "none"):
                    return self._reject(403, "cross-site editor request forbidden")
            # Non-browser local clients need not send Origin/Fetch Metadata.
            # Requiring non-simple JSON even for an empty POST closes the browser
            # fallback: HTML forms/no-cors fetch cannot send it without preflight.
            # We deliberately never grant CORS/preflight access.
            if self.command == "POST":
                types = self.headers.get_all("Content-Type", [])
                if len(types) != 1 or types[0].split(";", 1)[0].strip().lower() != (
                    "application/json"
                ):
                    return self._reject(415, "editor requests require application/json")
            return True

        def _body(self) -> dict[str, Any]:
            lengths = self.headers.get_all("Content-Length", [])
            if self.headers.get_all("Transfer-Encoding") or len(lengths) > 1:
                raise ValueError("unsupported or ambiguous request framing")
            raw_length = lengths[0] if lengths else "0"
            if not (raw_length.isascii() and raw_length.isdigit() and len(raw_length) <= 10):
                raise ValueError("invalid request length")
            length = int(raw_length)
            if length > MAX_JSON_BYTES:
                raise ValueError("request body larger than 2 MB")
            if not length:
                return {}
            payload = bytearray()
            previous = self.connection.gettimeout()
            deadline = monotonic() + self.BODY_SECONDS
            try:
                while len(payload) < length:
                    time_left = deadline - monotonic()
                    if time_left <= 0:
                        raise TimeoutError("request body timed out")
                    self.connection.settimeout(time_left)
                    chunk = self.rfile.read1(min(length - len(payload), 64 * 1024))
                    if not chunk:
                        raise ValueError("incomplete request body")
                    payload.extend(chunk)
                    self._body_bytes_read = len(payload)
            except OSError:
                self._body_read_failed = True
                raise
            finally:
                self.connection.settimeout(previous)
            text = payload.decode("utf-8")
            check_json_depth(text)
            return json.loads(text)

        def do_GET(self) -> None:  # noqa: N802 (http.server API)
            if not self._trusted_request():
                return
            if self.path in ("/", "/index.html"):
                html = resources.files("duplotrain").joinpath("static/editor.html")
                self._send(200, html.read_bytes(), "text/html; charset=utf-8")
            elif content_type := _EDITOR_ASSETS.get(self.path.split("?", 1)[0]):
                path = self.path.split("?", 1)[0]
                asset = resources.files("duplotrain").joinpath("static" + path)
                self._send(200, asset.read_bytes(), content_type)
            elif self.path in ("/api/state", "/api/export"):
                # A client slow to read must not hold the session lock.
                with session.lock:
                    result = dispatch_session(session, self.path, {})
                self._json(200, result)
            else:
                # A GET carrying a body (a mutation attempt) must be drained like
                # any other rejected request, or the close resets the connection
                # and the client never reads this refusal.
                self._reject(404, f"no route {self.path}")

        def do_POST(self) -> None:  # noqa: N802
            self._body_bytes_read = 0
            self._body_read_failed = False
            if not self._trusted_request():
                return
            try:
                body = self._body()
                with session.lock:
                    result = dispatch_session(session, self.path, body)
                self._json(200, result)
            except RevisionConflictError as exc:
                # The comparison above happened under the same lock as edits.
                # Return current state, but never replay the rejected mutation.
                # dispatch_session validated the body and its preview format first.
                with session.lock:
                    current = session.state(preview_format=body.get("preview_format"))
                self._json(409, {"error": str(exc), "code": "stale_revision", "state": current})
            except UnknownRouteError as exc:
                self._json(404, {"error": str(exc)})
            except TimeoutError:
                self._reject(408, "request body timed out")
            except (
                ValueError, KeyError, TypeError, IndexError, OverflowError, RecursionError
            ) as exc:
                self._reject(409, str(exc))

        def do_OPTIONS(self) -> None:  # noqa: N802
            self._reject(403, "cross-origin editor access is not enabled")

    return Handler


class _EditorServer(ThreadingHTTPServer):
    # On Windows SO_REUSEADDR lets a second editor bind a port that is still
    # listening and silently split its requests; a restart rebinds without it.
    allow_reuse_address = sys.platform != "win32"


def make_server(session: Session, port: int = 8137) -> ThreadingHTTPServer:
    """Build (but do not start) the editor server; port 0 picks a free port."""
    return _EditorServer(("127.0.0.1", port), _handler_for(session))


def run(port: int = 8137, open_browser: bool = True) -> None:
    """Serve the editor until interrupted."""
    session = Session()
    server = make_server(session, port)
    url = f"http://127.0.0.1:{server.server_port}/"
    print(f"duplotrain editor at {url}  (Ctrl+C to stop)")
    if open_browser:
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
