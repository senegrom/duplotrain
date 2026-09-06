"""Security regressions over real sockets, without browser/CORS assumptions."""

import http.client
import json
import socket
import threading

import pytest

from duplotrain.gui import Session, make_server
from duplotrain.validation import MAX_JSON_BYTES


@pytest.fixture()
def local_editor():
    session = Session()
    session.attach("straight", 0, None)
    server = make_server(session, port=0)
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.01})
    thread.start()
    try:
        yield session, server.server_port
    finally:
        server.shutdown()
        server.server_close()
        thread.join()


def request(port, method="POST", path="/api/clear", headers=None, body=b"{}", half_close=False):
    if headers is None:
        headers = [("Host", f"127.0.0.1:{port}"), ("Content-Type", "application/json")]
    conn = http.client.HTTPConnection("127.0.0.1", port, timeout=3)
    try:
        conn.putrequest(method, path, skip_host=True, skip_accept_encoding=True)
        for name, value in headers:
            conn.putheader(name, value)
        if not any(name.lower() == "content-length" for name, _ in headers):
            conn.putheader("Content-Length", str(len(body)))
        conn.endheaders(body)
        # Also makes a deliberately truncated request return EOF, not hang.
        if half_close:
            conn.sock.shutdown(socket.SHUT_WR)
        response = conn.getresponse()
        payload = response.read()
        if response.getheader("Content-Type") == "application/json":
            payload = json.loads(payload)
        return response.status, dict(response.getheaders()), payload
    finally:
        conn.close()


def assert_rejected(local_editor, expected, **kwargs):
    session, port = local_editor
    before = session.state()
    status, headers, payload = request(port, **kwargs)
    assert status == expected
    assert "error" in payload
    assert "Access-Control-Allow-Origin" not in headers
    assert session.state() == before


@pytest.mark.parametrize("origin", [
    "https://attacker.invalid", "null", "http://127.0.0.1:1",
    "https://127.0.0.1:{port}", "http://localhost:{port}",
    "http://127.0.0.1:{port}.attacker.invalid", "http://127.0.0.1:{port}/",
    "http://127.0.0.1:{port} https://attacker.invalid",
])
def test_foreign_or_malformed_origins_cannot_clear(local_editor, origin):
    _, port = local_editor
    assert_rejected(local_editor, 403, headers=[
        ("Host", f"127.0.0.1:{port}"),
        ("Content-Type", "application/json"),
        ("Origin", origin.format(port=port)),
    ])


@pytest.mark.parametrize("media_type", [
    None, "text/plain", "application/x-www-form-urlencoded", "multipart/form-data",
    "application/jsonp", "text/plain; application/json", "",
])
@pytest.mark.parametrize("body", [b"{}", b""])
def test_simple_or_missing_content_type_cannot_clear(local_editor, media_type, body):
    _, port = local_editor
    headers = [("Host", f"127.0.0.1:{port}")]
    if media_type is not None:
        headers.append(("Content-Type", media_type))
    assert_rejected(local_editor, 415, headers=headers, body=body)


@pytest.mark.parametrize("host", [
    None, "attacker.invalid:{port}", "127.0.0.1.attacker.invalid:{port}",
    "127.0.0.1:1", "127.0.0.1", "127.1:{port}", "2130706433:{port}",
    "localhost.attacker.invalid:{port}", "attacker@127.0.0.1:{port}",
    "127.0.0.1:{port}/", "[::1]:{port}",
])
@pytest.mark.parametrize("method,path", [("GET", "/api/state"), ("POST", "/api/clear")])
def test_dns_rebinding_and_invalid_hosts_are_rejected(local_editor, host, method, path):
    _, port = local_editor
    headers = [("Content-Type", "application/json")]
    if host is not None:
        headers.append(("Host", host.format(port=port)))
    # Forwarded headers must not be a way around the actual Host validation.
    headers.append(("X-Forwarded-Host", f"127.0.0.1:{port}"))
    assert_rejected(local_editor, 403, method=method, path=path, headers=headers)


@pytest.mark.parametrize("name,value,status", [
    ("Host", "127.0.0.1:{port}", 403),
    ("Origin", "http://127.0.0.1:{port}", 403),
    ("Content-Type", "application/json", 415),
    ("Content-Length", "2", 409),
    ("Sec-Fetch-Site", "same-origin", 403),
])
def test_duplicate_security_headers_fail_closed(local_editor, name, value, status):
    _, port = local_editor
    headers = [
        ("Host", f"127.0.0.1:{port}"), ("Content-Type", "application/json"),
        ("Origin", f"http://127.0.0.1:{port}"), ("Content-Length", "2"),
        ("Sec-Fetch-Site", "same-origin"), (name, value.format(port=port)),
    ]
    assert_rejected(local_editor, status, headers=headers)


@pytest.mark.parametrize("site", ["cross-site", "same-site", "invalid"])
def test_fetch_metadata_is_checked_without_origin(local_editor, site):
    _, port = local_editor
    assert_rejected(local_editor, 403, headers=[
        ("Host", f"127.0.0.1:{port}"), ("Content-Type", "application/json"),
        ("Sec-Fetch-Site", site),
    ])


@pytest.mark.parametrize("host", ["127.0.0.1", "localhost"])
@pytest.mark.parametrize("browser_headers", [False, True])
def test_same_origin_and_non_browser_json_clients_work(local_editor, host, browser_headers):
    session, port = local_editor
    headers = [("Host", f"{host}:{port}"), ("Content-Type", "application/json; charset=utf-8")]
    if browser_headers:
        headers += [("Origin", f"http://{host}:{port}"), ("Sec-Fetch-Site", "same-origin")]
    assert request(port, headers=headers)[0] == 200
    assert not session.layout.placements


@pytest.mark.parametrize("path", [
    "/api/clear", "/api/undo", "/api/inventory", "/api/import", "/api/restore",
    "/api/attach", "/api/remove", "/api/solve", "/api/apply", "/api/stone",
    "/api/join", "/api/unlimited", "/api/add_set",
])
def test_every_mutation_is_guarded_before_dispatch(local_editor, path):
    _, port = local_editor
    assert_rejected(local_editor, 403, path=path, headers=[
        ("Host", f"127.0.0.1:{port}"), ("Content-Type", "application/json"),
        ("Origin", "https://attacker.invalid"),
    ])


@pytest.mark.parametrize("length", ["-1", "+2", "two", "2, 2", str(MAX_JSON_BYTES + 1), "9" * 20])
def test_invalid_lengths_cannot_mutate(local_editor, length):
    _, port = local_editor
    assert_rejected(local_editor, 409, headers=[
        ("Host", f"127.0.0.1:{port}"), ("Content-Type", "application/json"),
        ("Content-Length", length),
    ])


def test_truncated_body_cannot_mutate(local_editor):
    _, port = local_editor
    assert_rejected(local_editor, 409, half_close=True, headers=[
        ("Host", f"127.0.0.1:{port}"), ("Content-Type", "application/json"),
        ("Content-Length", "100"),
    ])


def test_chunked_requests_are_not_silently_treated_as_empty(local_editor):
    _, port = local_editor
    assert_rejected(local_editor, 409, headers=[
        ("Host", f"127.0.0.1:{port}"), ("Content-Type", "application/json"),
        ("Transfer-Encoding", "chunked"),
    ])


@pytest.mark.parametrize("body", [b"not json", b"\xff", b"[" * 2000 + b"]" * 2000])
def test_malformed_or_deep_json_does_not_crash_or_mutate(local_editor, body):
    assert_rejected(local_editor, 409, body=body)


def test_cors_preflight_never_grants_access(local_editor):
    assert_rejected(local_editor, 403, method="OPTIONS")


def test_response_headers_prevent_embedding_and_sniffing(local_editor):
    _, port = local_editor
    for path in ("/", "/api/state"):
        status, headers, _ = request(port, method="GET", path=path)
        assert status == 200
        assert headers["X-Content-Type-Options"] == "nosniff"
        assert headers["X-Frame-Options"] == "DENY"
        assert headers["Content-Security-Policy"] == "frame-ancestors 'none'"
        assert headers["Cross-Origin-Resource-Policy"] == "same-origin"
        assert headers["Cache-Control"] == "no-store"
        assert "Access-Control-Allow-Origin" not in headers


def test_get_cannot_mutate(local_editor):
    assert_rejected(local_editor, 404, method="GET")
