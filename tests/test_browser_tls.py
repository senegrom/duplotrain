"""The isolated browser-test CA must enable TLS trust, not disable validation."""

import os
import shutil
import socket
import ssl
import subprocess
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.error import URLError
from urllib.request import urlopen

import pytest

from tests.browser import tls as tls_helpers
from tests.browser.tls import localhost_tls, runner_test_ca


@pytest.mark.skipif(shutil.which("openssl") is None, reason="issuing the test CA needs openssl")
def test_browser_test_ca_is_explicit_and_checks_hostname(tmp_path):
    server_context, ca = localhost_tls(tmp_path)

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.end_headers()
            self.wfile.write(b"verified TLS")

        def log_message(self, *_args):
            pass

    server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    server.socket = server_context.wrap_socket(server.socket, server_side=True)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
        trusted = ssl.create_default_context(cafile=str(ca))
        trusted.minimum_version = ssl.TLSVersion.TLSv1_2
        assert trusted.check_hostname and trusted.verify_mode == ssl.CERT_REQUIRED
        url = f"https://localhost:{server.server_port}/"
        with urlopen(url, context=trusted, timeout=5) as response:
            assert response.read() == b"verified TLS"
        # A fresh database has no trust in this ephemeral CA.
        untrusted = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
        untrusted.minimum_version = ssl.TLSVersion.TLSv1_2
        with pytest.raises(URLError, match="CERTIFICATE_VERIFY_FAILED"):
            urlopen(url, context=untrusted, timeout=5)
        with socket.create_connection(server.server_address, timeout=5) as connection:
            with pytest.raises(ssl.SSLCertVerificationError, match="Hostname mismatch"):
                trusted.wrap_socket(connection, server_hostname="not-localhost.invalid")
        if os.name != "nt":  # Windows has no owner-only permission bits
            assert (tmp_path / "ca-key.pem").stat().st_mode & 0o777 == 0o600
            assert (tmp_path / "server-key.pem").stat().st_mode & 0o777 == 0o600
    finally:
        server.shutdown()
        thread.join(timeout=3)
        server.server_close()


@pytest.fixture
def simulated_runner(monkeypatch, tmp_path):
    """Never modify actual system trust in native unit tests, even when run in CI."""
    calls = []

    def run(command, **kwargs):
        assert kwargs == {"check": True, "capture_output": True, "timeout": 60}
        calls.append(command)
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(tls_helpers.subprocess, "run", run)
    monkeypatch.setattr(tls_helpers.shutil, "which", lambda name: f"/tools/{name}")
    monkeypatch.setattr(tls_helpers.os, "geteuid", lambda: 1000, raising=False)
    monkeypatch.setattr(tls_helpers.sys, "platform", "linux")
    monkeypatch.setenv("GITHUB_ACTIONS", "true")
    monkeypatch.setenv("RUNNER_ENVIRONMENT", "github-hosted")
    monkeypatch.setenv("DUPLOTRAIN_TEST_SYSTEM_CA", "1")
    ca = tmp_path / "public ca.pem"
    ca.write_text("public certificate fixture")
    return ca, calls


@pytest.mark.parametrize("key,value", [
    ("DUPLOTRAIN_TEST_SYSTEM_CA", "0"), ("DUPLOTRAIN_TEST_SYSTEM_CA", ""),
    ("RUNNER_ENVIRONMENT", "self-hosted"), ("GITHUB_ACTIONS", "false"),
])
def test_runner_ca_requires_explicit_disposable_runner(simulated_runner, monkeypatch, key, value):
    ca, calls = simulated_runner
    monkeypatch.setenv(key, value)
    with pytest.raises(RuntimeError, match="explicitly opted-in disposable"):
        with runner_test_ca(ca):
            pytest.fail("trust guard did not run")
    assert calls == []


def test_runner_ca_rejects_unsupported_platform_or_missing_tools(simulated_runner, monkeypatch):
    ca, calls = simulated_runner
    monkeypatch.setattr(tls_helpers.sys, "platform", "darwin")
    with pytest.raises(RuntimeError, match="explicitly opted-in disposable"):
        with runner_test_ca(ca):
            pass
    monkeypatch.setattr(tls_helpers.sys, "platform", "linux")
    monkeypatch.setattr(tls_helpers.shutil, "which", lambda _: None)
    with pytest.raises(RuntimeError, match="requires install, rm"):
        with runner_test_ca(ca):
            pass
    assert calls == []


@pytest.mark.parametrize("fails", [False, True])
def test_runner_ca_scopes_trust_and_cleans_up_after_test_error(simulated_runner, fails):
    ca, calls = simulated_runner

    def exercise():
        with runner_test_ca(ca):
            assert len(calls) == 2
            if fails:
                raise ValueError("browser failed")

    if fails:
        with pytest.raises(ValueError, match="browser failed"):
            exercise()
    else:
        exercise()
    assert len(calls) == 4
    anchor = calls[0][-1]
    assert anchor.startswith("/usr/local/share/ca-certificates/duplotrain-test-")
    assert anchor.endswith(".crt") and "*" not in anchor
    assert calls[0] == ["sudo", "-n", "/tools/install", "-m", "0644", "--",
                        str(ca.resolve()), anchor]
    assert calls[1] == ["sudo", "-n", "/tools/update-ca-certificates"]
    assert calls[2] == ["sudo", "-n", "/tools/rm", "-f", "--", anchor]
    assert calls[3] == ["sudo", "-n", "/tools/update-ca-certificates", "--fresh"]
    assert ca.read_text() == "public certificate fixture"


@pytest.mark.parametrize("failure_at", [1, 2, 3])
def test_runner_ca_refreshes_trust_even_when_setup_or_removal_fails(
    simulated_runner, monkeypatch, failure_at,
):
    ca, calls = simulated_runner
    original = tls_helpers.subprocess.run

    def failing(command, **kwargs):
        original(command, **kwargs)
        if len(calls) == failure_at:
            raise subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(tls_helpers.subprocess, "run", failing)
    with pytest.raises(subprocess.CalledProcessError):
        with runner_test_ca(ca):
            assert failure_at == 3
    assert calls[-1] == ["sudo", "-n", "/tools/update-ca-certificates", "--fresh"]
    assert any(command[2] == "/tools/rm" and command[-1] == calls[0][-1] for command in calls)


def test_runner_ca_uses_distinct_anchors_and_no_sudo_for_root(simulated_runner, monkeypatch):
    ca, calls = simulated_runner
    monkeypatch.setattr(tls_helpers.os, "geteuid", lambda: 0, raising=False)
    for _ in range(2):
        with runner_test_ca(ca):
            pass
    assert calls[0][0] == calls[4][0] == "/tools/install"
    assert calls[0][-1] != calls[4][-1]
    assert calls[2][-1] == calls[0][-1]
    assert calls[6][-1] == calls[4][-1]
