"""Ephemeral certificates and opt-in trust for a disposable browser-test runner."""

import os
import shutil
import ssl
import subprocess
import sys
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path, PurePosixPath
from uuid import uuid4


def localhost_tls(directory: Path) -> tuple[ssl.SSLContext, Path]:
    """Issue a localhost server certificate from a fresh, short-lived test CA.

    The caller owns the temporary directory and must keep it alive until the
    server and browser have closed. Trust installation is a separate, explicitly
    opted-in operation; no certificate-error bypass is required.
    """
    ca, ca_key = directory / "ca.pem", directory / "ca-key.pem"
    cert, key, request = (
        directory / name for name in ("server.pem", "server-key.pem", "server.csr")
    )
    extensions = directory / "server.ext"
    extensions.write_text(
        "basicConstraints=critical,CA:FALSE\n"
        "keyUsage=critical,digitalSignature,keyEncipherment\n"
        "extendedKeyUsage=serverAuth\n"
        "subjectAltName=DNS:localhost,IP:127.0.0.1\n"
    )
    commands = (
        ["openssl", "req", "-x509", "-newkey", "rsa:2048", "-sha256", "-nodes",
         "-keyout", str(ca_key), "-out", str(ca), "-days", "1",
         "-subj", "/CN=DUPLOTRAIN ephemeral browser-test CA",
         "-addext", "basicConstraints=critical,CA:TRUE,pathlen:0",
         "-addext", "keyUsage=critical,keyCertSign,cRLSign"],
        ["openssl", "req", "-new", "-newkey", "rsa:2048", "-sha256", "-nodes",
         "-keyout", str(key), "-out", str(request), "-subj", "/CN=localhost"],
        ["openssl", "x509", "-req", "-in", str(request), "-CA", str(ca),
         "-CAkey", str(ca_key), "-set_serial", "1", "-out", str(cert),
         "-days", "1", "-sha256", "-extfile", str(extensions)],
    )
    for command in commands:
        subprocess.run(command, check=True, capture_output=True, timeout=30)
    for private_key in (ca_key, key):
        private_key.chmod(0o600)
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    context.minimum_version = ssl.TLSVersion.TLSv1_2
    context.load_cert_chain(cert, key)
    return context, ca


@contextmanager
def runner_test_ca(ca: Path) -> Iterator[None]:
    """Temporarily trust one CA only in an opted-in GitHub-hosted Linux runner.

    Release WebKit builds omit the developer-only CA-file environment override.
    Use the normal system trust database instead, then remove this unique anchor
    and rebuild the database even if installation, browser launch or testing fails.
    Never silently modify a developer machine or a persistent self-hosted runner.
    """
    if (os.environ.get("DUPLOTRAIN_TEST_SYSTEM_CA") != "1"
            or os.environ.get("RUNNER_ENVIRONMENT") != "github-hosted"
            or os.environ.get("GITHUB_ACTIONS") != "true"
            or sys.platform != "linux"):
        raise RuntimeError(
            "WebKit offline TLS testing requires an explicitly opted-in disposable "
            "GitHub-hosted Linux runner (DUPLOTRAIN_TEST_SYSTEM_CA=1). "
            "No certificates were installed."
        )
    programs = {name: shutil.which(name) for name in ("install", "rm", "update-ca-certificates")}
    if not all(programs.values()):
        raise RuntimeError("Disposable TLS test requires install, rm and update-ca-certificates")
    prefix = [] if os.geteuid() == 0 else ["sudo", "-n"]
    # A Linux trust-store path on every platform, so simulations match the runner.
    anchor = PurePosixPath("/usr/local/share/ca-certificates",
                           f"duplotrain-test-{uuid4().hex}.crt")
    if Path(anchor).exists():
        raise RuntimeError("Refusing to replace an existing test trust anchor")
    public_ca = ca.resolve(strict=True)

    def run(program: str, *args: str) -> None:
        subprocess.run([*prefix, programs[program], *args],
                       check=True, capture_output=True, timeout=60)

    try:
        # Install only the public CA, never a key or a certificate-error bypass.
        run("install", "-m", "0644", "--", str(public_ca), str(anchor))
        run("update-ca-certificates")
        yield
    finally:
        # No wildcard deletion: remove only the anchor owned by this invocation.
        try:
            run("rm", "-f", "--", str(anchor))
        finally:
            run("update-ca-certificates", "--fresh")
