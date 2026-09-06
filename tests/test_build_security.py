"""The static runtime is trusted only after checking a reviewed archive digest."""

import hashlib
import importlib.util
import io
import re
import tarfile
from pathlib import Path
from unittest.mock import Mock

import pytest

ROOT = Path(__file__).parents[1]
spec = importlib.util.spec_from_file_location("secure_build", ROOT / "webapp" / "build.py")
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)


def runtime_archive(names=None, extra=None):
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w:bz2") as archive:
        for name in build.PYODIDE_FILES if names is None else names:
            payload = f"verified runtime {name}".encode()
            member = tarfile.TarInfo(f"pyodide/{name}")
            member.size = len(payload)
            archive.addfile(member, io.BytesIO(payload))
        if extra:
            archive.addfile(extra, io.BytesIO(b""))
    return buffer.getvalue()


@pytest.fixture()
def dependency(monkeypatch, tmp_path):
    data = runtime_archive()
    vendor = tmp_path / "vendor"
    opener = Mock(side_effect=lambda *a, **kw: io.BytesIO(data))
    monkeypatch.setattr(build, "VENDOR", vendor)
    monkeypatch.setattr(build, "PYODIDE_SHA256", {"0.27.7": hashlib.sha256(data).hexdigest()})
    monkeypatch.setattr(build.urllib.request, "urlopen", opener)
    return vendor, opener, data


def test_verified_download_is_cached(dependency):
    vendor, opener, data = dependency
    target = build.fetch_pyodide("0.27.7")
    opener.assert_called_once_with(
        "https://github.com/pyodide/pyodide/releases/download/0.27.7/pyodide-core-0.27.7.tar.bz2",
        timeout=30,
    )
    assert (vendor / "pyodide-core-0.27.7.tar.bz2").read_bytes() == data
    assert all((target / name).read_bytes() == f"verified runtime {name}".encode()
               for name in build.PYODIDE_FILES)


def test_bad_download_never_creates_vendor(dependency):
    vendor, opener, _ = dependency
    opener.side_effect = lambda *a, **kw: io.BytesIO(b"tampered")
    with pytest.raises(SystemExit, match="checksum mismatch"):
        build.fetch_pyodide("0.27.7")
    assert not vendor.exists()


def test_bad_cached_archive_fails_closed_without_modifying_runtime(dependency):
    vendor, opener, _ = dependency
    target = build.fetch_pyodide("0.27.7")
    opener.reset_mock()
    before = {p.name: p.read_bytes() for p in target.iterdir()}
    (vendor / "pyodide-core-0.27.7.tar.bz2").write_bytes(b"tampered cache")
    with pytest.raises(SystemExit, match="checksum mismatch"):
        build.fetch_pyodide("0.27.7")
    opener.assert_not_called()
    assert before == {p.name: p.read_bytes() for p in target.iterdir()}


def test_loose_runtime_tampering_is_repaired_from_verified_cache(dependency):
    _, opener, _ = dependency
    target = build.fetch_pyodide("0.27.7")
    (target / "pyodide.js").write_bytes(b"tampered runtime")
    (target / "pyodide.asm.wasm").unlink()
    opener.reset_mock()
    assert build.fetch_pyodide("0.27.7") == target
    opener.assert_not_called()
    assert (target / "pyodide.js").read_bytes() == b"verified runtime pyodide.js"
    assert (target / "pyodide.asm.wasm").exists()


def test_legacy_loose_cache_is_not_trusted(dependency):
    vendor, opener, _ = dependency
    target = vendor / "pyodide-0.27.7"
    target.mkdir(parents=True)
    for name in build.PYODIDE_FILES:
        (target / name).write_bytes(b"unverified legacy cache")
    build.fetch_pyodide("0.27.7")
    opener.assert_called_once()
    assert (target / "pyodide.js").read_bytes() == b"verified runtime pyodide.js"


@pytest.mark.parametrize("version", ["latest", "99.0.0", "../../outside", "0.27.7/../../outside"])
def test_unreviewed_versions_fail_before_network_or_filesystem(dependency, version):
    vendor, opener, _ = dependency
    with pytest.raises(SystemExit, match="no reviewed Pyodide checksum"):
        build.fetch_pyodide(version)
    opener.assert_not_called()
    assert not vendor.exists()


@pytest.mark.parametrize("kind", ["missing", "duplicate", "symlink", "hardlink"])
def test_archive_must_contain_one_regular_copy_of_each_runtime_file(dependency, monkeypatch, kind):
    vendor, opener, _ = dependency
    if kind == "missing":
        data = runtime_archive(build.PYODIDE_FILES[:-1])
    else:
        member = tarfile.TarInfo("other/pyodide.js")
        if kind in ("symlink", "hardlink"):
            member.type = tarfile.SYMTYPE if kind == "symlink" else tarfile.LNKTYPE
            member.linkname = "../../outside"
        data = runtime_archive(extra=member)
    monkeypatch.setattr(build, "PYODIDE_SHA256", {"0.27.7": hashlib.sha256(data).hexdigest()})
    opener.side_effect = lambda *a, **kw: io.BytesIO(data)
    with pytest.raises(SystemExit, match="lacked expected|invalid or duplicate"):
        build.fetch_pyodide("0.27.7")
    assert not vendor.exists()


def test_download_size_is_bounded(dependency, monkeypatch):
    vendor, _, _ = dependency
    monkeypatch.setattr(build, "MAX_ARCHIVE_BYTES", 8)
    with pytest.raises(SystemExit, match="download size limit"):
        build.fetch_pyodide("0.27.7")
    assert not vendor.exists()


def test_extracted_size_is_bounded(dependency, monkeypatch):
    vendor, _, _ = dependency
    monkeypatch.setattr(build, "MAX_RUNTIME_BYTES", 1)
    with pytest.raises(SystemExit, match="extraction size limit"):
        build.fetch_pyodide("0.27.7")
    assert not vendor.exists()


def test_failed_dependency_verification_preserves_existing_dist(dependency, monkeypatch, tmp_path):
    _, opener, _ = dependency
    dist = tmp_path / "dist"
    dist.mkdir()
    (dist / "index.html").write_text("previous good build")
    monkeypatch.setattr(build, "DIST", dist)
    monkeypatch.setattr(build.sys, "argv", ["build.py"])
    opener.side_effect = lambda *a, **kw: io.BytesIO(b"bad download")
    with pytest.raises(SystemExit, match="checksum mismatch"):
        build.main()
    assert (dist / "index.html").read_text() == "previous good build"
    assert list(dist.iterdir()) == [dist / "index.html"]


def test_workflows_use_read_only_tokens_and_immutable_actions():
    for path in (ROOT / ".github" / "workflows").glob("*.yml"):
        workflow = path.read_text()
        assert "permissions:\n  contents: read\n" in workflow, path
        actions = re.findall(r"uses:\s*([^\s]+)", workflow)
        assert actions, path
        assert all(re.fullmatch(r"[\w./-]+@[0-9a-f]{40}", action) for action in actions), path
        assert workflow.count("persist-credentials: false") == sum(
            action.startswith("actions/checkout@") for action in actions
        ), path


def test_lean_installer_is_versioned_verified_and_not_piped_to_shell():
    workflow = (ROOT / ".github/workflows/state-law-check.yml").read_text()
    assert "elan/master/" not in workflow
    assert not re.search(r"\|\s*(?:ba)?sh(?:\s|$)", workflow)
    assert "sha256sum --check --strict" in workflow
    assert workflow.index("sha256sum --check --strict") < workflow.index("./elan-init")
    assert "--default-toolchain none" in workflow
    assert "set -euo pipefail" in workflow
    assert "permissions:\n  contents: read\n" in workflow
