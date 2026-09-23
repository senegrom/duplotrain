"""The offline manifest binds every executable/runtime asset to one content build."""
import hashlib
import json
import re
from pathlib import Path
from urllib.parse import urlsplit

from tests import test_editor_build as build_tests

build = build_tests.build
synthetic_runtime_build = build_tests.synthetic_runtime_build


def manifest(dist):
    source = (dist / "service-worker.js").read_text()
    stamp = re.search(r'const BUILD = "([0-9a-f]+)";', source).group(1)
    entries = json.loads(re.search(r"const ASSETS = (.*);", source).group(1))
    return stamp, entries


def test_offline_manifest_covers_actual_byte_hashes_and_versioned_editor(synthetic_runtime_build):
    _source, dist = synthetic_runtime_build
    build.main()
    stamp, entries = manifest(dist)
    urls = [a["url"] for a in entries]
    assert len(urls) == len(set(urls))
    assert "index.html" in urls and "manifest.webmanifest" in urls
    for name in (*build.EDITOR_SCRIPTS, "boot.js", "worker.js", "adapter.py", "editor.css"):
        assert f"{name}?v={stamp}" in urls
    for name in build.PYODIDE_FILES:
        assert f"pyodide-0.27.7/{name}" in urls
    assert any(u.startswith("duplotrain-src-") for u in urls)
    for entry in entries:
        parsed = urlsplit(entry["url"])
        assert not parsed.scheme and not parsed.netloc
        assert not parsed.path.startswith("/") and ".." not in Path(parsed.path).parts
        payload = (dist / parsed.path).read_bytes()
        assert hashlib.sha256(payload).hexdigest() == entry["sha256"]
        assert len(payload) == entry["bytes"]
    assert not any("api/" in u or "project" == u for u in urls)
    assert "__BUILD__" not in (dist / "boot.js").read_text()
    assert "__ASSETS__" not in (dist / "service-worker.js").read_text()


def test_offline_code_changes_stamp_and_manifest_without_changing_project_formats(
    synthetic_runtime_build, monkeypatch, tmp_path,
):
    _source, dist = synthetic_runtime_build
    build.main()
    before, _ = manifest(dist)
    webapp = tmp_path / "copied-webapp"
    webapp.mkdir()
    for name in ("adapter.py", "boot.js", "worker.js", "service-worker.js"):
        (webapp / name).write_bytes((build.WEBAPP / name).read_bytes())
    path = webapp / "service-worker.js"
    path.write_text(path.read_text() + "\n// changed implementation\n")
    monkeypatch.setattr(build, "WEBAPP", webapp)
    build.main()
    after, entries = manifest(dist)
    assert after != before
    assert all(before not in entry["url"] for entry in entries)
    assert len(list(dist.glob("duplotrain-src-*.zip"))) == 1


def test_runtime_verification_and_production_csp_are_not_weakened():
    assert build.PYODIDE_SHA256["0.27.7"] == (
        "9bc8f127db6c590b191b9aee754022cb41b1a36c7bac233776c11c5ecb541be8")
    source = (Path(__file__).parents[1] / "webapp/service-worker.js").read_text()
    assert "skipWaiting" in source  # only the explicit ACTIVATE message path
    install = source.split('self.addEventListener("install"', 1)[1].split(
        'self.addEventListener("message"', 1)[0]
    assert "await self.skipWaiting" not in install
    assert '"/api/"' in source and 'request.method !== "GET"' in source
    assert "crypto.subtle.digest" in source
