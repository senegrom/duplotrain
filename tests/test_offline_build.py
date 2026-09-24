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


def version(dist):
    """The offline version's name, which must be the digest of its manifest."""
    source = (dist / "service-worker.js").read_text()
    name = re.search(r'const VERSION = "([0-9a-f]{16})";', source).group(1)
    assert name == hashlib.sha256(
        re.search(r"const ASSETS = (.*);", source).group(1).encode()).hexdigest()[:16]
    return name


def test_offline_manifest_covers_actual_byte_hashes_and_versioned_editor(synthetic_runtime_build):
    source, dist = synthetic_runtime_build
    build.main()
    stamp, entries = manifest(dist)
    urls = [a["url"] for a in entries]
    assert len(urls) == len(set(urls))
    assert "index.html" in urls and "manifest.webmanifest" in urls
    # An installed app offline still shows its icons: every icon the build ships,
    # and every one the page and the web manifest name, is in the manifest.
    icons = {"icons/" + p.name for p in (source / "src/duplotrain/static/icons").iterdir()}
    assert len(icons) >= 9 and icons <= set(urls)
    named = {icon["src"] for icon in json.loads(
        (dist / "manifest.webmanifest").read_text())["icons"]}
    named |= set(re.findall(r'<link rel="(?:icon|apple-touch-icon)" href="([^"]+)"',
                            (dist / "index.html").read_text()))
    assert len(named) >= 9 and {name.removeprefix("./") for name in named} <= set(urls)
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
    assert version(dist)


def test_a_change_the_stamp_does_not_cover_still_names_a_new_offline_version(
    synthetic_runtime_build, monkeypatch,
):
    source, dist = synthetic_runtime_build
    build.main()
    before = manifest(dist)[0], version(dist)
    webmanifest = source / "src/duplotrain/static/manifest.webmanifest"
    webmanifest.write_text(webmanifest.read_text().replace("duplotrain", "duplotrain!", 1))
    build.main()
    assert manifest(dist)[0] == before[0] and version(dist) != before[1]
    # So does the Pages build's CSP meta tag.
    monkeypatch.setattr(build.sys, "argv", ["build.py"])
    changed = version(dist)
    build.main()
    assert manifest(dist)[0] == before[0] and version(dist) != changed


def test_a_service_worker_change_changes_the_stamp_and_manifest(
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


def test_the_reviewed_pyodide_digest_is_pinned():
    # The service worker's behaviour is tested in tests/web/offline-worker.test.cjs.
    assert build.PYODIDE_SHA256["0.27.7"] == (
        "9bc8f127db6c590b191b9aee754022cb41b1a36c7bac233776c11c5ecb541be8")
