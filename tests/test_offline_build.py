"""The offline manifest binds every executable/runtime asset to one content build."""
import hashlib
import io
import json
import re
import shutil
import zipfile
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


def version_name(dist):
    source = (dist / "service-worker.js").read_text()
    return re.search(r'const VERSION = "([0-9a-f]{16})";', source).group(1)


def version(dist):
    """The offline version's name: the digest of what the manifest serves.

    The engine zip counts by its entries, read back here, not by its bytes.
    """
    source = (dist / "service-worker.js").read_text()
    name = version_name(dist)
    served = []
    for entry in json.loads(re.search(r"const ASSETS = (.*);", source).group(1)):
        if entry["url"].startswith("duplotrain-src-"):
            with zipfile.ZipFile(dist / entry["url"]) as archive:
                content = hashlib.sha256(b"".join(
                    f"{info.filename}\n{info.file_size}\n".encode() + archive.read(info)
                    for info in archive.infolist())).hexdigest()
            entry = {"url": entry["url"], "content": content}
        served.append(entry)
    assert name == hashlib.sha256(
        json.dumps(served, separators=(",", ":")).encode()).hexdigest()[:16]
    return name


def test_offline_manifest_covers_actual_byte_hashes_and_versioned_editor(synthetic_runtime_build):
    source, dist = synthetic_runtime_build
    (dist / "icons").mkdir(parents=True)
    (dist / "icons" / "duplotrain-app-64-v0.png").write_bytes(b"left by an earlier build")
    build.main()
    stamp, entries = manifest(dist)
    urls = [a["url"] for a in entries]
    assert len(urls) == len(set(urls))
    assert "icons/duplotrain-app-64-v0.png" not in urls
    # The root icons serve only the local server; the page links those under icons/.
    assert not any((dist / name).exists()
                   for name in ("favicon.ico", "apple-touch-icon.png", "duplotrain-icon.svg"))
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


def test_one_commit_names_one_offline_version_on_every_build_host(
    synthetic_runtime_build, monkeypatch, tmp_path,
):
    # zlib and zlib-ng compress the same entries to different bytes, and a Windows
    # checkout may have CRLF text files. Neither may make a deploy from another
    # host look like a new version that every installed copy downloads again.
    source, dist = synthetic_runtime_build
    build.main()
    before = manifest(dist)[0], version_name(dist)
    engine = next(dist.glob("duplotrain-src-*.zip")).read_bytes()

    def recompressed(entries):
        buffer = io.BytesIO()
        with zipfile.ZipFile(buffer, "w") as archive:
            for arcname, payload in entries:
                archive.writestr(zipfile.ZipInfo(arcname, date_time=(2020, 1, 1, 0, 0, 0)),
                                 payload, zipfile.ZIP_DEFLATED, compresslevel=1)
        return buffer.getvalue()

    monkeypatch.setattr(build, "build_source_zip", recompressed)
    webapp = tmp_path / "crlf-webapp"
    shutil.copytree(build.WEBAPP, webapp,
                    ignore=shutil.ignore_patterns("dist", "vendor", "__pycache__"))
    monkeypatch.setattr(build, "WEBAPP", webapp)
    for root in (source / "src/duplotrain", webapp):
        for path in root.rglob("*"):
            if path.suffix in (".py", ".js", ".css", ".html", ".webmanifest", ".svg"):
                text = path.read_bytes().replace(b"\r\n", b"\n")
                path.write_bytes(text.replace(b"\n", b"\r\n"))
    build.main()
    assert next(dist.glob("duplotrain-src-*.zip")).read_bytes() != engine
    assert (manifest(dist)[0], version_name(dist)) == before
    assert version(dist)


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

