"""Build the static duplotrain web app into webapp/dist/.

Output layout (everything self-hosted, no third-party requests at runtime):

    dist/
      index.html                    the editor, with boot.js injected
      editor*.js / editor.css       the editor's scripts and style
      boot.js / worker.js           the worker bridge and the engine worker
      adapter.py                    the dispatch shim around duplotrain.editor.Session
      duplotrain-src-<stamp>.zip    the Python package, content-stamped
      pyodide-<version>/            Pyodide core (downloaded once into vendor/)
      service-worker.js             the opt-in offline copy
      icons/, manifest.webmanifest  favicon and installed-app identity
      .htaccess                     the caching contract below, for Apache hosts

Caching contract: mutable names (html/js/py) are served ``no-cache`` so every
visit revalidates them (cheap 304s), while the content-stamped zip and the
versioned Pyodide directory are immutable-cached forever.  The engine zip MUST
carry the stamp in its filename: under a flat name, an immutable header would pin
a stale engine in returning visitors' browsers.

Usage:  python webapp/build.py [--pyodide-version 0.27.7] [--pages]

``--pages`` additionally embeds the policy as a ``<meta>`` tag for hosts that
cannot send response headers (GitHub Pages); the stamped asset names keep
such a host's fixed short cache safe.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import shutil
import sys
import tarfile
import tempfile
import urllib.request
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WEBAPP = ROOT / "webapp"
DIST = WEBAPP / "dist"
VENDOR = WEBAPP / "vendor"

EDITOR_SCRIPTS = (
    "editor.js", "editor-geometry.js", "editor-projects.js", "editor-train.js",
    "editor-search.js", "editor-offline.js",
)

WORKER_EXCLUDES = {
    "cli.py",
    "gui.py",  # local HTTP host; the worker imports editor.Session
    "render.py",
    # Public desktop helpers imported only by the regular package __init__.  The
    # browser worker talks to editor.Session directly and does not need these modules.
    "explore.py",
    "networks.py",
    "scoring.py",
}

WORKER_INIT = b'''"""Minimal package marker for the Pyodide editor worker."""\n'''

#: Static files the build does not copy: index.html is made from editor.html,
#: favicon.ico and apple-touch-icon.png answer only the local server's automatic
#: requests, and duplotrain-icon.svg is the source the icons are exported from; the
#: page links its icons under icons/.
NOT_SHIPPED = {"editor.html", "favicon.ico", "apple-touch-icon.png", "duplotrain-icon.svg"}


def text_bytes(path: Path) -> bytes:
    """A text file's bytes with LF newlines, whatever the checkout used.

    A Windows checkout with autocrlf would otherwise ship CRLF sources and give
    the same commit a different content stamp from the Linux CI build.
    """
    return path.read_bytes().replace(b"\r\n", b"\n")


#: Static assets shipped as text, so with LF newlines (see ``text_bytes``).
TEXT_SUFFIXES = (".js", ".css", ".webmanifest", ".svg")


def framed(name: str, payload: bytes) -> bytes:
    """One part of a content digest, framed by its name and length.

    Bytes moving from one part to the next still change the digest.
    """
    return f"{name}\n{len(payload)}\n".encode() + payload

#: Everything Pyodide needs for `loadPyodide` + pure-Python imports.
PYODIDE_FILES = [
    "pyodide.js",
    "pyodide.asm.js",
    "pyodide.asm.wasm",
    "python_stdlib.zip",
    "pyodide-lock.json",
]


# Reviewed release-asset SHA-256, not a checksum fetched alongside the download.
# Source: https://api.github.com/repos/pyodide/pyodide/releases/assets/261126997
# Add a reviewed digest here before using --pyodide-version for another release.
PYODIDE_SHA256 = {
    "0.27.7": "9bc8f127db6c590b191b9aee754022cb41b1a36c7bac233776c11c5ecb541be8",
}
MAX_ARCHIVE_BYTES = 32 * 1024 * 1024
MAX_RUNTIME_BYTES = 128 * 1024 * 1024


def fetch_pyodide(version: str) -> Path:
    """Verify the cached/downloaded archive on every build, then unpack it.

    Never trust loose vendor files (including pre-checksum caches). Re-extract
    from verified bytes so a modified cached runtime cannot enter the build.
    """
    expected = PYODIDE_SHA256.get(version)
    if expected is None:
        raise SystemExit(f"no reviewed Pyodide checksum for {version!r}; update PYODIDE_SHA256")
    target = VENDOR / f"pyodide-{version}"
    archive = VENDOR / f"pyodide-core-{version}.tar.bz2"
    if archive.exists():
        with archive.open("rb") as source:
            data = source.read(MAX_ARCHIVE_BYTES + 1)
    else:
        url = (
            "https://github.com/pyodide/pyodide/releases/download/"
            f"{version}/pyodide-core-{version}.tar.bz2"
        )
        print(f"downloading {url} ...")
        with urllib.request.urlopen(url, timeout=30) as response:
            data = response.read(MAX_ARCHIVE_BYTES + 1)
    if len(data) > MAX_ARCHIVE_BYTES:
        raise SystemExit("Pyodide archive exceeds the download size limit")
    if hashlib.sha256(data).hexdigest() != expected:
        raise SystemExit(f"Pyodide {version} checksum mismatch; remove {archive} and retry")

    # Read only regular, allowlisted basenames; never extract archive paths or
    # links. Validate all entries before changing the vendor directory.
    payloads: dict[str, bytes] = {}
    total = 0
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:bz2") as tar:
        for member in tar:
            name = Path(member.name).name
            if name not in PYODIDE_FILES:
                continue
            if not member.isfile() or name in payloads:
                raise SystemExit(f"invalid or duplicate Pyodide file: {name}")
            total += member.size
            if member.size < 0 or total > MAX_RUNTIME_BYTES:
                raise SystemExit("Pyodide runtime exceeds the extraction size limit")
            stream = tar.extractfile(member)
            if stream is None:
                raise SystemExit(f"cannot read Pyodide file: {name}")
            with stream:
                payloads[name] = stream.read()
    missing = sorted(set(PYODIDE_FILES) - payloads.keys())
    if missing:
        raise SystemExit(f"pyodide release lacked expected files: {missing}")

    VENDOR.mkdir(parents=True, exist_ok=True)
    if not archive.exists():
        # Publish only a complete verified cache, even after an interrupted build.
        with tempfile.NamedTemporaryFile(dir=VENDOR, delete=False) as tmp:
            temporary = Path(tmp.name)
            try:
                tmp.write(data)
                tmp.close()
                temporary.replace(archive)
            finally:
                temporary.unlink(missing_ok=True)
    target.mkdir(parents=True, exist_ok=True)
    for name, payload in payloads.items():
        (target / name).write_bytes(payload)
    print(f"pyodide {version}: SHA-256 verified; unpacked into {target}")
    return target


def worker_entries() -> list[tuple[str, bytes]]:
    """The worker's Python modules as sorted ``(archive name, LF bytes)`` pairs.

    The editor and all static assets are served separately. Desktop files stay in the
    regular Python package, not in the worker (which imports neither).
    """
    src = ROOT / "src" / "duplotrain"
    entries = []
    for path in sorted(src.rglob("*")):
        relative = path.relative_to(src)
        if ("__pycache__" in relative.parts or relative.parts[0] == "static" or not path.is_file()
                or relative.as_posix() in WORKER_EXCLUDES):
            continue
        arcname = (Path("duplotrain") / relative).as_posix()
        payload = WORKER_INIT if relative.as_posix() == "__init__.py" else text_bytes(path)
        entries.append((arcname, payload))
    return entries


def build_source_zip(entries: list[tuple[str, bytes]] | None = None) -> bytes:
    """Zip the worker's Python modules for unpackArchive; returns the bytes.

    Zip entries carry a fixed timestamp. The stamp is taken over the entries
    themselves (see ``main``), never over these bytes: zlib and zlib-ng compress
    identical input differently, so the archive is not reproducible across
    platforms even though its contents are.
    """
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as zf:
        for arcname, payload in (worker_entries() if entries is None else entries):
            info = zipfile.ZipInfo(arcname, date_time=(2020, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            zf.writestr(info, payload)
    return buffer.getvalue()


#: The site serves apps under a strict CSP; this scoped override only adds what
#: Pyodide needs (wasm compilation) and keeps scripts external-only.
_CSP = (
    "default-src 'self'; script-src 'self' 'wasm-unsafe-eval'; "
    "style-src 'self'; img-src 'self'; font-src 'self'; "
    "connect-src 'self'; worker-src 'self'; object-src 'none'; "
    "base-uri 'self'; form-action 'self'; frame-ancestors 'none'; "
    "manifest-src 'self'; upgrade-insecure-requests"
)

#: The same policy for a <meta> tag: browsers ignore frame-ancestors there.
_META_CSP = _CSP.replace("frame-ancestors 'none'; ", "")
assert "frame-ancestors" not in _META_CSP and '"' not in _META_CSP

HTACCESS = """\
# duplotrain: Pyodide needs 'wasm-unsafe-eval' to compile its WebAssembly.
# Scripts and styles stay external and same-origin: no 'unsafe-inline' at all.
<IfModule mod_headers.c>
  Header always set Content-Security-Policy "__CSP__"

  # Mutable names (the page, scripts, adapter) revalidate on every visit so
  # engine fixes actually reach returning visitors; 304s make this cheap.
  # NEVER serve a flat-named artifact as immutable: it would pin a stale
  # engine in browser caches.
  Header set Cache-Control "no-cache"

  # Content-stamped artifacts may cache forever: a new build gets a new name.
  <FilesMatch "^duplotrain-src-[0-9a-f]{8}\\.zip$">
    Header set Cache-Control "public, max-age=31536000, immutable"
  </FilesMatch>
</IfModule>

AddType application/wasm .wasm
""".replace("__CSP__", _CSP)

#: Dropped into the versioned pyodide-<version>/ directory: its URL changes on
#: upgrade, so its contents may cache forever.
HTACCESS_PYODIDE = """\
<IfModule mod_headers.c>
  Header set Cache-Control "public, max-age=31536000, immutable"
</IfModule>

AddType application/wasm .wasm
"""


def build_index(meta_csp: bool = False) -> None:
    """Copy the shared editor assets and inject the static worker boot script.

    JavaScript and CSS are normal source files, not fragments extracted from HTML.
    """
    static = ROOT / "src" / "duplotrain" / "static"
    html = text_bytes(static / "editor.html").decode("utf-8")
    boot_marker = "<!-- Worker boot is inserted here by the static build. -->"
    if html.count(boot_marker) != 1:
        raise SystemExit("editor.html needs one worker boot marker")
    html = html.replace(boot_marker, '<script src="./boot.js?v=__V__" defer></script>')
    for asset in (*EDITOR_SCRIPTS, "editor.css"):
        html = html.replace(f'./{asset}"', f'./{asset}?v=__V__"')
    html = html.replace(
        "<title>duplotrain editor</title>",
        "<title>duplotrain — DUPLO track designer</title>\n"
        '<meta name="description" content="Design LEGO DUPLO train track layouts and '
        'let an exact-arithmetic solver close the loop. Runs entirely in your browser."/>',
        1,
    )
    if meta_csp:
        charset = '<meta charset="utf-8">\n'
        if html.count(charset) != 1:
            raise SystemExit("editor.html changed shape; update webapp/build.py")
        html = html.replace(
            charset,
            charset + f'<meta http-equiv="Content-Security-Policy" content="{_META_CSP}">\n',
        )
    (DIST / "index.html").write_text(html, encoding="utf-8", newline="\n")
    (DIST / ".htaccess").write_text(HTACCESS, encoding="utf-8", newline="\n")
    # Commit raster exports so the static build and installed Python editor use
    # identical icons without needing image-rendering dependencies at build time.
    for source in sorted(static.rglob("*")):
        if not source.is_file() or source.relative_to(static).as_posix() in NOT_SHIPPED:
            continue
        dest = DIST / source.relative_to(static)
        dest.parent.mkdir(parents=True, exist_ok=True)
        if source.suffix in TEXT_SUFFIXES:
            dest.write_bytes(text_bytes(source))
        else:
            shutil.copy2(source, dest)
    print(f"wrote {DIST / 'index.html'}, editor assets and .htaccess")


def _stamp_file(source: Path, dest: Path, replacements: dict[str, str]) -> None:
    text = source.read_text(encoding="utf-8")
    for marker, value in replacements.items():
        if marker not in text:
            raise SystemExit(f"{source.name} lost its {marker} marker; fix webapp/")
        text = text.replace(marker, value)
    dest.write_text(text, encoding="utf-8", newline="\n")


def build_offline_worker(stamp: str, runtime: str, zip_name: str, zip_content: str) -> None:
    """Embed a complete exact-byte manifest, not an open-ended runtime cache.

    *zip_content* is the SHA-256 of the engine zip's framed entries.
    """
    paths = ["index.html", "manifest.webmanifest", zip_name]
    paths += [f"{name}?v={stamp}" for name in (*EDITOR_SCRIPTS, "editor.css",
                                               "boot.js", "worker.js", "adapter.py")]
    paths += [f"{runtime}/{name}" for name in PYODIDE_FILES]
    # The icons the source ships: dist is refreshed in place and may hold stale ones.
    static = ROOT / "src" / "duplotrain" / "static"
    paths += [p.relative_to(static).as_posix() for p in sorted((static / "icons").rglob("*"))
              if p.is_file()]
    assets = []
    for url in paths:
        payload = (DIST / url.split("?")[0]).read_bytes()
        assets.append({"url": url, "bytes": len(payload),
                       "sha256": hashlib.sha256(payload).hexdigest()})
    manifest = json.dumps(assets, separators=(",", ":"))
    # The offline cache is named by what the manifest serves: a change the stamp
    # does not cover (the page's CSP meta, title, web manifest or icons) must still
    # install as a new version rather than be taken for the installed one. The
    # engine zip counts by its entries, not its bytes: zlib and zlib-ng compress
    # the same entries differently, and one commit must name one version on every
    # build host, or a deploy from another host would be downloaded all over again.
    served = [{"url": asset["url"], "content": zip_content} if asset["url"] == zip_name
              else asset for asset in assets]
    version = hashlib.sha256(json.dumps(served, separators=(",", ":")).encode()).hexdigest()
    _stamp_file(WEBAPP / "service-worker.js", DIST / "service-worker.js", {
        "__BUILD__": stamp, "__VERSION__": version[:16], "__ASSETS__": manifest,
    })


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pyodide-version", default="0.27.7", choices=sorted(PYODIDE_SHA256))
    parser.add_argument(
        "--pages", action="store_true",
        help="also embed the CSP as a <meta> tag (GitHub Pages cannot send headers)",
    )
    args = parser.parse_args()

    # Verify dependencies before changing an existing deployable build.
    pyodide_dir = fetch_pyodide(args.pyodide_version)

    # Refresh in place: OneDrive/Windows often hold transient locks on the big
    # pyodide directory, so overwrite rather than rmtree.
    DIST.mkdir(parents=True, exist_ok=True)
    shutil.rmtree(DIST / "__pycache__", ignore_errors=True)

    build_index(meta_csp=args.pages)

    entries = worker_entries()
    zip_bytes = build_source_zip(entries)
    adapter = text_bytes(WEBAPP / "adapter.py")
    # Content-only stamp: the same commit yields the same name on every platform.
    digest = hashlib.sha256()

    def stamp_part(name: str, payload: bytes) -> None:
        digest.update(framed(name, payload))

    for arcname, payload in entries:
        stamp_part(arcname, payload)
    zip_content = hashlib.sha256(b"".join(framed(*entry) for entry in entries)).hexdigest()
    stamp_part("adapter.py", adapter)
    stamp_part("pyodide", args.pyodide_version.encode("ascii"))
    for name in (*EDITOR_SCRIPTS, "editor.css", "editor.html"):
        stamp_part(name, text_bytes(ROOT / "src/duplotrain/static" / name))
    for name in ("boot.js", "worker.js", "service-worker.js"):
        stamp_part(name, text_bytes(WEBAPP / name))
    stamp = digest.hexdigest()[:8]

    for stale in DIST.glob("duplotrain-src*.zip"):
        stale.unlink()
    zip_name = f"duplotrain-src-{stamp}.zip"
    (DIST / zip_name).write_bytes(zip_bytes)
    print(f"wrote {DIST / zip_name} ({len(zip_bytes) / 1e3:.0f} kB)")

    index = (DIST / "index.html").read_text(encoding="utf-8")
    (DIST / "index.html").write_text(
        index.replace("__V__", stamp), encoding="utf-8", newline="\n"
    )

    pyodide_dirname = f"pyodide-{args.pyodide_version}"
    _stamp_file(WEBAPP / "boot.js", DIST / "boot.js", {"__BUILD__": stamp})
    _stamp_file(
        WEBAPP / "worker.js",
        DIST / "worker.js",
        {
            "__PYODIDE_DIR__": f"./{pyodide_dirname}",
            "__ENGINE_ZIP__": f"./{zip_name}",
            "__ADAPTER__": f"./adapter.py?v={stamp}",
        },
    )
    (DIST / "adapter.py").write_bytes(adapter)

    dest = DIST / pyodide_dirname
    dest.mkdir(exist_ok=True)
    for name in PYODIDE_FILES:
        shutil.copy2(pyodide_dir / name, dest / name)
    (dest / ".htaccess").write_text(HTACCESS_PYODIDE, encoding="utf-8", newline="\n")

    build_offline_worker(stamp, pyodide_dirname, zip_name, zip_content)
    total = sum(f.stat().st_size for f in DIST.rglob("*") if f.is_file())
    print(f"dist ready: build {stamp}, {total / 1e6:.1f} MB total")


if __name__ == "__main__":
    sys.exit(main())
