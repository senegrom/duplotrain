"""Build the static duplotrain web app into webapp/dist/.

Output layout (everything self-hosted, no third-party requests at runtime):

    dist/
      index.html                    the editor, with boot.js injected
      boot.js / app.js / worker.js  bridge + editor + engine worker
      adapter.py                    the dispatch shim around duplotrain.gui.Session
      duplotrain-src-<stamp>.zip    the Python package, content-stamped
      pyodide-<version>/            Pyodide core (downloaded once into vendor/)

Caching contract: mutable names (html/js/py) are served ``no-cache`` so every
visit revalidates them (cheap 304s), while the content-stamped zip and the
versioned Pyodide directory are immutable-cached forever.  The engine zip MUST
carry the stamp in its filename: it was once served under a flat name with an
immutable header, which pinned stale engines in returning visitors' browsers.

Usage:  python webapp/build.py [--pyodide-version 0.27.7]
"""

from __future__ import annotations

import argparse
import hashlib
import io
import shutil
import sys
import tarfile
import urllib.request
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WEBAPP = ROOT / "webapp"
DIST = WEBAPP / "dist"
VENDOR = WEBAPP / "vendor"

#: Everything Pyodide needs for `loadPyodide` + pure-Python imports.
PYODIDE_FILES = [
    "pyodide.mjs",
    "pyodide.js",
    "pyodide.asm.js",
    "pyodide.asm.wasm",
    "python_stdlib.zip",
    "pyodide-lock.json",
]


def fetch_pyodide(version: str) -> Path:
    """Download (once) and unpack the Pyodide core release into vendor/."""
    target = VENDOR / f"pyodide-{version}"
    if all((target / name).exists() for name in PYODIDE_FILES):
        print(f"pyodide {version}: cached in {target}")
        return target
    url = (
        "https://github.com/pyodide/pyodide/releases/download/"
        f"{version}/pyodide-core-{version}.tar.bz2"
    )
    print(f"downloading {url} ...")
    with urllib.request.urlopen(url) as response:
        data = response.read()
    print(f"  {len(data) / 1e6:.1f} MB; unpacking")
    target.mkdir(parents=True, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:bz2") as tar:
        for member in tar.getmembers():
            name = Path(member.name).name
            if member.isfile() and name in PYODIDE_FILES:
                payload = tar.extractfile(member).read()
                (target / name).write_bytes(payload)
    missing = [n for n in PYODIDE_FILES if not (target / n).exists()]
    if missing:
        raise SystemExit(f"pyodide release lacked expected files: {missing}")
    return target


def build_source_zip() -> bytes:
    """Zip src/duplotrain (source only) for unpackArchive; returns the bytes.

    Zip entries carry a fixed timestamp so the stamp depends on content alone.
    """
    src = ROOT / "src" / "duplotrain"
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as zf:
        for path in sorted(src.rglob("*")):
            if "__pycache__" in path.parts or not path.is_file():
                continue
            arcname = str(Path("duplotrain") / path.relative_to(src))
            info = zipfile.ZipInfo(arcname, date_time=(2020, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            zf.writestr(info, path.read_bytes())
    return buffer.getvalue()


#: The site serves apps under a strict CSP; this scoped override only adds what
#: Pyodide needs (wasm compilation) and keeps scripts external-only.
_CSP = (
    "default-src 'self'; script-src 'self' 'wasm-unsafe-eval'; "
    "style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self'; "
    "connect-src 'self'; worker-src 'self' blob:; object-src 'none'; "
    "base-uri 'self'; form-action 'self'; frame-ancestors 'none'; "
    "manifest-src 'self'; upgrade-insecure-requests"
)

HTACCESS = """\
# duplotrain: Pyodide needs 'wasm-unsafe-eval' to compile its WebAssembly.
# All scripts stay external and same-origin (no 'unsafe-inline' for scripts).
<IfModule mod_headers.c>
  Header always set Content-Security-Policy "__CSP__"

  # Mutable names (the page, scripts, adapter) revalidate on every visit so
  # engine fixes actually reach returning visitors; 304s make this cheap.
  # NEVER serve a flat-named artifact as immutable -- a stale engine pinned
  # in browser caches is exactly the bug this policy replaced.
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


def build_index() -> None:
    """The editor split CSP-clean: page + external app.js, boot.js loaded first."""
    editor = (ROOT / "src" / "duplotrain" / "static" / "editor.html").read_text(
        encoding="utf-8"
    )
    start_marker = "<script>\n\"use strict\";"
    end_marker = "</script>\n</body>"
    if start_marker not in editor or end_marker not in editor:
        raise SystemExit("editor.html changed shape; update webapp/build.py")
    head, rest = editor.split(start_marker, 1)
    script, tail = rest.rsplit(end_marker, 1)
    (DIST / "app.js").write_text(
        '"use strict";' + script, encoding="utf-8", newline="\n"
    )

    html = (
        head
        + '<script src="./boot.js?v=__V__"></script>\n'
        + '<script src="./app.js?v=__V__"></script>\n</body>'
        + tail
    )
    html = html.replace(
        "<title>duplotrain editor</title>",
        "<title>duplotrain — DUPLO track designer</title>\n"
        '<meta name="description" content="Design LEGO DUPLO train track layouts and '
        'let an exact-arithmetic solver close the loop. Runs entirely in your browser."/>',
        1,
    )
    (DIST / "index.html").write_text(html, encoding="utf-8", newline="\n")
    (DIST / ".htaccess").write_text(HTACCESS, encoding="utf-8", newline="\n")
    print(f"wrote {DIST / 'index.html'}, app.js and .htaccess")


def _stamp_file(source: Path, dest: Path, replacements: dict[str, str]) -> None:
    text = source.read_text(encoding="utf-8")
    for marker, value in replacements.items():
        if marker not in text:
            raise SystemExit(f"{source.name} lost its {marker} marker; fix webapp/")
        text = text.replace(marker, value)
    dest.write_text(text, encoding="utf-8", newline="\n")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pyodide-version", default="0.27.7")
    args = parser.parse_args()

    # Refresh in place: OneDrive/Windows often hold transient locks on the big
    # pyodide directory, so overwrite rather than rmtree.
    DIST.mkdir(parents=True, exist_ok=True)
    shutil.rmtree(DIST / "__pycache__", ignore_errors=True)

    build_index()

    zip_bytes = build_source_zip()
    adapter = (WEBAPP / "adapter.py").read_bytes()
    stamp_src = zip_bytes + adapter + (DIST / "app.js").read_bytes()
    for name in ("boot.js", "worker.js"):
        stamp_src += (WEBAPP / name).read_bytes()
    stamp = hashlib.sha256(stamp_src).hexdigest()[:8]

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
    shutil.copy2(WEBAPP / "adapter.py", DIST / "adapter.py")

    pyodide_dir = fetch_pyodide(args.pyodide_version)
    dest = DIST / pyodide_dirname
    dest.mkdir(exist_ok=True)
    for name in PYODIDE_FILES:
        shutil.copy2(pyodide_dir / name, dest / name)
    (dest / ".htaccess").write_text(HTACCESS_PYODIDE, encoding="utf-8", newline="\n")
    # The pre-stamp flat layout, if present from an older build.
    shutil.rmtree(DIST / "pyodide", ignore_errors=True)

    total = sum(f.stat().st_size for f in DIST.rglob("*") if f.is_file())
    print(f"dist ready: build {stamp}, {total / 1e6:.1f} MB total")


if __name__ == "__main__":
    sys.exit(main())
