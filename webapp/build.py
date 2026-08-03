"""Build the static duplotrain web app into webapp/dist/.

Output layout (everything self-hosted, no third-party requests at runtime):

    dist/
      index.html          the editor, with boot.js injected
      boot.js             Pyodide bootstrap + in-process API bridge
      adapter.py          the dispatch shim around duplotrain.gui.Session
      duplotrain-src.zip  the Python package, plain source
      pyodide/            Pyodide core (downloaded once into webapp/vendor/)

Usage:  python webapp/build.py [--pyodide-version 0.27.7]
"""

from __future__ import annotations

import argparse
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


def build_source_zip() -> None:
    """Zip src/duplotrain (source only) for unpackArchive."""
    out = DIST / "duplotrain-src.zip"
    src = ROOT / "src" / "duplotrain"
    with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as zf:
        for path in sorted(src.rglob("*")):
            if "__pycache__" in path.parts or not path.is_file():
                continue
            zf.write(path, Path("duplotrain") / path.relative_to(src))
    print(f"wrote {out} ({out.stat().st_size / 1e3:.0f} kB)")


#: The site serves apps under a strict CSP; this scoped override only adds what
#: Pyodide needs (wasm compilation) and keeps scripts external-only.
HTACCESS = """\
# duplotrain: Pyodide needs 'wasm-unsafe-eval' to compile its WebAssembly.
# All scripts stay external and same-origin (no 'unsafe-inline' for scripts).
<IfModule mod_headers.c>
  Header always set Content-Security-Policy "default-src 'self'; script-src 'self' 'wasm-unsafe-eval'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; font-src 'self'; connect-src 'self'; worker-src 'self' blob:; object-src 'none'; base-uri 'self'; form-action 'self'; frame-ancestors 'none'; manifest-src 'self'; upgrade-insecure-requests"
</IfModule>

# The Pyodide runtime files are big and effectively immutable; cache hard.
# (Bump the pyodide/ directory name if the runtime is ever upgraded.)
<IfModule mod_headers.c>
  <FilesMatch "\\.(wasm|zip|whl)$">
    Header set Cache-Control "public, max-age=31536000, immutable"
  </FilesMatch>
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
        + '<script src="./boot.js"></script>\n<script src="./app.js"></script>\n</body>'
        + tail
    )
    html = html.replace(
        "<title>duplotrain editor</title>",
        "<title>duplotrain — DUPLO track designer</title>\n"
        '<meta name="description" content="Design LEGO DUPLO train track layouts and '
        'let an exact-arithmetic solver close the loop. Runs entirely in your browser."/>'
        '\n<link rel="canonical" href="https://carlgeorgheise.com/app/duplotrain/"/>',
        1,
    )
    (DIST / "index.html").write_text(html, encoding="utf-8", newline="\n")
    (DIST / ".htaccess").write_text(HTACCESS, encoding="utf-8", newline="\n")
    print(f"wrote {DIST / 'index.html'}, app.js and .htaccess")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pyodide-version", default="0.27.7")
    args = parser.parse_args()

    # Refresh in place: OneDrive/Windows often hold transient locks on the big
    # pyodide directory, so overwrite rather than rmtree.
    DIST.mkdir(parents=True, exist_ok=True)
    shutil.rmtree(DIST / "__pycache__", ignore_errors=True)

    build_index()
    shutil.copy2(WEBAPP / "boot.js", DIST / "boot.js")
    shutil.copy2(WEBAPP / "adapter.py", DIST / "adapter.py")
    build_source_zip()

    pyodide_dir = fetch_pyodide(args.pyodide_version)
    dest = DIST / "pyodide"
    dest.mkdir(exist_ok=True)
    for name in PYODIDE_FILES:
        shutil.copy2(pyodide_dir / name, dest / name)
    total = sum(f.stat().st_size for f in DIST.rglob("*") if f.is_file())
    print(f"dist ready: {total / 1e6:.1f} MB total")


if __name__ == "__main__":
    sys.exit(main())
