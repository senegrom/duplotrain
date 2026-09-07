from __future__ import annotations

import base64
import hashlib
import json
import lzma
from pathlib import Path

EXPECTED_PAYLOAD_SHA256 = "f759a5ebfca9f285f1ef9f808836f2fb07bb33a84e460c5438408506cec6533b"
ALLOWED = {
    "docs/performance.md",
    "src/duplotrain/catalog.py",
    "src/duplotrain/collision.py",
    "src/duplotrain/exact.py",
    "src/duplotrain/layout.py",
    "src/duplotrain/solver.py",
    "tests/test_performance_contracts.py",
    "tests/test_worker_bundle.py",
    "webapp/build.py",
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


parts = sorted(Path(".github/editor-opt").glob("part-*.txt"))
assert [p.name for p in parts] == [f"part-{i}.txt" for i in range(4)]
encoded = b"".join(p.read_bytes() for p in parts)
raw = lzma.decompress(base64.b64decode(encoded, validate=True))
assert sha256(raw) == EXPECTED_PAYLOAD_SHA256
entries = json.loads(raw)
assert len(entries) == len(ALLOWED)
assert {entry[0] for entry in entries} == ALLOWED

for name, before, after, text in entries:
    path = Path(name)
    assert ".." not in path.parts and path.is_relative_to(Path("."))
    old = path.read_bytes()
    assert sha256(old) == before, f"Concurrent source change: {name}"
    new = text.encode("utf-8")
    assert sha256(new) == after, f"Reviewed output mismatch: {name}"
    path.write_bytes(new)

print(f"Applied {len(entries)} hash-verified app edits")
