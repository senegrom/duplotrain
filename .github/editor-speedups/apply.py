"""Apply the reviewed editor patch, refusing changed input or output bytes."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXPECTED = json.loads(r'''{"tested_parent":"254ea4973a272a9f0fd27479f540705b50ce7903","files":[["docs/performance.md",null,"3171c19c117aa7d6503744859cc878cbad49f296899350c4f70aa674928fe893"],["src/duplotrain/exact.py","18444fd2a495330545fa0fbdb4cc06b071c0c158f3b016b2975948fa04d0a5d1","b28b41d86566b4a88b4ac1d8aa110d9b78f7e45c9c5f8a9ca9d1f58d0f36c896"],["src/duplotrain/gui.py","cdf887388cd230c939b10dd9bf148ed3e449b58cf2d2a44af966cea8ba0e7765","0fb03cfe569fcc8b00fb130765207b43c0176a0f9bb229378c1bb7cee272c6a6"],["src/duplotrain/layout.py","d95e507b3b25e53d2aa48db3b0eac268d923b0a7129abbdf400d6fe779575958","8bf40bb83a2c71ee9fffc6375332a762b657ddc192fea9114800b0984639d339"],["src/duplotrain/pieces.py","e3b0370665fa4c6e0e4a25c635591296193aceb9e46a38efb458726c047644bd","1c7467e42cb5ef26d8eca8962e1cbee86058a2d5104294b7806975beaa9ee98c"],["src/duplotrain/solver.py","b0581bb8c894e3340094164acb847ebc0f3b91d1a539ef8ffcdaa400bc75efff","a7594c060862014cf4b5d5ed853187339c3a617819c81a4d0ca55c976c024f2c"],["src/duplotrain/static/editor.html","81f1a585a2efe82650bb96d7f2f1b786e03e811c9c9703070358e1321c0c29fd","d015e6a20049ba27eb8e7c8cff3ebe2a95c80e6829793c98ea22e34ee12b50bb"],["tests/browser/test_editor.py","2afcc904a170764d0bb82ac8a1c3858b8f99eaab3d760741d6a08e9944139898","546653cf34bcbef12a255abec5a5331a0783f8b1c48e49970fa6df958806497c"],["tests/test_performance_contracts.py",null,"f90950c619a945449cd48efcd63474ac1ca3e353b314fccd55bcc53833553724"],["tests/test_worker_bundle.py",null,"fcdd4fb6a355e8bbdd27fd1b07fe433065fca4a79c6904fb479966f19fcd4b69"],["tests/web/render-reuse.test.cjs",null,"f958d5fadfcd356c14c7c6aa996fff18342b30817709501ceb2ffbf078d9325b"],["webapp/build.py","a037c0e4bd7d507035f874a3127c423ec20c9820e86b18698d664f4088e369d4","146de8b696e8dcaa1d7ac973fcacec74f090fc1b5a26bc83727e20d1b2c2215e"]],"patch_sha256":"e84f13239cfe3397ca2906086138c66d6b6601b266a6f46a18976abf043d800d"}''')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None

parts = sorted(Path(__file__).parent.glob("[0-9][0-9].patch"))
assert len(parts) == 12, "Incomplete patch"
patch = b"".join(path.read_bytes() for path in parts)
assert hashlib.sha256(patch).hexdigest() == EXPECTED["patch_sha256"], "Patch mismatch"
for name, before, after in EXPECTED["files"]:
    path = ROOT / name
    assert path.resolve().is_relative_to(ROOT) and name.startswith(("src/", "webapp/", "tests/", "docs/"))
    assert digest(path) == before, f"Concurrent source change: {name}"
subprocess.run(["git", "apply", "--index", "--whitespace=error", "-"],
               input=patch, cwd=ROOT, check=True)
changed = subprocess.check_output(["git", "diff", "--cached", "--name-only"], cwd=ROOT, text=True)
assert changed.splitlines() == [name for name, _, _ in EXPECTED["files"]]
for name, before, after in EXPECTED["files"]:
    assert digest(ROOT / name) == after, f"Output mismatch: {name}"
print("All 12 reviewed files match; no other code or proof files changed.")
