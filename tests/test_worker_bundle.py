"""The lean worker archive must stay deterministic and retain the complete editor API."""

import importlib.util
import io
import subprocess
import sys
import zipfile
from pathlib import Path

ROOT = Path(__file__).parents[1]
spec = importlib.util.spec_from_file_location("worker_build", ROOT / "webapp/build.py")
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)


def test_worker_zip_is_deterministic_and_excludes_only_desktop_files():
    data = build.build_source_zip()
    assert data == build.build_source_zip()
    excluded = {"static/editor.html", "cli.py", "render.py"}
    src = ROOT / "src/duplotrain"
    expected = {
        "duplotrain/" + p.relative_to(src).as_posix()
        for p in src.rglob("*")
        if p.is_file() and "__pycache__" not in p.parts
        and p.relative_to(src).as_posix() not in excluded
    }
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        assert set(archive.namelist()) == expected
        assert all(info.date_time == (2020, 1, 1, 0, 0, 0) for info in archive.infolist())
        assert all("\\" not in name for name in archive.namelist())
    assert all((src / name).is_file() for name in excluded)


def test_isolated_worker_zip_runs_all_editor_operations(tmp_path):
    archive = tmp_path / "engine.zip"
    archive.write_bytes(build.build_source_zip())
    (tmp_path / "adapter.py").write_bytes((ROOT / "webapp/adapter.py").read_bytes())
    code = '''
import sys, json
sys.path[:0] = sys.argv[1:3]
import adapter
from duplotrain import gui
assert "engine.zip" in gui.__file__, gui.__file__
def api(path, body):
    result = json.loads(adapter.dispatch(path, json.dumps(body)))
    assert "__error" not in result, result
    return result
s = api("/api/state", {})
s = api("/api/attach", {"piece": "curve", "entry": 0, "revision": s["revision"]})
s = api("/api/attach", {"piece": "curve", "entry": 0, "at": [0, 1], "revision": s["revision"]})
s = api("/api/solve", {"max_results": 1, "revision": s["revision"]})
assert s["found"] == 1
s = api("/api/apply", {"index": 0, "revision": s["revision"]})
assert s["layout"]["exactly_closed"]
snapshot = s["snapshot"]
exported = api("/api/export", {})
s = api("/api/clear", {"revision": s["revision"]})
s = api("/api/import", {"data": exported, "revision": s["revision"]})
assert s["layout"]["exactly_closed"]
s = api("/api/restore", {"data": snapshot, "revision": s["revision"]})
assert s["snapshot"] == snapshot
# Trimming the worker must not remove the shared stale-edit protection.
r = json.loads(adapter.dispatch("/api/clear", json.dumps({"revision": 0})))
assert r["code"] == "stale_revision"
assert api("/api/state", {})["snapshot"] == snapshot
'''
    subprocess.run([sys.executable, "-I", "-c", code, str(archive), str(tmp_path)],
                   cwd=tmp_path, check=True, capture_output=True, text=True, timeout=30)
