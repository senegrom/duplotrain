"""The lean worker archive must stay deterministic and retain the complete editor API."""

import importlib.util
import io
import subprocess
import sys
import zipfile
from pathlib import Path

import pytest

ROOT = Path(__file__).parents[1]
spec = importlib.util.spec_from_file_location("worker_build", ROOT / "webapp/build.py")
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)


def test_worker_zip_is_deterministic_and_excludes_only_desktop_files():
    data = build.build_source_zip()
    assert data == build.build_source_zip()
    excluded = build.WORKER_EXCLUDES
    src = ROOT / "src/duplotrain"
    expected = {
        "duplotrain/" + p.relative_to(src).as_posix()
        for p in src.rglob("*")
        if p.is_file() and "__pycache__" not in p.parts
        and p.relative_to(src).parts[0] != "static"
        and p.relative_to(src).as_posix() not in excluded
    }
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        assert set(archive.namelist()) == expected
        assert archive.read("duplotrain/__init__.py") == build.WORKER_INIT
        assert all(info.date_time == (2020, 1, 1, 0, 0, 0) for info in archive.infolist())
        assert all("\\" not in name for name in archive.namelist())
        assert not any(name.startswith("duplotrain/static/") for name in archive.namelist())
    assert all((src / name).is_file() for name in excluded)


@pytest.mark.parametrize("compact", [False, True])
def test_isolated_worker_zip_runs_all_editor_operations(tmp_path, compact):
    archive = tmp_path / "engine.zip"
    archive.write_bytes(build.build_source_zip())
    (tmp_path / "adapter.py").write_bytes((ROOT / "webapp/adapter.py").read_bytes())
    code = '''
import sys, json
sys.path[:0] = sys.argv[1:3]
import adapter
from duplotrain import editor
assert "engine.zip" in editor.__file__, editor.__file__
assert "duplotrain.gui" not in sys.modules
assert "http.server" not in sys.modules
assert "webbrowser" not in sys.modules
def api(path, body):
    if sys.argv[3] == "compact" and path != "/api/export":
        body = {**body, "preview_format": "duplotrain-preview/1"}
    result = json.loads(adapter.dispatch(path, json.dumps(body)))
    assert "__error" not in result, result
    return result
s = api("/api/state", {})
s = api("/api/attach", {"piece": "curve", "entry": 0, "revision": s["revision"]})
s = api("/api/attach", {"piece": "curve", "entry": 0, "at": [0, 1], "revision": s["revision"]})
# The resumable search and the route analysis are imported only when first used.
assert "duplotrain.editor_search" not in sys.modules
job = api("/api/search/start", {"revision": s["revision"], "max_results": 1})
body = {"revision": s["revision"], "job_id": job["job_id"]}
for _ in range(500):
    if job["status"] != "running":
        break
    job = api("/api/search/tick", body)
assert job["found"] == 1, job
s = api("/api/search/publish", body)
assert (s["candidates"][0]["preview"].get("format") == "duplotrain-preview/1") == (
    sys.argv[3] == "compact"
)
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
assert "duplotrain.editor_routes" not in sys.modules
routes = api("/api/routes/start", {"revision": s["revision"]})
body = {"revision": s["revision"], "job_id": routes["job_id"]}
for _ in range(500):
    if routes["status"] != "running":
        break
    routes = api("/api/routes/tick", body)
assert routes["complete"] and routes["classification"] is not None, routes
assert api("/api/check", {"revision": s["revision"]})["connector_closed"]
assert api("/api/drive", {"revision": s["revision"], "start": [0, 0]})["complete"]
'''
    run = subprocess.run([sys.executable, "-I", "-c", code, str(archive), str(tmp_path),
                          "compact" if compact else "legacy"],
                         cwd=tmp_path, capture_output=True, text=True, timeout=30)
    assert run.returncode == 0, run.stderr
