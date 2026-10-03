"""Editor-only packaging and optional congruence features preserve geometry."""

import importlib.util
import json
import math
import random
import subprocess
import sys
from pathlib import Path

import pytest

from duplotrain import _congruence as curves
from duplotrain.catalog import default_catalog
from duplotrain.exact import Alg
from duplotrain.geometry import DEGREES_PER_STEP, Pose
from duplotrain.layout import Layout, Placement, layout_from_dict

ROOT = Path(__file__).resolve().parents[1]


def reference_length(union):
    lines, circles, _isolated, opaque, _features = union
    lengths = [math.sqrt(float(sum(((y - x) * (y - x)
                                   for x, y in zip(a, b, strict=True)), Alg(0))))
               for a, b in lines]
    lengths.extend(float(radius) * math.radians(DEGREES_PER_STEP * len(sectors))
                   for (_centre, radius), sectors in circles.items())
    lengths.extend(segment.length() for _start, _end, segment in opaque)
    return math.fsum(lengths)


@pytest.mark.parametrize("seed", range(12))
def test_length_only_union_matches_full_union(seed):
    rng = random.Random(seed)
    catalog = default_catalog()
    choices = [catalog[k] for k in ("straight", "curve", "switch", "ramp", "span")]
    pieces = [Placement(rng.choice(choices), Pose(
        Alg(rng.randrange(-3, 4) * 128), Alg(rng.randrange(-3, 4) * 128),
        Alg(rng.randrange(3) * 64), rng.randrange(24))) for _ in range(12)]
    layout = Layout(pieces + pieces[::2])  # overlapping exact duplicates must be unioned
    complete = curves._union(layout)
    lean = curves._union(layout, with_features=False)
    assert lean[0] == complete[0] and lean[1] == complete[1] and lean[3] == complete[3]
    assert lean[2] == lean[4] == set()
    assert layout.track_length() == reference_length(complete)
    assert curves.curve_key(layout, 8, 1) == curves.curve_key(Layout(pieces), 8, 1)


@pytest.mark.parametrize("name", ["bridge-gap.json", "bridge-completed.json"])
def test_reported_layout_lengths_and_shape_keys_keep_the_default_features(name, monkeypatch):
    layout = layout_from_dict(json.loads((ROOT / "tests/fixtures" / name).read_text()),
                              default_catalog())
    original = curves._union
    expected = reference_length(original(layout))
    key = curves.curve_key(layout, 8, 1)
    calls = []

    def observed(layout, *, with_features=True):
        calls.append(with_features)
        return original(layout, with_features=with_features)

    monkeypatch.setattr(curves, "_union", observed)
    assert layout.track_length() == expected
    assert calls == [False]
    calls.clear()
    assert curves.curve_key(layout, 8, 1) == key
    assert calls == [True]


def test_empty_and_coincident_track_do_not_gain_length():
    assert Layout().track_length() == 0
    piece = Placement(default_catalog()["straight"], Pose(Alg(0), Alg(0), Alg(0), 0))
    assert Layout([piece, piece]).track_length() == Layout([piece]).track_length()


def test_built_editor_archive_runs_without_desktop_congruence(tmp_path):
    spec = importlib.util.spec_from_file_location("editor_build_test", ROOT / "webapp/build.py")
    build = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(build)
    entries = build.worker_entries()
    names = {name for name, _payload in entries}
    assert "duplotrain/_congruence.py" not in names
    assert "duplotrain/layout.py" in names
    assert (ROOT / "src/duplotrain/_congruence.py").is_file()
    archive = tmp_path / "editor.zip"
    archive.write_bytes(build.build_source_zip(entries))
    # -I ignores checkout/PYTHONPATH; import only the built package and stdlib.
    script = '''
import json, sys
sys.path.insert(0, sys.argv[1])
from duplotrain.catalog import default_catalog
from duplotrain.editor import Session, PREVIEW_FORMAT, dispatch_session
from duplotrain.editor_search import SearchJob
from duplotrain.layout import build_chain
c = default_catalog()
s = Session(history=[build_chain([(c["curve"], 0, 1)] * 6)], unlimited=True)
initial = s.snapshot()
job = SearchJob(s, {"max_pieces": 6, "max_results": 8})
s._interactive_job = job
while job.status == "running":
    job.tick()
assert job.solutions
result = dispatch_session(s, "/api/search/publish", {
    "job_id": job.id, "revision": s.revision, "page_only": True,
    "preview_format": PREVIEW_FORMAT})
assert result["candidates"] == [] and result["search_job"]["candidates"]
s.apply_candidate(result["search_job"]["candidates"][0]["index"], s.revision)
assert s.layout.is_closed and not s.layout.joint_issues()
dispatch_session(s, "/api/check", {"revision": s.revision})
dispatch_session(s, "/api/drive", {"revision": s.revision, "start": [0, 0]})
s.undo()
assert s.snapshot() == initial
assert "duplotrain._congruence" not in sys.modules
print("editor archive validated")
'''
    result = subprocess.run([sys.executable, "-I", "-c", script, str(archive)],
                            text=True, capture_output=True, timeout=30, check=True)
    assert result.stdout.strip() == "editor archive validated"
