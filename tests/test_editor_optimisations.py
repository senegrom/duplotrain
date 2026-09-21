"""Presentation optimisations must not cache state or change sampled diagnostics."""

import gc
import http.client
import json
import random
import weakref
from dataclasses import replace

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.collision import DEFAULT_CLEARANCE, CollisionField, bounds_of
from duplotrain.editor import PREVIEW_FORMAT, Session, _drawing_lines, _drawing_size
from duplotrain.editor_tools import check_session
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, Placement, build_chain
from tests.editor_support import load_adapter, running_server, unchanged


def reference_overlaps(layout):
    """The pre-index all-pairs check, including order and truncation semantics."""
    neighbours = {}
    for (a, _), (b, _) in layout.links.items():
        neighbours.setdefault(a, set()).add(b)
    fields, result = [], []
    for i, placement in enumerate(layout):
        points = [point for line in placement.centrelines(8.0) for point in line]
        half, bounds = placement.piece.width / 2, bounds_of(points)
        for j, field in enumerate(fields):
            if j in neighbours.get(i, ()):
                continue
            if field.near(bounds, half, set()) and field.clashes(
                points, half, set(), underpass=placement.piece.underpass,
            ):
                result.append([j, i])
                if len(result) == 200:
                    return result, False
        field = CollisionField(clearance=DEFAULT_CLEARANCE)
        field.add(i, points, half, underpass=placement.piece.underpass)
        fields.append(field)
    return result, True


@pytest.mark.parametrize("seed", range(12))
def test_indexed_diagnostics_match_original_sampled_pairs(seed):
    rng = random.Random(seed)
    pieces = list(default_catalog().values())
    # Sparse early pieces ensure the check reaches the index activation threshold;
    # the final cluster includes contacts at varying heights and both wide pieces
    # and underpasses. Negative cells and non-lattice headings are intentional.
    placements = [Placement(pieces[i % len(pieces)], Pose.make(-900 * i, -700, heading=i % 24))
                  for i in range(130)]
    placements += [Placement(rng.choice(pieces), Pose.make(
        rng.randrange(-400, 401), rng.randrange(-400, 401),
        z=rng.choice([0, 40, 42, 57.6, 120, 160]), heading=rng.randrange(24),
    )) for _ in range(40)]
    layout = Layout(tuple(placements))
    report = check_session(Session(history=[layout]))
    assert (report["overlaps"], report["overlap_check_complete"]) == reference_overlaps(layout)


@pytest.mark.parametrize("count", [0, 1, 24, 127, 128, 129, 180])
def test_diagnostics_small_and_indexed_paths_keep_report_and_truncation(count):
    piece = default_catalog()["straight"]
    layout = Layout(tuple(Placement(piece, Pose.make()) for _ in range(count)))
    session = Session(history=[layout])
    before = unchanged(session)
    report = check_session(session)
    assert (report["overlaps"], report["overlap_check_complete"]) == reference_overlaps(layout)
    assert unchanged(session) == before


def test_diagnostic_neighbours_and_sample_cache_match(monkeypatch):
    cat = default_catalog()
    layout = build_chain([(cat["curve"], 0, 1)] * 24).join((0, 0), (23, 1))
    original = check_session(Session(history=[layout]))
    expected = reference_overlaps(layout)
    assert (original["overlaps"], original["overlap_check_complete"]) == expected
    # Warm the shared point-cloud cache, then prove the diagnostic path no longer
    # transforms/reshapes the same routes via the drawing helper.
    for placement in layout:
        assert placement.centreline_points(8.0) == tuple(
            point for line in placement.centrelines(8.0) for point in line
        )
    monkeypatch.setattr(Placement, "centrelines", lambda *_a, **_k: pytest.fail("resampled"))
    assert check_session(Session(history=[layout])) == original


@pytest.mark.parametrize("wide", [False, True])
def test_spatial_shortlist_is_sorted_distinct_conservative_and_non_binning(wide):
    field = CollisionField()
    for index in range(140):
        x = -500 * index
        points = [(x, 0.0, 0.0), (x + (1e8 if wide and index == 0 else 128), 0.0, 0.0)]
        field.add_deferred(index, points, (0.0, 0.0, 0.0), 80, bounds_of(points))
    # Duplicate placement IDs remain valid input to a collision field.
    field.add_deferred(139, [(-69500.0, 0.0, 0.0)], (0.0, 0.0, 0.0), 32,
                       (-69500.0, -69500.0, 0.0, 0.0, 0.0, 0.0))
    bounds = (-69560.0, -69400.0, -1.0, 1.0, -1.0, 1.0)
    ids = field.nearby_placements(bounds, 32)
    assert ids == sorted(set(ids)) and 139 in ids
    assert not field._grid
    assert all(cloud.deferred is not None for cloud in field._clouds)
    field.pop()
    assert 139 in field.nearby_placements(bounds, 32)
    field.pop()
    assert 139 not in field.nearby_placements(bounds, 32)


@pytest.mark.parametrize("pid", list(default_catalog()))
def test_drawing_cache_keeps_routes_values_and_public_mutability_isolation(pid):
    piece = default_catalog()[pid]
    placement = Placement(piece, Pose.make(-125.125, 301.75, z=57.6, heading=3))
    expected = {"width": piece.width, "lines": [
        [[round(x, 2), round(y, 2), round(z, 2)] for x, y, z in line]
        for line in placement.centrelines(10.0)
    ]}
    one, two = Session._drawing_json(placement), Session._drawing_json(placement)
    assert one == two == expected and one is not two
    one["lines"][0][0][0] = 1e99
    one["lines"].append([])
    one["width"] = 0
    assert Session._drawing_json(placement) == two == expected
    changed = Placement(replace(piece, width=piece.width + 1), placement.frame)
    assert Session._drawing_json(changed)["width"] == piece.width + 1


def test_presentation_caches_are_bounded_and_do_not_retain_sessions():
    _drawing_lines.cache_clear()
    _drawing_size.cache_clear()
    piece = default_catalog()["straight"]
    for index in range(2060):
        placement = Placement(piece, Pose.make(index * 10, 0))
        Session._drawing_json(placement)
        _drawing_size((placement,))
    assert _drawing_lines.cache_info().currsize == _drawing_lines.cache_info().maxsize == 2048
    assert _drawing_size.cache_info().currsize == _drawing_size.cache_info().maxsize == 32
    session = Session(history=[Layout((placement,))])
    session.state()
    ref = weakref.ref(session)
    del session
    gc.collect()
    assert ref() is None


def test_size_cache_is_geometry_only_and_state_fields_stay_live():
    cat = default_catalog()
    layout = build_chain([(cat["straight"], 0, 1)] * 2)
    assert _drawing_size(layout.placements) == layout.size()
    session = Session(history=[layout])
    original = session.state(preview_format=PREVIEW_FORMAT)
    session.set_inventory({"straight": 81})
    current = session.state(preview_format=PREVIEW_FORMAT)
    assert original["layout"] == current["layout"]
    assert current["inventory"]["owned"]["straight"] == 81
    assert current["revision"] != original["revision"]
    disconnected = Layout(layout.placements)
    session = Session(history=[disconnected])
    assert len(session.state()["open_ends"]) == 4
    assert _drawing_size(disconnected.placements) == layout.size()


def test_restore_checks_final_snapshot_once_and_rejection_is_atomic(monkeypatch):
    session = Session()
    snapshot = session.snapshot()
    check = session._check_snapshot
    calls = []

    def counted(data):
        calls.append(data)
        check(data)

    monkeypatch.setattr(session, "_check_snapshot", counted)
    session.restore(snapshot)
    assert len(calls) == 1
    before = unchanged(session)

    def reject(_snapshot):
        raise ValueError("too large")

    monkeypatch.setattr(session, "_check_snapshot", reject)
    with pytest.raises(ValueError, match="too large"):
        session.restore(snapshot)
    assert unchanged(session) == before


@pytest.mark.parametrize("path,body", [
    ("/api/state", {}), ("/api/missing", {}), ("/api/clear", {"revision": -1}),
    ("/api/attach", {"piece": "not a piece – 🚂", "entry": 0}),
])
def test_worker_json_is_compact_but_keeps_strings_and_ascii_escaping(path, body):
    adapter = load_adapter()
    raw = adapter.dispatch(path, json.dumps(body))
    assert raw == json.dumps(json.loads(raw), separators=(",", ":"))
    assert raw.isascii()


def test_http_json_is_compact_and_the_export_schema_is_unchanged():
    with running_server(Session()) as server:
        for path in ("/api/state", "/api/export", "/missing"):
            connection = http.client.HTTPConnection("127.0.0.1", server.server_port, timeout=3)
            try:
                connection.request("GET", path)
                response = connection.getresponse()
                raw = response.read().decode()
                assert raw == json.dumps(json.loads(raw), separators=(",", ":"))
                if path == "/api/export":
                    assert json.loads(raw)["format"] == "duplotrain-layout/1"
            finally:
                connection.close()
