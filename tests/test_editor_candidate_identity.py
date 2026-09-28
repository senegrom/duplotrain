"""Editor alternatives distinguish full paths, not just matching connector poses."""

from dataclasses import replace

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.editor import Session
from duplotrain.editor_search import SearchJob, physical_key
from duplotrain.geometry import ORIGIN, Pose
from duplotrain.layout import Layout, Placement, layout_to_dict
from duplotrain.pieces import parse_piece
from duplotrain.solver import SolverConfig, _solution_overlaps, solve


def asymmetric_gap():
    piece = parse_piece({"id": "asymmetric", "paths": [{"segments": [
        {"type": "straight", "run": 32},
        {"type": "arc", "radius": 64, "degrees": 90},
        {"type": "straight", "run": 64},
        {"type": "arc", "radius": 64, "degrees": -90},
        {"type": "straight", "run": 96},
    ]}]})
    bar = parse_piece({"id": "bar", "paths": [{"segments": [
        {"type": "straight", "run": 64}]}]})
    base = Layout((Placement(bar, Pose.make(-64, 0)),
                   Placement(bar, Pose.make(256, 192))))
    return piece, bar, base


def finish(job):
    for _ in range(1000):
        if job.status != "running":
            return
        job.tick()
    pytest.fail("small regression search exceeded 1000 cooperative ticks")


@pytest.mark.parametrize("grow,close", [((0, 1), (1, 0)), ((1, 0), (0, 1))])
@pytest.mark.parametrize("candidate_index", [0, 1])
def test_editor_keeps_both_asymmetric_closures_and_applies_each(grow, close, candidate_index):
    piece, bar, base = asymmetric_gap()
    catalog, stock = {"asymmetric": piece, "bar": bar}, {"asymmetric": 1, "bar": 2}
    result = solve({"asymmetric": 1}, catalog,
                   SolverConfig(min_pieces=0, max_pieces=1, max_nodes=10000, max_results=8),
                   base=base, grow_from=grow, close_onto=close)
    assert len(result.solutions) == 2
    a, b = (candidate.layout.placements[-1] for candidate in result.solutions)
    assert {a.port_pose(i) for i in (0, 1)} == {b.port_pose(i) for i in (0, 1)}
    assert physical_key(result.solutions[0].layout, base) != physical_key(
        result.solutions[1].layout, base)
    session = Session(catalog=catalog, history=[base], inventory=stock)
    before = session.snapshot()
    job = SearchJob(session, {"grow": list(grow), "close": list(close), "max_pieces": 1})
    try:
        finish(job)
        assert len(job.solutions) == 2
        assert {physical_key(s.layout, base) for s in job.solutions} == {
            physical_key(s.layout, base) for s in result.solutions}
        assert session.snapshot() == before
        candidate = job.solutions[candidate_index]
        layout = candidate.layout
        assert candidate.exact and not layout.joint_issues()
        assert not _solution_overlaps(layout, 0, 120.0, 8.0)
        assert layout.placements[:len(base)] == base.placements
        # The two outer ends intentionally remain open: this closes the selected gap.
        assert grow not in layout.connectable_ends() and close not in layout.connectable_ends()
        job.publish(session)
        session.apply_candidate(candidate_index, revision=session.revision)
        assert layout_to_dict(session.layout) == layout_to_dict(layout)
        session.undo()
        assert session.snapshot() == before
    finally:
        job.close()


@pytest.mark.parametrize("pid", ["straight", "crossing"])
def test_editor_still_deduplicates_true_reversals(pid):
    piece = default_catalog()[pid]
    a = Placement(piece, ORIGIN)
    # Rotate/translate a fresh copy so its opposite port sits at the original entry.
    b = Placement(piece, piece.frame_for(1, a.port_pose(0).reversed()))
    assert physical_key(Layout((a,)), Layout()) == physical_key(Layout((b,)), Layout())


def test_editor_identity_keeps_connector_kinds_and_multiplicity():
    piece = default_catalog()["straight"]
    altered = replace(piece, ports=(replace(piece.ports[0], kind="arch_foot"), piece.ports[1]))
    a, b = Placement(piece, ORIGIN), Placement(altered, ORIGIN)
    assert physical_key(Layout((a,)), Layout()) != physical_key(Layout((b,)), Layout())
    assert physical_key(Layout((a, a)), Layout()) != physical_key(Layout((a,)), Layout())
