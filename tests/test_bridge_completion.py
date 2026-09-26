"""The reported 59-piece gap must be solved, not merely accept its supplied witness."""

import json
from dataclasses import replace
from pathlib import Path

import pytest

import duplotrain.editor_search as editor_search
from duplotrain import build_chain, default_catalog
from duplotrain.bridge_completion import _BRIDGE_ID, _bridge, _expand
from duplotrain.editor_search import PairSearch, SearchJob, physical_key, search_options
from duplotrain.geometry import ORIGIN
from duplotrain.gui import Session, dispatch_session
from duplotrain.layout import layout_from_dict, layout_to_dict
from duplotrain.solver import Solution, _solution_overlaps
from tests.editor_support import complete

FIXTURES = Path(__file__).parent / "fixtures"
SPARE = {"curve": 16, "straight": 4, "ramp": 2, "span": 2}


def load(name):
    return layout_from_dict(json.loads((FIXTURES / name).read_text()), default_catalog())


def owned(base):
    """The fixture's own pieces plus the spare box; no coordinates or recipe."""
    return {pid: base.piece_counts.get(pid, 0) + SPARE.get(pid, 0) for pid in default_catalog()}


def assert_extension(base, completed, remaining=None, max_pieces=26):
    assert completed.placements[:len(base)] == base.placements
    assert all(completed.links[a] == b for a, b in base.links.items())
    assert completed.accessories == base.accessories
    assert completed.is_closed and not completed.joint_issues()
    assert not _solution_overlaps(completed, 0, 120.0, 8.0)
    assert len(completed) - len(base) <= max_pieces
    assert all(p.frame.z == ORIGIN.z for p in completed if p.piece.id != "span")
    if remaining is not None:
        assert all(n - base.piece_counts.get(pid, 0) <= remaining.get(pid, 0)
                   for pid, n in completed.piece_counts.items())
    # No search-only macro may escape through export or candidate application.
    assert layout_from_dict(layout_to_dict(completed), default_catalog()) == completed


def pair_search(base, catalog, stock, grow, close, depth=26, effort=1):
    return PairSearch(base, catalog, stock, grow, close, depth, effort, 0, False,
                      search_options(None, catalog))


def test_supplied_bridge_witness_is_valid_and_preserves_the_gap():
    base, witness = load("bridge-gap.json"), load("bridge-completed.json")
    assert len(base) == 59 and len(witness) == 83
    assert base.connectable_ends() == [(23, 1), (25, 0)]
    assert_extension(base, witness)


@pytest.mark.parametrize("unlimited", [False, True])
@pytest.mark.parametrize("reversing", [False, True])
def test_editor_finds_a_standard_bridge_without_being_given_the_witness(unlimited, reversing):
    base = load("bridge-gap.json")
    session = Session(history=[base], inventory=owned(base), unlimited=unlimited)
    remaining = session.remaining()
    job = complete(session, max_pieces=26, max_results=8, reversing=reversing)
    assert len(job.solutions) == 8 and job.stage == "standard bridge"
    assert job.nodes < 2_000 and not job.complete
    for candidate in session.candidates:
        assert candidate.signature[0] == "standard_bridge" and len(candidate.layout) == 83
        assert_extension(base, candidate.layout, remaining)
    session.apply_candidate(0, revision=session.revision)
    assert_extension(base, session.layout, remaining)
    session.undo()
    assert session.layout == base


def test_either_end_closes_the_reported_gap_with_the_same_tracks():
    base = load("bridge-gap.json")
    found = []
    for grow, close in (((25, 0), (23, 1)), ((23, 1), (25, 0))):
        job = complete(Session(history=[base], inventory=owned(base)), grow, close)
        # The plain stage from (25, 0) could wander for tens of thousands of
        # nodes; the other end proves it impossible in about a hundred, and the
        # bridge stage then starts from that end.
        assert len(job.solutions) == 8 and job.stage == "standard bridge"
        assert job.nodes < 3_000
        found.append({physical_key(s.layout, base) for s in job.solutions})
    assert found[0] == found[1]


def test_macro_expands_in_both_directions_and_keeps_action_stones():
    catalog = default_catalog()
    macro, parts = _bridge(catalog)
    for entry in (0, 1):
        composed = build_chain([
            (catalog["straight"], 0, 1), (macro, entry, 1 - entry),
            (catalog["straight"], 0, 1),
        ]).with_accessory(2, "stop")
        expanded = _expand(composed, parts)
        assert len(expanded) == 6
        assert not expanded.joint_issues()
        assert expanded.accessories == ((5, "stop"),)
        assert expanded.pose_of((0, 0)) == composed.pose_of((0, 0))
        assert expanded.pose_of((5, 1)) == composed.pose_of((2, 1))
        assert not _solution_overlaps(expanded, 0, 120, 8)


@pytest.mark.parametrize("problem", ["one_ramp", "one_span", "depth", "elevated", "custom"])
def test_inapplicable_macro_stage_never_searches(problem):
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)])
    stock = {"ramp": 2, "span": 2}
    depth = 26
    if problem == "one_ramp":
        stock["ramp"] = 1
    elif problem == "one_span":
        stock["span"] = 1
    elif problem == "depth":
        depth = 3
    elif problem == "elevated":
        base = build_chain([(catalog["ramp"], 0, 1)])
    else:
        catalog["ramp"] = replace(catalog["ramp"], underpass=False)
    pool = pair_search(base, catalog, stock, (0, 1), (0, 0), depth)
    try:
        # A macro needs two ramps, two spans, four free slots, floor-level ends
        # and the standard geometry: otherwise the stage is absent, or blocked
        # when only the depth is short.
        bridge = [c for c in pool.cursors if c.stage == "standard bridge"]
        assert bridge == [] if problem != "depth" else bridge and all(c.blocked for c in bridge)
    finally:
        pool.close()


def test_macro_stage_counts_real_pieces_and_stock_and_reaudits(monkeypatch):
    catalog, base = default_catalog(), load("bridge-gap.json")
    calls = []
    real = editor_search.solve_steps

    def recorded(inventory, pieces, config, **kwargs):
        calls.append((inventory, config, kwargs["limits"]))
        return real(inventory, pieces, config, **kwargs)

    monkeypatch.setattr(editor_search, "solve_steps", recorded)
    pool = pair_search(base, catalog, dict(SPARE), (25, 0), (23, 1), depth=24)
    try:
        stage = [call for call in calls if _BRIDGE_ID in call[0]]
        assert len(stage) == 2  # both directions of an exact stage
        for inventory, config, limits in stage:
            # One search move stands for four real pieces: three slots are reserved.
            assert inventory == {"curve": 16, "straight": 4, _BRIDGE_ID: 1}
            assert limits.max_pieces == 21
            assert config.max_nodes == 250_000
        # The expanded macro is audited against the base before it can count.
        witness = load("bridge-completed.json")
        monkeypatch.setattr(editor_search, "_expand", lambda *args: witness)
        accept = stage[0][1].solution_filter
        candidate = Solution(witness, (), 0, True, 0, ())
        assert accept(candidate)
        pool.audit = type("RejectAll", (), {"overlaps": lambda self, layout: True})()
        assert not accept(candidate)
    finally:
        pool.close()


@pytest.mark.parametrize("bad", [True, False, 0, 17, -1, 1.5, "2", None])
def test_invalid_search_effort_does_not_mutate_the_session(bad):
    session = Session()
    before = session.snapshot(), session.revision
    with pytest.raises(ValueError, match="search effort"):
        dispatch_session(session, "/api/search/start", {"revision": 0, "search_effort": bad})
    assert (session.snapshot(), session.revision) == before
    assert session._interactive_job is None


def test_search_effort_scales_all_three_stages():
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)])
    for effort in (1, 2, 16):
        session = Session(history=[base], unlimited=True)
        job = SearchJob(session, {"search_effort": effort})
        try:
            assert {c.stage: c.cap for c in job.pool.cursors} == {
                "plain track": 25_000 * effort, "standard bridge": 250_000 * effort,
                "full inventory": 60_000 * effort}
            assert job.response(session, {})["search_effort"] == effort
        finally:
            job.close()


def test_a_rejected_bridge_expansion_does_not_stop_the_stage(monkeypatch):
    base = load("bridge-gap.json")
    attempts = 0

    # Only the bridge stage's own auditor rejects; the core solver keeps its own.
    class RejectFirst(editor_search._OverlapAudit):
        def overlaps(self, layout):
            nonlocal attempts
            attempts += 1
            return attempts == 1 or super().overlaps(layout)

    monkeypatch.setattr(editor_search, "_OverlapAudit", RejectFirst)
    job = complete(Session(history=[base], inventory=owned(base)), max_results=1)
    assert len(job.solutions) == 1 and attempts >= 2
    assert_extension(base, job.solutions[0].layout)


def test_bridge_stage_audits_only_the_joints_it_adds():
    from duplotrain.geometry import Pose
    from duplotrain.layout import Layout, Placement

    base = load("bridge-gap.json")
    # A deliberate forced fit inside the base: one curve sits a millimetre off.
    p = base.placements[40]
    shifted = Placement(p.piece, Pose.make(p.frame.x + 1, p.frame.y, p.frame.z, p.frame.heading))
    base = Layout(base.placements[:40] + (shifted,) + base.placements[41:],
                  dict(base.links), base.accessories)
    forced = base.joint_issues()
    assert [issue["problems"] for issue in forced] == [["planar gap"]] * 2
    job = complete(Session(history=[base], inventory=owned(base)), (23, 1), (25, 0),
                   max_results=1)
    assert len(job.solutions) == 1
    completed = job.solutions[0].layout
    assert completed.placements[:len(base)] == base.placements
    assert completed.is_closed
    assert completed.joint_issues() == forced  # the base's own forced fits, nothing new
    assert not _solution_overlaps(completed, 0, 120.0, 8.0)


def test_the_templates_and_the_bridge_stage_share_one_overlap_auditor(monkeypatch):
    import duplotrain.editor as editor_module

    built = []

    class Counting(editor_search._OverlapAudit):
        def __init__(self, *args, **kwargs):
            built.append(args[0])
            super().__init__(*args, **kwargs)

    monkeypatch.setattr(editor_search, "_OverlapAudit", Counting)
    monkeypatch.setattr(editor_module, "_OverlapAudit", Counting)
    base = load("bridge-gap.json")
    job = complete(Session(history=[base], inventory=owned(base)), max_results=50)
    try:
        job.more(harder=True)  # the templates come again, at a greater depth
        while job.status == "running":
            job.tick()
    finally:
        job.close()
    assert len(built) == 1 and built[0] is base
