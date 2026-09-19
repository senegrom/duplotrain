"""The reported 59-piece gap must be solved, not merely accept its supplied witness."""

import json
from dataclasses import replace
from pathlib import Path

import pytest

import duplotrain.bridge_completion as bridge_module
import duplotrain.editor as editor
from duplotrain import build_chain, default_catalog
from duplotrain.bridge_completion import _bridge, _expand, bridge_completion
from duplotrain.geometry import ORIGIN
from duplotrain.gui import Session, dispatch_session
from duplotrain.layout import layout_from_dict, layout_to_dict
from duplotrain.solver import Solution, SolveResult, SolveStats, _solution_overlaps

FIXTURES = Path(__file__).parent / "fixtures"


def load(name):
    return layout_from_dict(json.loads((FIXTURES / name).read_text()), default_catalog())


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


def test_supplied_bridge_witness_is_valid_and_preserves_the_gap():
    base, witness = load("bridge-gap.json"), load("bridge-completed.json")
    assert len(base) == 59 and len(witness) == 83
    assert base.connectable_ends() == [(23, 1), (25, 0)]
    assert_extension(base, witness)


@pytest.mark.parametrize("unlimited", [False, True])
@pytest.mark.parametrize("reversing", [False, True])
def test_editor_finds_a_standard_bridge_without_being_given_the_witness(unlimited, reversing):
    base = load("bridge-gap.json")
    # Only the stock counts are supplied; no coordinates or recipe of the answer.
    spare = {"curve": 16, "straight": 4, "ramp": 2, "span": 2}
    owned = {pid: base.piece_counts.get(pid, 0) + spare.get(pid, 0)
             for pid in default_catalog()}
    session = Session(history=[base], inventory=owned, unlimited=unlimited)
    remaining = session.remaining()
    progress = []
    result = dispatch_session(session, "/api/solve", {
        "revision": 0, "max_pieces": 26, "max_results": 8, "reversing": reversing,
    }, progress=progress.append)
    assert result["found"] > 0 and result["stop_reason"] == "bridge_search"
    assert result["searched"] <= 275_002
    assert not result["complete"]
    assert progress == sorted(progress) and progress
    for candidate in session.candidates:
        assert len(candidate.layout) == 83
        assert_extension(base, candidate.layout, remaining)
    session.apply_candidate(0, revision=result["revision"])
    assert_extension(base, session.layout, remaining)
    session.undo()
    assert session.layout == base


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
def test_inapplicable_macro_stage_defers_without_searching(monkeypatch, problem):
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)])
    stock = {"ramp": 2, "span": 2}
    cap = 26
    if problem == "one_ramp":
        stock["ramp"] = 1
    elif problem == "one_span":
        stock["span"] = 1
    elif problem == "depth":
        cap = 3
    elif problem == "elevated":
        base = build_chain([(catalog["ramp"], 0, 1)])
    else:
        catalog["ramp"] = replace(catalog["ramp"], underpass=False)

    def unexpected(*args, **kwargs):
        pytest.fail("inapplicable stage must not run a search")

    monkeypatch.setattr(bridge_module, "solve", unexpected)
    assert bridge_completion(base, catalog, stock, (0, 1), (0, 0),
                             max_pieces=cap, max_results=1, max_nodes=10) is None


def test_macro_uses_real_piece_and_stock_limits_and_reaudits(monkeypatch):
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)])
    calls = []
    witness = load("bridge-completed.json")

    def search(stock, pieces, config, **kwargs):
        calls.append((stock, config))
        return SolveResult([Solution(witness, (), 0, True, 0, ())], SolveStats())

    monkeypatch.setattr(bridge_module, "solve", search)
    monkeypatch.setattr(bridge_module, "_expand", lambda *args: witness)
    # Use the fixture's actual base and inventory; independently reject the expanded audit.
    base = load("bridge-gap.json")
    remaining = {"curve": 16, "straight": 4, "ramp": 2, "span": 2}
    monkeypatch.setattr(bridge_module, "_OverlapAudit", type(
        "RejectAll", (bridge_module._OverlapAudit,), {"overlaps": lambda self, layout: True}))
    result = bridge_completion(base, catalog, remaining, (25, 0), (23, 1),
                               max_pieces=24, max_results=1, max_nodes=1234)
    stock, config = calls[0]
    assert config.max_pieces == 21 and config.max_nodes == 1234
    assert stock == {"curve": 16, "straight": 4, "_completion_bridge": 1}
    assert result.solutions == [] and not result.stats.complete


@pytest.mark.parametrize("bad", [True, False, 0, 17, -1, 1.5, "2", None])
def test_invalid_search_effort_does_not_mutate_the_session(bad):
    session = Session()
    before = session.snapshot(), session.revision
    with pytest.raises(ValueError, match="search effort"):
        dispatch_session(session, "/api/solve", {"revision": 0, "search_effort": bad})
    assert (session.snapshot(), session.revision) == before


def test_search_effort_scales_all_three_stages(monkeypatch):
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)])
    calls = []

    def search(stock, pieces, config, **kwargs):
        calls.append(config.max_nodes)
        return SolveResult([], SolveStats(complete=False, stop_reason="node_limit"))

    def bridges(*args, **kwargs):
        calls.append(kwargs["max_nodes"])
        return SolveResult([], SolveStats())

    monkeypatch.setattr(Session, "_arc_closures", lambda *args: [])
    monkeypatch.setattr(editor, "solve", search)
    monkeypatch.setattr(editor, "bridge_completion", bridges)
    for effort in (1, 2, 16):
        session = Session(history=[base], unlimited=True)
        calls.clear()
        result = dispatch_session(session, "/api/solve", {
            "revision": 0, "search_effort": effort,
        })
        assert calls == [25_000 * effort, 250_000 * effort, 60_000 * effort]
        assert result["search_effort"] == effort


def test_two_ended_search_keeps_the_reported_gap_below_fifty_thousand_nodes():
    base = load("bridge-gap.json")
    session = Session(history=[base], unlimited=True)
    outcome = session.solve_gap(None, None, 0, 8)
    assert len(session.candidates) == 8
    assert outcome["searched"] < 50_000
    for candidate in session.candidates:
        assert_extension(base, candidate.layout, session.remaining())


def test_expanded_bridge_rejections_do_not_fill_result_slots(monkeypatch):
    base = load("bridge-gap.json")
    catalog = default_catalog()
    attempts = 0

    # Only the bridge stage's own auditor rejects; the core solver keeps its own.
    class RejectFirst(bridge_module._OverlapAudit):
        def overlaps(self, layout):
            nonlocal attempts
            attempts += 1
            return attempts == 1 or super().overlaps(layout)

    monkeypatch.setattr(bridge_module, "_OverlapAudit", RejectFirst)
    result = bridge_completion(base, catalog, {"curve": 16, "straight": 4, "ramp": 2, "span": 2},
                               (23, 1), (25, 0), max_pieces=26, max_results=1, max_nodes=250_000)
    assert len(result.solutions) == 1 and attempts >= 2
    assert result.stats.dropped_filter >= 1
    assert_extension(base, result.solutions[0].layout)


def test_bridge_stage_audits_only_the_joints_it_adds():
    from duplotrain.geometry import Pose
    from duplotrain.layout import Layout, Placement

    base, catalog = load("bridge-gap.json"), default_catalog()
    # A deliberate forced fit inside the base: one curve sits a millimetre off.
    p = base.placements[40]
    shifted = Placement(p.piece, Pose.make(p.frame.x + 1, p.frame.y, p.frame.z, p.frame.heading))
    base = Layout(base.placements[:40] + (shifted,) + base.placements[41:],
                  dict(base.links), base.accessories)
    forced = base.joint_issues()
    assert [issue["problems"] for issue in forced] == [["planar gap"]] * 2
    result = bridge_completion(base, catalog, {"curve": 16, "straight": 4, "ramp": 2, "span": 2},
                               (23, 1), (25, 0), max_pieces=26, max_results=1, max_nodes=250_000)
    assert len(result.solutions) == 1
    completed = result.solutions[0].layout
    assert completed.placements[:len(base)] == base.placements
    assert completed.is_closed and completed.joint_issues(since=len(base)) == []
    assert completed.joint_issues() == forced  # the base's own forced fits, nothing new
    assert not _solution_overlaps(completed, 0, 120.0, 8.0)
