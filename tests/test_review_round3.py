"""Additional regressions for duplotrain main at 041b7066.

Run from a checkout with:
    PYTHONPATH=src python -m pytest /path/to/test_review_round3.py -v

These pin the corrected behaviour and failed on the reviewed commit.
No repository source is patched or replaced by these tests.
"""

from dataclasses import replace

import pytest

from duplotrain import (
    ORIGIN,
    Layout,
    Placement,
    SolverConfig,
    build_chain,
    classify,
    default_catalog,
    drive,
    layout_to_dict,
    parse_piece,
    solve,
)
from duplotrain.gui import Session, dispatch_session
from duplotrain.solver import _solution_overlaps


def exact_oval():
    catalog = default_catalog()
    half = [(catalog["straight"], 0, 1)] + [(catalog["curve"], 0, 1)] * 6
    layout = build_chain(half * 2)
    return layout.join(*layout.connectable_ends())


def oval_with_return_stop(face):
    """Both stone placements are accepted by the shared editor API."""
    session = Session()
    dispatch_session(session, "/api/import", {
        "revision": session.revision, "data": layout_to_dict(exact_oval()),
    })
    for sid, position in (("stone_direction", None), ("stone_stop", face)):
        dispatch_session(session, "/api/stone", {
            "revision": session.revision,
            "placement": 0, "id": sid, "at_port": position,
        })
    layout = session.layout
    assert layout.is_closed and not layout.joint_issues()
    assert not _solution_overlaps(layout, 0, 120.0, 8.0)
    return layout


@pytest.mark.parametrize("face", [0, 1])
def test_returning_from_mid_piece_reversal_hits_the_face_stop(face):
    layout = oval_with_return_stop(face)
    # Starting away from the face is silent; returning toward it after the green
    # stone must fire the red stone before the train leaves that same connector.
    assert drive(layout, start=(0, face)).outcome == "stopped"


@pytest.mark.parametrize("face", [0, 1])
def test_reachable_return_stop_prevents_a_perfect_verdict(face):
    layout = oval_with_return_stop(face)
    verdict = classify(layout)
    assert not verdict.perfectly_looping
    assert not verdict.looping


def crossing_completion():
    """An exactly closed four-piece eight, with two upper pieces as the base.

    The crossing is the stock 60-degree crossing. The two lobe types are valid
    custom arcs of radius 64*sqrt(3) mm; all widths are the stock 64 mm.
    """
    catalog = dict(default_catalog())
    for pid, degrees in (("upper", 150), ("lower", -300)):
        catalog[pid] = parse_piece({
            "id": pid, "width": 64,
            "paths": [{"segments": [{
                "type": "arc", "radius": {"alg": [0, 0, 64, 0]},
                "degrees": degrees,
            }]}],
        })
    crossing = Placement(catalog["crossing"], ORIGIN)
    base = build_chain(
        [(catalog["upper"], 0, 1)] * 2, start=crossing.port_pose(3)
    )
    grow, close = (1, 1), (0, 0)
    witness, cross = base.attach(catalog["crossing"], 0, grow)
    witness, lower = witness.attach(catalog["lower"], 0, (cross, 1))
    witness = witness.join((lower, 1), (cross, 2)).join((cross, 3), close)
    assert witness.is_closed and not witness.joint_issues()
    assert not _solution_overlaps(witness, 0, 120.0, 8.0)
    return catalog, base, grow, close, witness


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_completion_retains_crossing_whose_other_port_joins_target_later(engine):
    catalog, base, grow, close, witness = crossing_completion()
    result = solve(
        {"crossing": 1, "lower": 1}, catalog,
        SolverConfig(min_pieces=1, max_results=100, max_nodes=100_000, engine=engine),
        base=base, grow_from=grow, close_onto=close,
    )
    assert result.stats.complete and result.stats.stop_reason == "exhausted"
    assert result.solutions, "exact, overlap-audited completion was incorrectly pruned"
    assert any(s.exact and s.layout.piece_counts == witness.piece_counts
               and s.layout.is_closed for s in result.solutions)


def preplaced_crossing_gap():
    catalog = default_catalog()
    base, cross = Layout().with_piece(catalog["crossing"], ORIGIN)
    base, left = base.attach(catalog["straight"], 1, (cross, 0))
    base, right = base.attach(catalog["straight"], 0, (cross, 1))
    # The components are already positioned; only the two joints need recording.
    # Disconnected bases are allowed (e.g. completion searches with obstacles).
    base = Layout(base.placements, {})
    grow, close = (left, 1), (right, 0)
    witness = base.join(grow, (cross, 0)).join((cross, 1), close)
    assert not witness.joint_issues()
    assert not _solution_overlaps(witness, 0, 120.0, 8.0)
    assert list(witness.walk(start=(left, 0))) == [
        (left, 0, 1), (cross, 0, 1), (right, 0, 1),
    ]
    return catalog, base, grow, close


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("inventory", [{}, {"curve": 1}])
def test_zero_new_pieces_can_complete_via_an_existing_crossing(engine, inventory):
    catalog, base, grow, close = preplaced_crossing_gap()
    result = solve(
        inventory, catalog, SolverConfig(min_pieces=0, max_pieces=1, engine=engine),
        base=base, grow_from=grow, close_onto=close,
    )
    assert result.stats.complete
    assert result.solutions, "min_pieces=0 must permit an existing-junction-only completion"
    assert any(s.exact and len(s.layout) == len(base) for s in result.solutions)


def test_removing_a_positioned_stone_preserves_the_other_same_colour_stone():
    catalog = default_catalog()
    layout = build_chain([(catalog["straight"], 0, 1)])
    layout = layout.with_accessory(0, "stone_lights", at_port=0)
    layout = layout.with_accessory(0, "stone_lights", at_port=1)
    session = Session()
    session.set_inventory({"stone_lights": 2})
    state = dispatch_session(session, "/api/import", {
        "revision": session.revision, "data": layout_to_dict(layout),
    })
    assert state["layout"]["placements"][0]["stone_marks"] == [
        {"id": "stone_lights", "at": 0}, {"id": "stone_lights", "at": 1},
    ]
    dispatch_session(session, "/api/stone", {
        "revision": session.revision, "placement": 0,
        "id": "stone_lights", "at_port": 0,
    })
    assert session.layout.accessories == ((0, "stone_lights", 1),)


# Additional boundary cases for both arithmetic engines.

@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_future_joint_exemption_does_not_ignore_unrelated_obstacle(engine):
    catalog, base, grow, close, witness = crossing_completion()
    base, _ = base.with_piece(catalog["straight"], ORIGIN)
    blocked, _ = witness.with_piece(catalog["straight"], ORIGIN)
    assert _solution_overlaps(blocked, 0, 120, 8)
    result = solve(
        {"crossing": 1, "lower": 1}, catalog,
        SolverConfig(min_pieces=1, engine=engine, max_nodes=100_000),
        base=base, grow_from=grow, close_onto=close,
    )
    assert not result.solutions
    assert result.stats.complete and result.stats.pruned_collision


@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_sealed_crossing_branch_is_not_a_future_joint(engine):
    catalog, base, grow, close, _ = crossing_completion()
    catalog["crossing"] = replace(catalog["crossing"], sealed=frozenset({3}))
    result = solve(
        {"crossing": 1, "lower": 1}, catalog,
        SolverConfig(min_pieces=1, engine=engine, max_nodes=100_000),
        base=base, grow_from=grow, close_onto=close,
    )
    assert not result.solutions and result.stats.complete


@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_zero_piece_contour_can_transit_multiple_preplaced_junctions(engine):
    catalog = default_catalog()
    base, a = Layout().with_piece(catalog["crossing"], ORIGIN)
    base, b = base.attach(catalog["crossing"], 0, (a, 1))
    base, left = base.attach(catalog["straight"], 1, (a, 0))
    base, right = base.attach(catalog["straight"], 0, (b, 1))
    base = Layout(base.placements, {})
    result = solve(
        {}, catalog, SolverConfig(min_pieces=0, engine=engine),
        base=base, grow_from=(left, 1), close_onto=(right, 0),
    )
    assert len(result.solutions) == 1
    solution = result.solutions[0]
    assert solution.exact and len(solution.steps) == 2
    assert solution.layout.placements == base.placements
    assert len(solution.layout.links) == 6
    assert not solution.layout.joint_issues()
    assert not _solution_overlaps(solution.layout, 0, 120, 8)
    assert result.stats.complete and result.stats.max_pieces_searched == 0


@pytest.mark.parametrize("engine", ["field", "lattice"])
@pytest.mark.parametrize("use_all,inventory,minimum,expected", [
    (True, {}, 0, True), (True, {"curve": 1}, 0, False),
    (False, {}, 1, False), (False, {"curve": 1}, 1, False),
])
def test_zero_piece_completion_respects_inventory_and_minimum(engine, use_all, inventory,
                                                            minimum, expected):
    catalog, base, grow, close = preplaced_crossing_gap()
    result = solve(
        inventory, catalog,
        SolverConfig(min_pieces=minimum, use_all_pieces=use_all, engine=engine),
        base=base, grow_from=grow, close_onto=close,
    )
    assert bool(result.solutions) is expected
    assert result.stats.complete


@pytest.mark.parametrize("engine", ["field", "lattice"])
@pytest.mark.parametrize("limit,reason", [("nodes", "node_limit"), ("results", "result_limit")])
def test_zero_piece_contour_retains_limit_reporting(engine, limit, reason):
    catalog, base, grow, close = preplaced_crossing_gap()
    config = SolverConfig(min_pieces=0, engine=engine,
                          max_nodes=1 if limit == "nodes" else 100,
                          max_results=1 if limit == "results" else 100)
    result = solve({}, catalog, config, base=base, grow_from=grow, close_onto=close)
    assert not result.stats.complete and result.stats.stop_reason == reason
    assert bool(result.solutions) is (limit == "results")


@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_contour_zero_does_not_emit_an_empty_fresh_loop(engine):
    result = solve({}, default_catalog(), SolverConfig(min_pieces=0, engine=engine))
    assert not result.solutions and result.stats.complete


def test_editor_can_apply_a_completion_without_new_inventory():
    catalog, base, grow, close = preplaced_crossing_gap()
    session = Session(catalog=catalog, history=[base], inventory={})
    result = session.solve_gap(grow, close, 0.0, 10)
    assert result["found"] == 1 and result["complete"]
    session.apply_candidate(0, revision=session.revision)
    assert session.layout.placements == base.placements
    assert session.layout.links[(1, 1)] == (0, 0)
    assert session.layout.links[(0, 1)] == (2, 0)
