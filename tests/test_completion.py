"""Completion mode: close a partially built layout using spare pieces."""

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.collision import DEFAULT_CLEARANCE
from duplotrain.geometry import ORIGIN
from duplotrain.gui import Session
from duplotrain.layout import Layout, Placement, build_chain
from duplotrain.pieces import parse_piece
from duplotrain.solver import SolverConfig, _solution_overlaps, solve
from tests.editor_support import complete

LEFT = (0, 1)


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


@pytest.fixture()
def half_circle(catalog):
    return build_chain([(catalog["curve"], *LEFT)] * 6)


def test_complete_half_circle_with_six_curves(catalog, half_circle):
    result = solve(
        {"curve": 6},
        catalog,
        SolverConfig(min_pieces=1),
        base=half_circle,
    )
    assert len(result.solutions) == 1
    sol = result.solutions[0]
    assert sol.exact
    assert sol.layout.is_closed
    assert len(sol.layout) == 12  # 6 base + 6 grown
    assert sol.piece_count == 12


def test_completions_enumerate_straight_variants(catalog, half_circle):
    """With 6 curves + 4 straights spare there are exactly three ways to close."""
    result = solve(
        {"curve": 6, "straight": 4},
        catalog,
        SolverConfig(min_pieces=1, max_results=100),
        base=half_circle,
    )
    assert all(s.exact and s.layout.is_closed for s in result.solutions)
    grown_counts = sorted(
        sum(n for pid, n in s.layout.piece_counts.items()) for s in result.solutions
    )
    # circle (6 curves), oval-let (6c+2s), full oval (6c+4s)
    assert grown_counts == [12, 14, 16]


def test_completion_respects_base_collisions(catalog):
    """Growing must not plough through the base track: with enough curves a walk
    can loop back across the base's own body, and no such completion is reported."""
    base = build_chain([(catalog["curve"], *LEFT)] * 6)
    result = solve({"curve": 18}, catalog, SolverConfig(min_pieces=1, max_results=200),
                   base=base)
    # A search blind to collisions finds 87 closures here, six of them crossing
    # the base; the independent audit agrees with the search's own field.
    assert result.stats.complete and len(result.solutions) == 81
    assert not any(_solution_overlaps(s.layout, len(base), DEFAULT_CLEARANCE, 8.0)
                   for s in result.solutions)
    # The search refuses those six itself, as it places their pieces; the
    # final audit of each closure finds nothing left to drop.
    assert result.stats.pruned_collision and not result.stats.dropped_overlap


def test_completion_around_a_switch_leaves_its_branch_open(catalog):
    switch = catalog["switch"]
    base = build_chain([(switch, 0, 1)])  # stem in at origin, left branch onward
    result = solve(
        {"curve": 11},
        catalog,
        SolverConfig(min_pieces=1),
        base=base,
        grow_from=(0, 1),  # continue from the left branch
        close_onto=(0, 0),  # come back around to the stem
    )
    assert result.solutions
    sol = result.solutions[0]
    assert sol.exact
    assert len(sol.layout) == 12
    assert sol.layout.open_ends() == [(0, 2)]  # only the right branch dangles


def test_completion_rejects_already_mating_ends(catalog):
    layout = build_chain([(catalog["curve"], *LEFT)] * 12)  # full circle, unjoined
    with pytest.raises(ValueError, match="already mate"):
        solve({"curve": 1}, catalog, SolverConfig(min_pieces=1), base=layout)


def test_completion_needs_two_open_ends(catalog):
    layout = build_chain([(catalog["curve"], *LEFT)] * 12)
    closed = layout.join(layout.open_ends()[1], layout.open_ends()[0])
    with pytest.raises(ValueError, match="two distinct open ends"):
        solve({"curve": 1}, catalog, SolverConfig(min_pieces=1), base=closed)


def test_loop_mode_rejects_stray_end_arguments(catalog):
    with pytest.raises(ValueError, match="only make sense"):
        solve({"curve": 12}, catalog, grow_from=(0, 0))


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


def test_editor_can_apply_a_completion_without_new_inventory():
    catalog, base, grow, close = preplaced_crossing_gap()
    session = Session(catalog=catalog, history=[base], inventory={})
    job = complete(session, grow, close, max_results=10)
    assert len(job.solutions) == 1 and job.complete
    session.apply_candidate(0, revision=session.revision)
    assert session.layout.placements == base.placements
    assert session.layout.links[(1, 1)] == (0, 0)
    assert session.layout.links[(0, 1)] == (2, 0)
