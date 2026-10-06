"""Completion mode: close a partially built layout using spare pieces."""

from fractions import Fraction

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
    assert sol.layout.connectable_ends() == [(0, 2)]  # only the right branch dangles


def test_completion_rejects_already_mating_ends(catalog):
    layout = build_chain([(catalog["curve"], *LEFT)] * 12)  # full circle, unjoined
    with pytest.raises(ValueError, match="already mate"):
        solve({"curve": 1}, catalog, SolverConfig(min_pieces=1), base=layout)


def test_completion_needs_two_open_ends(catalog):
    layout = build_chain([(catalog["curve"], *LEFT)] * 12)
    closed = layout.join(layout.connectable_ends()[1], layout.connectable_ends()[0])
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


def test_a_completion_never_runs_under_the_floor(catalog):
    # A 1024 mm gap in floor track: a bridge climbs over it and straights fill it,
    # but a bridge hung under the floor, its arches down from the floor track,
    # is no layout.
    base = build_chain([(catalog["straight"], 0, 1)])
    base, far = base.with_piece(catalog["straight"], ORIGIN.then(1152, 0, 0, 0))
    result = solve({"straight": 8, "ramp": 2, "span": 2}, catalog,
                   SolverConfig(min_pieces=1, max_results=50), base=base,
                   grow_from=(0, 1), close_onto=(far, 0))
    lowest = [min(float(placement.port_pose(port).z) for placement in solution.layout
                  for port in range(len(placement.piece.ports)))
              for solution in result.solutions]
    assert result.stats.complete and lowest and min(lowest) == 0.0
    assert any("span" in solution.layout.piece_counts for solution in result.solutions)


def test_an_open_arch_foot_stands_a_ramp_above_the_floor(catalog):
    # An arch placed first: its foot rests on a ramp's top, never on the floor, so
    # the ramp that carries it stands a ramp's rise lower, and the loop closes.
    base = build_chain([(catalog["span"], 0, 1)] + [(catalog["curve"], 0, 1)] * 6)
    assert base.floor() == 0 and float(base.floor(catalog.values())) == pytest.approx(-57.6)
    for engine in ("field", "lattice"):
        result = solve({"curve": 6, "ramp": 2, "span": 1}, catalog,
                       SolverConfig(min_pieces=1, engine=engine), base=base,
                       grow_from=(6, 1), close_onto=(0, 0))
        assert result.stats.complete and len(result.solutions) == 1
        layout = result.solutions[0].layout
        assert layout.piece_counts == {"span": 2, "curve": 12, "ramp": 2}
        assert layout.is_closed and not layout.joint_issues()


def test_a_floor_off_the_height_lattice_holds_in_both_engines(catalog):
    # An imported file with a loose straight a fortieth of a millimetre low: the
    # lattice engine keeps that floor exactly as the field engine does.
    from duplotrain.geometry import Pose

    straight = catalog["straight"]
    base = build_chain([(straight, 0, 1)])
    base, far = base.with_piece(straight, ORIGIN.then(640, 0, 0, 0))
    base, _loose = base.with_piece(straight, Pose.make(0, 2000, Fraction(-1, 40), 0))
    for engine in ("field", "lattice"):
        result = solve({"straight": 4, "slope": 2}, catalog,
                       SolverConfig(min_pieces=1, engine=engine), base=base,
                       grow_from=(0, 1), close_onto=(far, 0))
        assert result.stats.engine == engine and len(result.solutions) == 2
        assert min(float(p.port_pose(port).z) for s in result.solutions for p in s.layout
                   for port in range(len(p.piece.ports))) == -0.025


def dipping(rise, piece_id="probe"):
    """A custom 256 mm piece with level ends whose track dips (or humps) by *rise*."""
    return parse_piece({"id": piece_id, "width": 40, "paths": [{"segments": [
        {"type": "ramp", "run": 128, "rise": str(rise)},
        {"type": "ramp", "run": 128, "rise": str(-rise)}]}]})


def floor_gap(probe, height=0):
    """A 256 mm gap between two straights at *height*; a straight elsewhere on the floor."""
    from duplotrain.geometry import Pose

    catalog = {**default_catalog(), "probe": probe}
    base = Layout([Placement(catalog["straight"], Pose.make(-128, 0, height)),
                   Placement(catalog["straight"], Pose.make(256, 0, height)),
                   Placement(catalog["straight"], Pose.make(0, 1000, 0))])
    return catalog, base


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("reverse", [False, True])
@pytest.mark.parametrize("height", [0, 80])
@pytest.mark.parametrize("rise", [-40, Fraction(-1, 10**12), Fraction(-1, 7), 40])
def test_no_track_of_an_added_piece_runs_under_the_floor(engine, reverse, height, rise):
    # Its ends are level, but the whole piece counts: a dip under the floor, however
    # slight or off the height lattice, is never placed; raised high enough, it is.
    catalog, base = floor_gap(dipping(rise), height)
    ends = [(0, 1), (1, 0)][::-1 if reverse else 1]
    result = solve({"probe": 1}, catalog,
                   SolverConfig(min_pieces=1, max_pieces=1, max_nodes=10_000, engine=engine),
                   base=base, grow_from=ends[0], close_onto=ends[1])
    assert result.stats.complete and len(result.solutions) == int(height + min(rise, 0) >= 0)
    for solution in result.solutions:
        assert not solution.layout.joint_issues()
        assert (solution.layout.placements[-1].frame.z + catalog["probe"].minimum_z).sign() >= 0


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_an_unused_lower_route_stays_above_the_floor_too(engine):
    # Entered by its upper route, the piece would set its lower one 40 mm under the
    # floor; entered by the lower route, it stands 40 mm higher, and fits.
    probe = parse_piece({"id": "probe", "width": 40, "paths": [
        {"segments": [{"type": "straight", "run": 256}]},
        {"start": {"y": 200, "z": -40}, "segments": [{"type": "straight", "run": 256}]}]})
    catalog, base = floor_gap(probe)
    result = solve({"probe": 1}, catalog,
                   SolverConfig(min_pieces=1, max_pieces=1, max_nodes=10_000, engine=engine),
                   base=base, grow_from=(0, 1), close_onto=(1, 0))
    assert len(result.solutions) == 2
    assert all(solution.steps[0].entry in (2, 3) for solution in result.solutions)


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("rise", [-40, -50])
def test_a_base_dipping_already_stands_on_its_dip(engine, rise):
    # The base holds a piece dipping 40 mm: it stands on that dip, so another as
    # deep fits beside it, and a deeper one does not.
    from duplotrain.geometry import Pose

    base_dip = dipping(-40, "dip")
    catalog = {**default_catalog(), "dip": base_dip, "probe": dipping(rise)}
    base = Layout([Placement(catalog["straight"], Pose.make(-128, 0, 0)),
                   Placement(base_dip, Pose.make(0, 0, 0)),
                   Placement(catalog["straight"], Pose.make(512, 0, 0))]).join((0, 1), (1, 0))
    assert base.floor(catalog.values()) == -40
    result = solve({"probe": 1}, catalog,
                   SolverConfig(min_pieces=1, max_pieces=1, max_nodes=10_000, engine=engine),
                   base=base, grow_from=(1, 1), close_onto=(2, 0))
    assert len(result.solutions) == int(rise == -40)


def test_a_ramps_top_does_not_pass_through_a_switch_it_meets(catalog):
    ramp, switch = catalog["ramp"], catalog["switch"]
    base, _ = Layout().with_piece(ramp, ORIGIN)
    base, sw = base.with_piece(switch, switch.frame_for(0, base.pose_of((0, 1))))
    result = solve({"curve": 12, "straight": 4}, catalog, SolverConfig(min_pieces=0),
                   base=base, grow_from=(0, 1), close_onto=(sw, 2))
    assert result.stats.complete and not result.solutions


def test_plain_track_cannot_close_onto_a_ramps_top(catalog):
    from duplotrain.geometry import Pose

    # A ramp's top carries only an arch's foot. A straight raised to its height
    # faces it from 1024 mm away: eight straights close that gap onto raised track
    # ending where the top is, but none can join the top itself.
    straight, rise = catalog["straight"], Fraction(288, 5)
    ramp, _ = Layout().with_piece(catalog["ramp"], ORIGIN)
    raised, _ = Layout().with_piece(straight, Pose.make(x=192, z=rise))
    assert ramp.pose_of((0, 1)) == raised.pose_of((0, 1))  # 320 mm along, 57.6 mm up
    for engine in ("lattice", "field"):
        added = []
        for start in (ramp, raised):
            base, far = start.with_piece(straight, Pose.make(x=1344, z=rise))
            result = solve({"straight": 12}, catalog, SolverConfig(min_pieces=1, engine=engine),
                           base=base, grow_from=(far, 0), close_onto=(0, 1))
            assert result.stats.complete
            added.append([len(s.layout) - len(base) for s in result.solutions])
        assert added == [[], [8]]


def test_a_half_built_bridge_closes_alike_from_either_end(catalog):
    # Grown from the ramp's top or closed onto it: the same track.
    from duplotrain.editor_search import physical_key

    base = build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["ramp"], 0, 1)])
    found = []
    for grow, close in (((6, 1), (0, 0)), ((0, 0), (6, 1))):
        result = solve({"curve": 6, "straight": 4, "ramp": 1, "span": 2}, catalog,
                       SolverConfig(min_pieces=0, max_results=100), base=base,
                       grow_from=grow, close_onto=close)
        assert result.stats.complete
        found.append({physical_key(s.layout, base) for s in result.solutions})
    assert found[0] and found[0] == found[1]


def test_ends_that_meet_but_cannot_join_say_why(catalog):
    ramp, straight = catalog["ramp"], catalog["straight"]
    base, _ = Layout().with_piece(ramp, ORIGIN)
    base, end = base.with_piece(straight, straight.frame_for(0, base.pose_of((0, 1))))
    with pytest.raises(ValueError, match="ramp and straight cannot join there"):
        solve({"curve": 12}, catalog, SolverConfig(min_pieces=1), base=base,
              grow_from=(0, 1), close_onto=(end, 0))
