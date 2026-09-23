"""Turning stock, free routes and future targets must retain complete solutions."""

from dataclasses import replace

import pytest

from duplotrain import Layout, Pose, SolverConfig, build_chain, default_catalog, parse_piece, solve
from duplotrain.solver import _solution_overlaps


def compare_searches(catalog, inventory, cfg, base, grow, close):
    options = dict(base=base, grow_from=grow, close_onto=close)
    reference = solve(inventory, catalog, replace(cfg, completion_lookahead=0), **options)
    improved = solve(inventory, catalog, cfg, **options)
    assert reference.stats.complete and improved.stats.complete
    # Equality includes enumeration order, links, forced gaps and closure kinds.
    assert improved.solutions == reference.solutions
    assert improved.stats.nodes <= reference.stats.nodes
    for solution in improved.solutions:
        assert solution.layout.placements[:len(base)] == base.placements
        assert solution.gap <= cfg.slop + 1e-12
        assert not _solution_overlaps(solution.layout, len(base), 120, 8)
    return improved


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("branch", [1, 2])
@pytest.mark.parametrize("reverse", [False, True])
@pytest.mark.parametrize("slop", [0.0, 5.0])
def test_existing_switch_can_supply_all_turning_without_new_stock(engine, branch, reverse, slop):
    catalog = default_catalog()
    base, switch = Layout().with_piece(catalog["switch"],
                                       Pose.make(x=317, y=-290, z=77, heading=4))
    base, left = base.attach(catalog["straight"], 1, (switch, 0))
    end = base.pose_of((switch, branch))
    target = Pose(end.x + (3 if slop else 0), end.y + (4 if slop else 0), end.z, end.heading)
    base, right = base.with_piece(catalog["straight"], catalog["straight"].frame_for(0, target))
    base = Layout(base.placements, {})
    witness = base.join((left, 1), (switch, 0)).join((switch, branch), (right, 0), force=bool(slop))
    grow, close = (left, 1), (right, 0)
    if reverse:
        grow, close = close, grow
    cfg = SolverConfig(min_pieces=0, max_pieces=1, max_results=1000, engine=engine, slop=slop)
    result = compare_searches(catalog, {}, cfg, base, grow, close)
    assert len(result.solutions) == 1 and result.solutions[0].layout == witness
    assert result.solutions[0].gap == pytest.approx(slop)
    assert result.solutions[0].exact is (slop == 0)


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("slop", [0.0, 5.0])
@pytest.mark.parametrize("reversing", [True, False])
def test_new_junction_retains_its_later_turning_transit(engine, slop, reversing):
    catalog = default_catalog()
    start = catalog["curve"].paths[0].end().then(128, 0, 0, 0)
    # Two independent curved routes on one custom junction. A spare straight
    # bridges them; traversing the second route turns another 30° for free.
    catalog["double_curve"] = parse_piece({"id": "double_curve", "paths": [
        {"segments": [{"type": "arc", "radius": 256, "degrees": 30}]},
        {"start": {"x": start.x, "y": start.y, "heading_deg": start.degrees},
         "segments": [{"type": "arc", "radius": 256, "degrees": 30}]},
    ]})
    base, left = Layout().with_piece(catalog["straight"], Pose.make(x=-128))
    end = catalog["double_curve"].ports[3].pose
    target = Pose(end.x + (3 if slop else 0), end.y + (4 if slop else 0), end.z, end.heading)
    base, right = base.with_piece(catalog["straight"], catalog["straight"].frame_for(0, target))
    witness, junction = base.attach(catalog["double_curve"], 0, (left, 1))
    witness, bridge = witness.attach(catalog["straight"], 0, (junction, 1))
    witness = witness.join((bridge, 1), (junction, 2)).join((junction, 3), (right, 0),
                                                          force=bool(slop))
    assert not _solution_overlaps(witness, len(base), 120, 8)
    # Without reversing targets the quick turn prunes stay active: they must
    # count the second pass's turn, which needs no further piece.
    cfg = SolverConfig(min_pieces=2, max_results=1000, engine=engine,
                       reversing_loops=reversing, slop=slop)
    result = compare_searches(catalog, {"double_curve": 1, "straight": 1}, cfg,
                              base, (left, 1), (right, 0))
    assert any(s.layout == witness for s in result.solutions)


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("curves", [1, 2])
@pytest.mark.parametrize("slop", [0.0, 512.0])
def test_scarce_turning_stock_preserves_results_across_backtracking(engine, curves, slop):
    catalog = default_catalog()
    base = build_chain([(catalog["switch"], 0, 1)])
    inventory = {"curve": curves, "switch": 1, "crossing": 1}
    # Deliberately generous position slack isolates exact heading constraints.
    # Branches with equal lengths can retain different amounts of turning stock.
    cfg = SolverConfig(min_pieces=0, max_results=1000, max_nodes=100_000,
                       reversing_loops=True, engine=engine, slop=slop)
    result = compare_searches(catalog, inventory, cfg, base, (0, 1), (0, 0))
    if slop:
        assert {s.kind for s in result.solutions} == {"loop", "reversing"}
        assert all(not s.exact for s in result.solutions)
    else:
        assert not result.solutions


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("bridge", [1, 2, 3])
def test_return_loop_floor_grants_the_transit_exactly_when_the_loop_fits(engine, bridge):
    catalog = default_catalog()
    # The second route starts `bridge` straights beyond the first route's exit, so
    # a tail must place the junction, lay exactly that many straights back to the
    # second route and pass through it for free. The floor must allow precisely that.
    start = catalog["curve"].paths[0].end().then(128 * bridge, 0, 0, 0)
    catalog["double_curve"] = parse_piece({"id": "double_curve", "paths": [
        {"segments": [{"type": "arc", "radius": 256, "degrees": 30}]},
        {"start": {"x": start.x, "y": start.y, "heading_deg": start.degrees},
         "segments": [{"type": "arc", "radius": 256, "degrees": 30}]},
    ]})
    base, left = Layout().with_piece(catalog["straight"], Pose.make(x=-128))
    end = catalog["double_curve"].ports[3].pose
    base, right = base.with_piece(catalog["straight"], catalog["straight"].frame_for(0, end))
    witness, junction = base.attach(catalog["double_curve"], 0, (left, 1))
    cursor = (junction, 1)
    for _ in range(bridge):
        witness, index = witness.attach(catalog["straight"], 0, cursor)
        cursor = (index, 1)
    witness = witness.join(cursor, (junction, 2)).join((junction, 3), (right, 0))
    assert not witness.joint_issues()
    cfg = SolverConfig(min_pieces=bridge + 1, max_results=1000, engine=engine,
                       reversing_loops=True)
    result = compare_searches(catalog, {"double_curve": 1, "straight": bridge + 1}, cfg,
                              base, (left, 1), (right, 0))
    assert any(s.layout == witness for s in result.solutions)
    tables = {}
    solve({"double_curve": 1, "straight": bridge + 1}, catalog, cfg, base=base,
          grow_from=(left, 1), close_onto=(right, 0), tables=tables)
    (completion,) = tables.values()
    # The loop back takes `bridge` traversals, so exactly the shorter ones are too few.
    assert completion.transit_floor("double_curve") == bridge - 1
