"""Slippage pruning must preserve actual forced joints, budgets, and exact geometry."""

import random
from dataclasses import replace

import pytest

from benchmarks.completion import cases
from duplotrain import ORIGIN, Layout, Pose, SolverConfig, default_catalog, solve
from duplotrain.exact import Alg
from duplotrain.solver import (
    _MM_SCALE,
    _compile_lattice,
    _completion_budget,
    _CompletionBounds,
    _CompletionReachability,
    _FieldEngine,
    _flat,
    _moves_for,
    _pose_to_lattice,
    _solution_overlaps,
)


@pytest.fixture(scope="module")
def inputs():
    catalog = default_catalog()
    return catalog, {case.name: case for case in cases(catalog)}


def engine_for(catalog, engine, anchor=ORIGIN):
    moves = {pid: _moves_for(piece) for pid, piece in catalog.items()}
    if engine == "lattice":
        eng = _compile_lattice(anchor, anchor, catalog, moves)

        def convert(pose):
            return _flat(_pose_to_lattice(pose))
    else:
        eng = _FieldEngine(anchor, anchor, catalog, moves)

        def convert(pose):
            return pose
    return eng, convert, moves


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("name", [
    "half_circle_slop_1", "offset_circle_slop_4.9", "offset_circle_slop_5",
    "offset_circle_slop_10", "transit_slop_2.9", "transit_slop_3",
    "turn_transit_slop_4.9", "turn_transit_slop_5",
])
def test_exhaustive_slippage_results_match_unpruned_search(inputs, engine, name):
    catalog, examples = inputs
    case = examples[name]
    cfg = SolverConfig(min_pieces=0, max_pieces=20, max_results=1000, max_nodes=100_000,
                       slop=case.slop, engine=engine)
    options = dict(base=case.base, **(case.ends or {}))
    reference = solve(case.inventory, catalog, replace(cfg, completion_lookahead=0), **options)
    improved = solve(case.inventory, catalog, cfg, **options)
    assert reference.stats.complete and improved.stats.complete
    # Includes layouts, enumeration order, gaps and exact flags.
    assert improved.solutions == reference.solutions
    assert improved.stats.nodes <= reference.stats.nodes
    for solution in improved.solutions:
        assert solution.gap <= case.slop + 1e-12
        assert solution.layout.placements[:len(case.base)] == case.base.placements
        assert not _solution_overlaps(solution.layout, len(case.base), 120, 8)
    if name == "offset_circle_slop_5":
        assert len(improved.solutions) == 3
        assert all(not s.exact and s.gap == pytest.approx(5) for s in improved.solutions)
        assert improved.stats.nodes < reference.stats.nodes // 5
    elif name == "transit_slop_3":
        assert len(improved.solutions) == 1
        solution = improved.solutions[0]
        assert solution.gap == 3 and not solution.exact
        assert sorted(j["gap_mm"] for j in solution.layout.joint_issues()) == [1, 2]
    elif name == "turn_transit_slop_5":
        assert len(improved.solutions) == 1
        assert not improved.solutions[0].exact
        assert improved.solutions[0].gap == pytest.approx(5)
    elif name in ("transit_slop_2.9", "offset_circle_slop_4.9", "turn_transit_slop_4.9"):
        assert not improved.solutions


def test_fractional_fifteen_degree_slippage_retains_its_completion(inputs):
    catalog, examples = inputs
    case = examples["fifteen_degree_slop_1"]
    cfg = SolverConfig(min_pieces=0, slop=1)
    reference = solve(case.inventory, catalog, replace(cfg, completion_lookahead=0), base=case.base)
    improved = solve(case.inventory, catalog, cfg, base=case.base)
    assert reference.stats.complete and improved.stats.complete
    assert improved.stats.engine == "field" and improved.solutions == reference.solutions
    assert len(improved.solutions) == 1


@pytest.mark.parametrize("name", [
    "bridge_full_slop_1", "switch_full_slop_5", "long_gap_slop_5",
    "offset_full_slop_5", "offset_long_slop_5",
    "mixed_full", "mixed_full_slop_1", "mixed_full_slop_5",
])
def test_slippage_benchmarks_find_more_audited_results_with_same_budget(inputs, name):
    catalog, examples = inputs
    case = examples[name]
    cfg = SolverConfig(min_pieces=0, slop=case.slop, max_pieces=20,
                       max_results=8, max_nodes=25_000, reversing_loops=case.reversing)
    options = dict(base=case.base, **(case.ends or {}))
    reference = solve(case.inventory, catalog, replace(cfg, completion_lookahead=0), **options)
    improved = solve(case.inventory, catalog, cfg, **options)
    assert reference.stats.aborted and len(improved.solutions) == 8
    assert not improved.stats.aborted and improved.stats.nodes < reference.stats.nodes
    assert improved.solutions[:len(reference.solutions)] == reference.solutions
    assert improved.stats.completion_work <= _completion_budget(improved.stats.nodes, cfg.max_nodes)
    for solution in improved.solutions:
        assert not _solution_overlaps(solution.layout, len(case.base), 120, 8)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_near_cache_includes_remaining_slack_height_heading_and_depth(engine):
    catalog = {"straight": default_catalog()["straight"]}
    eng, convert, _moves = engine_for(catalog, engine)
    table = _CompletionReachability(eng, 6, 4096, slippage=True)
    query = convert(Pose.make(x=-133))
    assert not table.allows(query, 1, 4.9)
    assert table.allows(query, 1, 5.0)
    assert not table.allows(query, 0, 5.0)
    assert not table.allows(convert(Pose.make(x=-133, z=1)), 1, 1000)
    assert not table.allows(convert(Pose.make(x=-133, heading=2)), 1, 1000)
    before = table.cache_hits
    assert table.allows(query, 1, 5.0)
    assert not table.allows(query, 1, 4.9)
    assert table.cache_hits == before + 2


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_small_physical_gap_with_large_cancelling_coefficients_is_not_pruned(engine):
    catalog = default_catalog()
    # A Pell approximation of sqrt(3): huge exact coefficients but a sub-micron gap.
    offset = Alg(3650401, 0, -2107560)
    assert abs(float(offset)) < 1e-3
    base, left = Layout().with_piece(catalog["straight"], ORIGIN)
    base, right = base.with_piece(catalog["straight"], Pose(256 + offset, 0, 0, 0))
    cfg = SolverConfig(min_pieces=1, slop=1e-3, engine=engine)
    options = dict(base=base, grow_from=(left, 1), close_onto=(right, 0))
    reference = solve({"straight": 1}, catalog, replace(cfg, completion_lookahead=0), **options)
    improved = solve({"straight": 1}, catalog, cfg, **options)
    assert len(improved.solutions) == 1 and improved.solutions == reference.solutions
    assert not improved.solutions[0].exact


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_physical_envelopes_contain_independent_perturbed_tails(engine):
    catalog = default_catalog()
    anchor = Pose.make(x=317, y=-290, z=77, heading=4 if engine == "lattice" else 7)
    eng, convert, moves = engine_for(catalog, engine, anchor)
    bounds = _CompletionBounds(eng, slippage=True)
    assert 0 < bounds.extend(12, 4096) <= 4096
    rng = random.Random(6152)
    pool = [move for routes in moves.values() for move in routes]
    for length in range(13):
        for _ in range(4):
            tail = rng.choices(pool, k=length)
            delta = ORIGIN
            for move in tail:
                delta = delta.then(move.dx, move.dy, move.dz, move.dheading)
            heading = (anchor.heading - delta.heading) % 24
            offset = Pose.make(heading=heading).then(delta.x, delta.y, delta.z, delta.heading)
            # Translating any subset of a tail's joints by vectors summing to (3,4)
            # is contained in the five-millimetre total budget by the triangle bound.
            cursor = Pose(anchor.x - offset.x + 3, anchor.y - offset.y + 4,
                          anchor.z - offset.z, heading)
            end = cursor
            for move in tail:
                end = end.then(move.dx, move.dy, move.dz, move.dheading)
            assert end == Pose(anchor.x + 3, anchor.y + 4, anchor.z, anchor.heading)
            assert bounds.allows_near(convert(cursor), length, 5 * _MM_SCALE)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_unfinished_slippage_layers_remain_permissive(engine):
    catalog = {"straight": default_catalog()["straight"]}
    eng, convert, _moves = engine_for(catalog, engine)
    table = _CompletionReachability(eng, 6, 0, slippage=True)
    impossible = convert(Pose.make(x=-999, heading=2))
    assert table.allows(impossible, 6, 1)
    assert not table.allows(impossible, 0, 1)
    assert table.work_left == 0 and len(table.layers) == 1


def test_near_index_uses_euclidean_gap_and_outward_bounds():
    catalog = {"straight": default_catalog()["straight"]}
    eng, convert, _moves = engine_for(catalog, "lattice")
    table = _CompletionReachability(eng, 6, 4096, slippage=True)
    query = convert(Pose.make(x=-131, y=-4))
    assert table.allows(query, 1, 5)
    assert not table.allows(query, 1, 4.9)
    assert table.near_indices


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_forced_reversing_target_retains_every_result(engine):
    catalog = default_catalog()
    base, switch = Layout().with_piece(catalog["switch"], ORIGIN)
    branch = base.pose_of((switch, 0))
    base, seed = base.with_piece(catalog["curve"],
                                  catalog["curve"].frame_for(0, branch.then(1, 0, 0, 0)))
    cfg = SolverConfig(min_pieces=0, slop=1.0, max_results=1000, engine=engine,
                       reversing_loops=True)
    options = dict(base=base, grow_from=(seed, 1), close_onto=(switch, 1))
    reference = solve({"curve": 10}, catalog, replace(cfg, completion_lookahead=0), **options)
    improved = solve({"curve": 10}, catalog, cfg, **options)
    assert reference.stats.complete and improved.stats.complete
    assert improved.solutions == reference.solutions
    assert any(s.kind == "reversing" and not s.exact for s in improved.solutions)


def test_finite_large_slack_does_not_overflow_and_near_cache_is_bounded():
    catalog = {"straight": default_catalog()["straight"]}
    eng, convert, _moves = engine_for(catalog, "lattice")
    table = _CompletionReachability(eng, 6, 0, slippage=True)
    for i in range(4100):
        assert table.allows(convert(Pose.make(x=i + 1)), 0, 1e308)
    assert len(table.cache) == 4096
    assert table.allows(convert(Pose.make(x=1)), 0, 1e308)
    assert not table.allows(convert(Pose.make(x=1, z=1)), 0, 1e308)
