"""Long-tail bounds retain exact witnesses and respect the preprocessing cap."""

import random
from dataclasses import replace

import pytest

from duplotrain import ORIGIN, Pose, SolverConfig, build_chain, default_catalog, parse_piece, solve
from duplotrain.solver import (
    _compile_lattice,
    _CompletionBounds,
    _FieldEngine,
    _flat,
    _moves_for,
    _pose_to_lattice,
    _solution_overlaps,
)


def signatures(result):
    return {(s.signature, s.kind, s.gap) for s in result.solutions}


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_envelopes_contain_independently_constructed_exact_tails(engine):
    catalog = default_catalog()
    if engine == "field":
        catalog["fine"] = parse_piece({"id": "fine", "paths": [{"segments": [
            {"type": "arc", "radius": "317/3", "degrees": 15},
        ]}]})
    moves = {pid: _moves_for(piece) for pid, piece in catalog.items()}
    anchor = Pose.make(x=317, y=-290, z=77, heading=4 if engine == "lattice" else 7)
    if engine == "lattice":
        eng = _compile_lattice(anchor, anchor, catalog, moves)

        def convert(pose):
            return _flat(_pose_to_lattice(pose))
    else:
        eng = _FieldEngine(anchor, anchor, catalog, moves)

        def convert(pose):
            return pose

    bounds = _CompletionBounds(eng)
    assert 0 < bounds.extend(12, 4096) <= 4096
    assert len(bounds.layers) == 13
    rng = random.Random(2037)
    pool = [move for piece_moves in moves.values() for move in piece_moves]
    for length in range(13):
        for _ in range(8):
            tail = rng.choices(pool, k=length)
            delta = ORIGIN
            for move in tail:
                delta = delta.then(move.dx, move.dy, move.dz, move.dheading)
            heading = (anchor.heading - delta.heading) % 24
            offset = Pose.make(heading=heading).then(delta.x, delta.y, delta.z, delta.heading)
            cursor = Pose(anchor.x - offset.x, anchor.y - offset.y, anchor.z - offset.z, heading)
            end = cursor
            for move in tail:
                end = end.then(move.dx, move.dy, move.dz, move.dheading)
            assert end == anchor
            assert bounds.allows(convert(cursor), length)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_elevated_mixed_inventory_retains_every_completion(engine):
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 8,
                       start=Pose.make(x=317, y=-90, z=41, heading=4))
    inventory = {"curve": 4, "straight": 2, "ramp": 2}
    cfg = SolverConfig(min_pieces=0, max_results=1000, max_nodes=100_000, engine=engine)
    reference = solve(inventory, catalog, replace(cfg, completion_lookahead=0), base=base)
    improved = solve(inventory, catalog, cfg, base=base)
    assert reference.stats.complete and improved.stats.complete
    assert improved.solutions and signatures(improved) == signatures(reference)
    assert improved.stats.nodes < reference.stats.nodes // 4


def test_fifteen_degree_completion_beyond_the_exact_table_retains_all_results():
    catalog = default_catalog()
    catalog["fine"] = parse_piece({"id": "fine", "paths": [{"segments": [
        {"type": "arc", "radius": 512, "degrees": 15},
    ]}]})
    base = build_chain([(catalog["fine"], 0, 1)] * 16,
                       start=Pose.make(x=317, y=-90, z=41, heading=5))
    inventory = {"fine": 8, "straight": 1}
    cfg = SolverConfig(min_pieces=0, max_results=1000)
    reference = solve(inventory, catalog, replace(cfg, completion_lookahead=0), base=base)
    improved = solve(inventory, catalog, cfg, base=base)
    assert reference.stats.complete and improved.stats.complete
    assert improved.solutions and signatures(improved) == signatures(reference)
    assert improved.stats.completion_bound_depth > cfg.completion_lookahead


@pytest.mark.parametrize("case", ["mixed", "switch"])
def test_previously_capped_broad_search_finds_audited_solutions(case):
    catalog = default_catalog()
    if case == "mixed":
        base = build_chain([(catalog["straight"], 0, 1)] * 2 + [(catalog["curve"], 0, 1)] * 4)
        inventory = {"curve": 20, "straight": 6, "ramp": 2, "span": 2,
                     "switch": 2, "crossing": 1, "slope": 2}
        ends = {}
    else:
        base = build_chain([(catalog["switch"], 0, 1)])
        inventory = {"curve": 12, "straight": 4, "switch": 1, "crossing": 1,
                     "ramp": 2, "span": 2}
        ends = {"grow_from": (0, 1), "close_onto": (0, 0)}
    cfg = SolverConfig(min_pieces=0, max_pieces=20, max_results=8, max_nodes=25_000,
                       reversing_loops=True)
    result = solve(inventory, catalog, cfg, base=base, **ends)
    assert len(result.solutions) == 8 and not result.stats.aborted
    assert result.stats.stop_reason == "result_limit" and not result.stats.complete
    assert result.stats.completion_work <= min(4096, cfg.max_nodes // 8)
    assert result.stats.completion_bound_depth > cfg.completion_lookahead
    for solution in result.solutions:
        assert solution.exact and not solution.layout.joint_issues()
        assert solution.layout.placements[:len(base)] == base.placements
        assert not _solution_overlaps(solution.layout, len(base), cfg.clearance, 8)
        assert all(n <= inventory.get(pid, 0) + base.piece_counts.get(pid, 0)
                   for pid, n in solution.layout.piece_counts.items())


def test_long_gap_uses_less_than_a_thousand_nodes():
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)] * 4 + [(catalog["curve"], 0, 1)] * 2)
    cfg = SolverConfig(min_pieces=0, max_pieces=20, max_results=8, max_nodes=25_000)
    result = solve({"curve": 14, "straight": 8}, catalog, cfg, base=base)
    assert len(result.solutions) == 8 and result.stats.nodes < 1000
    assert result.stats.completion_work <= min(4096, cfg.max_nodes // 8)
    assert result.stats.completion_bound_states <= 12 * (result.stats.completion_bound_depth + 1)


def test_unfinished_envelope_is_permissive_and_complete_layers_remain_usable():
    catalog = default_catalog()
    moves = {pid: _moves_for(piece) for pid, piece in catalog.items()}
    eng = _compile_lattice(ORIGIN, ORIGIN, catalog, moves)
    bounds = _CompletionBounds(eng)
    unreachable = (10**9, 0, 0, 0, 0, 0)
    assert bounds.extend(1, 0) == 0
    assert bounds.allows(unreachable, 1)
    work = bounds.extend(1, 1000)
    assert 0 < work <= 1000 and not bounds.allows(unreachable, 1)
    retained = list(bounds.layers)
    assert bounds.extend(100, 0) == 0
    assert bounds.layers == retained
    assert bounds.allows(unreachable, 100)
    assert not bounds.allows(unreachable, 1)


def test_empty_move_pool_stabilizes_without_unbounded_layers():
    catalog = {"buffer": default_catalog()["buffer"]}
    eng = _compile_lattice(ORIGIN, ORIGIN, catalog, {"buffer": []})
    bounds = _CompletionBounds(eng)
    assert bounds.extend(10**9, 0) == 0
    assert bounds.saturated and len(bounds.layers) == 1
    assert bounds.allows(eng.anchor, 10**9)
    assert not bounds.allows((1, 0, 0, 0, 0, 0), 10**9)
