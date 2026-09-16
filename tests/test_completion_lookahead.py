"""Reverse reachability must accelerate completions and loops without losing witnesses."""

from dataclasses import replace

import pytest

from duplotrain import (
    ORIGIN,
    Layout,
    Pose,
    SolverConfig,
    build_chain,
    default_catalog,
    parse_piece,
    solve,
)
from duplotrain.gui import Session
from duplotrain.solver import _solution_overlaps


def signatures(result):
    return {(s.signature, s.gap, s.kind) for s in result.solutions}


def ordered(result):
    return [(s.signature, s.gap, s.kind) for s in result.solutions]


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_exact_lookahead_keeps_every_completion_and_reduces_work(engine):
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    cfg = SolverConfig(min_pieces=0, max_results=100, engine=engine)
    plain = solve({"curve": 6, "straight": 4}, catalog,
                  replace(cfg, completion_lookahead=0), base=base)
    fast = solve({"curve": 6, "straight": 4}, catalog, cfg, base=base)
    assert plain.stats.complete and fast.stats.complete
    assert len(fast.solutions) == 3
    assert signatures(fast) == signatures(plain)
    assert fast.stats.nodes < plain.stats.nodes // 2
    assert fast.stats.pruned_completion > 0
    assert 0 < fast.stats.completion_states <= 4097
    assert all(not _solution_overlaps(s.layout, len(base), 120, 8) for s in fast.solutions)


def test_lookahead_handles_a_custom_fifteen_degree_piece():
    catalog = default_catalog()
    catalog["fine_curve"] = parse_piece({"id": "fine_curve", "paths": [{"segments": [
        {"type": "arc", "radius": 512, "degrees": 15},
    ]}]})
    base = build_chain([(catalog["fine_curve"], 0, 1)] * 20)
    inventory = {"fine_curve": 4, "straight": 2}
    cfg = SolverConfig(min_pieces=0)
    plain = solve(inventory, catalog, replace(cfg, completion_lookahead=0), base=base)
    fast = solve(inventory, catalog, cfg, base=base)
    assert fast.stats.engine == "field" and fast.stats.complete
    assert fast.solutions and signatures(fast) == signatures(plain)


def test_incomplete_reverse_layer_falls_back_to_full_search(monkeypatch):
    import duplotrain.solver as solver

    original = solver._CompletionReachability
    monkeypatch.setattr(solver, "_CompletionReachability",
                        lambda eng, horizon, max_work, **kw: original(eng, horizon, 1, **kw))
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    cfg = SolverConfig(min_pieces=0)
    plain = solve({"curve": 6, "straight": 4}, catalog,
                  replace(cfg, completion_lookahead=0), base=base)
    fast = solve({"curve": 6, "straight": 4}, catalog, cfg, base=base)
    assert fast.stats.complete and signatures(fast) == signatures(plain)
    assert fast.stats.completion_states == 1


def test_bridge_completion_finds_more_results_with_the_same_node_budget():
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["ramp"], 0, 1)])
    inventory = {"curve": 6, "straight": 4, "ramp": 1, "span": 2}
    cfg = SolverConfig(min_pieces=0, max_pieces=16, max_results=8, max_nodes=25_000,
                       reversing_loops=True)
    plain = solve(inventory, catalog, replace(cfg, completion_lookahead=0), base=base)
    fast = solve(inventory, catalog, cfg, base=base)
    assert plain.stats.aborted and not fast.stats.aborted
    assert len(fast.solutions) == 8 > len(plain.solutions)
    assert signatures(plain) <= signatures(fast)
    assert fast.stats.nodes < plain.stats.nodes // 2
    assert not fast.stats.complete and fast.stats.stop_reason == "result_limit"
    assert all(s.exact and not s.layout.joint_issues() for s in fast.solutions)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_exact_lookahead_does_not_discard_forced_fits(engine):
    catalog = default_catalog()
    base, left = Layout().with_piece(catalog["straight"], ORIGIN)
    base, right = base.with_piece(catalog["straight"], Pose(257, 0, 0, 0))
    cfg = SolverConfig(min_pieces=1, slop=1, engine=engine)
    options = dict(base=base, grow_from=(left, 1), close_onto=(right, 0))
    plain = solve({"straight": 1}, catalog, replace(cfg, completion_lookahead=0), **options)
    fast = solve({"straight": 1}, catalog, cfg, **options)
    assert fast.stats.complete and signatures(fast) == signatures(plain)
    assert len(fast.solutions) == 1
    assert fast.solutions[0].gap == 1 and not fast.solutions[0].exact
    assert fast.stats.completion_states > 0


def test_editor_can_apply_a_completion_from_the_improved_search():
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    session = Session(catalog=catalog, inventory={"curve": 12, "straight": 4}, history=[base])
    before_revision = session.revision
    outcome = session.solve_gap(None, None, 0.0, 8, reversing=True)
    assert outcome["found"] == 3 and outcome["complete"]
    assert outcome["searched"] < 500
    assert session.revision == before_revision + 1
    session.apply_candidate(0, revision=session.revision)
    assert session.layout.is_closed and not session.layout.joint_issues()
    assert session.layout.placements[:len(base)] == base.placements


@pytest.mark.parametrize("lookahead", [-1, 13, 1.5, True])
def test_invalid_lookahead_is_rejected(lookahead):
    with pytest.raises(ValueError, match="completion_lookahead"):
        SolverConfig(completion_lookahead=lookahead)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_loop_search_prunes_with_the_reverse_tables(engine):
    # A fresh loop must return to the origin face: the tables built for
    # completions apply unchanged, and a sound prune leaves the ordered results.
    catalog = default_catalog()
    cfg = SolverConfig(max_results=100, engine=engine)
    plain = solve({"curve": 12, "straight": 2}, catalog, replace(cfg, completion_lookahead=0))
    fast = solve({"curve": 12, "straight": 2}, catalog, cfg)
    assert plain.stats.complete and fast.stats.complete
    assert len(fast.solutions) == 2 and ordered(fast) == ordered(plain)
    assert fast.stats.pruned_completion > 0 and fast.stats.completion_states > 1
    assert fast.stats.nodes * 10 < plain.stats.nodes
    assert all(not _solution_overlaps(s.layout, 0, 120, 8) for s in fast.solutions)


def test_loop_search_keeps_slop_reversing_and_stub_witnesses():
    catalog = default_catalog()
    slop = SolverConfig(max_results=100, slop=3.0)
    plain = solve({"curve": 12, "straight": 2}, catalog, replace(slop, completion_lookahead=0))
    fast = solve({"curve": 12, "straight": 2}, catalog, slop)
    assert plain.stats.complete and fast.stats.complete and ordered(fast) == ordered(plain)
    assert fast.stats.nodes * 10 < plain.stats.nodes
    # Closing into the switch's own branch, and looping through its stub.
    reversing = SolverConfig(max_results=100, reversing_loops=True)
    plain = solve({"curve": 12, "switch": 1}, catalog, replace(reversing, completion_lookahead=0))
    fast = solve({"curve": 12, "switch": 1}, catalog, reversing)
    assert plain.stats.complete and fast.stats.complete and ordered(fast) == ordered(plain)
    assert {s.kind for s in fast.solutions} == {"loop", "reversing"}
    assert fast.stats.nodes * 50 < plain.stats.nodes


def test_loop_search_finishes_a_previously_capped_reversing_search():
    catalog = default_catalog()
    inventory = {"curve": 12, "straight": 2, "switch": 1}
    cfg = SolverConfig(max_results=100, reversing_loops=True, slop=3.0, max_nodes=25_000)
    plain = solve(inventory, catalog, replace(cfg, completion_lookahead=0))
    fast = solve(inventory, catalog, cfg)
    assert plain.stats.aborted and fast.stats.complete
    assert set(ordered(plain)) <= set(ordered(fast))
    assert len(fast.solutions) > len(plain.solutions)
    assert all(not _solution_overlaps(s.layout, 0, 120, 8) for s in fast.solutions)
