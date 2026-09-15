"""Reuse geometric proofs without retaining solver state or changing enumeration."""

import gc
import weakref
from dataclasses import asdict

import pytest

from duplotrain import ORIGIN, Pose, SolverConfig, build_chain, default_catalog, solve
from duplotrain.lattice import LatticePoint
from duplotrain.solver import (
    _compile_lattice,
    _CompletionReachability,
    _FieldEngine,
    _flat,
    _moves_for,
    _pose_to_lattice,
)


def table_for(engine, pids=("straight",), max_work=4096):
    catalog = {pid: default_catalog()[pid] for pid in pids}
    moves = {pid: _moves_for(piece) for pid, piece in catalog.items()}
    if engine == "lattice":
        eng = _compile_lattice(ORIGIN, ORIGIN, catalog, moves)

        def convert(pose):
            return _flat(_pose_to_lattice(pose))
    else:
        eng = _FieldEngine(ORIGIN, ORIGIN, catalog, moves)

        def convert(pose):
            return pose

    return _CompletionReachability(eng, 6, max_work), convert


def assert_same_search(cached, reference):
    assert cached.solutions == reference.solutions
    old, new = asdict(reference.stats), asdict(cached.stats)
    # Preprocessing grows with the search effort and a repeated query may extend
    # it a little earlier when evaluated afresh; every answer and therefore every
    # search decision is the same, only the moment some layer was built differs.
    for key in ("duration_s", "completion_cache_hits", "completion_checks", "completion_work",
                "completion_states", "completion_height_states", "completion_bound_depth",
                "completion_bound_states"):
        old.pop(key)
        new.pop(key)
    assert old == new
    assert (reference.stats.completion_checks
            == cached.stats.completion_checks + cached.stats.completion_cache_hits)


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("reversing", [False, True])
def test_cache_preserves_exhaustive_results_and_all_search_counters(engine, reversing, monkeypatch):
    catalog = default_catalog()
    start = Pose.make(x=317, y=-190, z=77, heading=4 if engine == "lattice" else 5)
    if reversing:
        base = build_chain([(catalog["switch"], 0, 1)], start=start)
        inventory = {"curve": 12}
        ends = {"grow_from": (0, 1), "close_onto": (0, 0)}
    else:
        base = build_chain([(catalog["curve"], 0, 1)] * 6, start=start)
        inventory = {"curve": 6, "straight": 4}
        ends = {}
    config = SolverConfig(min_pieces=0, max_results=1000, engine=engine,
                          reversing_loops=reversing)
    cached = solve(inventory, catalog, config, base=base, **ends)
    monkeypatch.setattr(_CompletionReachability, "allows", _CompletionReachability._allows)
    reference = solve(inventory, catalog, config, base=base, **ends)
    assert reference.stats.complete and cached.solutions
    assert cached.stats.completion_cache_hits > 0
    assert_same_search(cached, reference)


def test_broad_inventory_avoids_most_repeated_geometry_checks(monkeypatch):
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)] * 2 + [(catalog["curve"], 0, 1)] * 4)
    inventory = {"curve": 20, "straight": 6, "ramp": 2, "span": 2,
                 "switch": 2, "crossing": 1, "slope": 2}
    config = SolverConfig(min_pieces=0, max_pieces=20, max_results=8, max_nodes=25_000,
                          reversing_loops=True)
    cached = solve(inventory, catalog, config, base=base)
    monkeypatch.setattr(_CompletionReachability, "allows", _CompletionReachability._allows)
    reference = solve(inventory, catalog, config, base=base)
    assert len(cached.solutions) == 8
    assert_same_search(cached, reference)
    assert cached.stats.completion_checks < reference.stats.completion_checks // 5


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_cache_keys_include_height_heading_and_traversal_budget(engine):
    table, convert = table_for(engine)
    predecessor = convert(Pose.make(x=-128))
    assert not table.allows(predecessor, 0)
    assert table.allows(predecessor, 1)
    for pose in (Pose.make(x=-128, z=1), Pose.make(x=-128, heading=2)):
        assert not table.allows(convert(pose), 1)
    work, checks = table.work_left, table.checks
    assert not table.allows(predecessor, 0)
    assert table.allows(predecessor, 1)
    assert table.cache_hits == 2 and table.checks == checks and table.work_left == work


def test_cache_eviction_and_budget_exhaustion_preserve_permissive_fallback():
    table, convert = table_for("lattice", max_work=0)
    queries = [convert(Pose.make(x=-i)) for i in range(1, 4100)]
    for query in queries:
        assert not table.allows(query, 0)
        assert table.allows(query, 10)
        assert len(table.cache) <= 4096
    # The first answers were evicted. Re-evaluation must still fall back at an
    # unfinished depth, while retaining the exact zero-traversal rejection.
    assert not table.allows(queries[0], 0)
    assert table.allows(queries[0], 10)
    assert table.work_left == 0 and len(table.layers) == len(table.bounds.layers) == 1


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_caches_are_isolated_between_catalogues_and_released_after_search(engine):
    straight, convert = table_for(engine)
    curve, _ = table_for(engine, ("curve",))
    query = convert(Pose.make(x=-128))
    assert straight.allows(query, 1)
    assert not curve.allows(query, 1)
    assert straight.allows(query, 1)
    reference = weakref.ref(straight)
    del straight
    gc.collect()
    assert reference() is None


def test_direct_target_rotations_match_exact_lattice_arithmetic_on_every_basis():
    table, _ = table_for("lattice")
    eng = table.eng
    samples = [tuple(int(i == j) for i in range(4)) for j in range(4)]
    samples.extend(((10**15, -3, 177, -29), (-11, 97, -33, 71)))
    for heading in range(12):
        target = (29, -53, 61, -71, 83, heading)
        turn = (eng.anchor[5] - heading) % 12
        for sample in samples:
            cursor = (*sample, -109, (heading + 5) % 12)
            delta = LatticePoint(*(cursor[i] - target[i] for i in range(4))).rotated(turn)
            expected = (*delta.key(), -192, 5)
            assert eng.retarget(cursor, target) == expected


@pytest.mark.parametrize("interrupt", [False, True])
@pytest.mark.parametrize("slop", [0.0, 5.0])
def test_solver_releases_cached_poses_on_success_and_callback_failure(monkeypatch, interrupt, slop):
    import duplotrain.solver as solver

    tables = []

    def capture(*args, **kwargs):
        table = _CompletionReachability(*args, **kwargs)
        tables.append(table)
        return table

    def progress(_nodes):
        raise RuntimeError("cancelled by caller")

    monkeypatch.setattr(solver, "_CompletionReachability", capture)
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)] * 2 + [(catalog["curve"], 0, 1)] * 4)
    inventory = {"curve": 20, "straight": 6, "ramp": 2, "span": 2,
                 "switch": 2, "crossing": 1, "slope": 2}
    # The eight-result search now ends before the first progress report, so the
    # interrupted variant keeps searching until the callback fires.
    config = SolverConfig(min_pieces=0, max_pieces=20, max_results=1000 if interrupt else 8,
                          max_nodes=60_000, slop=slop, reversing_loops=True,
                          progress=progress if interrupt else None)
    if interrupt:
        with pytest.raises(RuntimeError, match="cancelled by caller"):
            solve(inventory, catalog, config, base=base)
    else:
        assert len(solve(inventory, catalog, config, base=base).solutions) == 8
    assert len(tables) == 1 and tables[0].cache_hits > 0
    assert not tables[0].cache
    assert not tables[0].near_indices
