"""Finished searches must release workspaces without relying on cyclic garbage collection."""

import gc
import json
import weakref
from pathlib import Path

import pytest

import duplotrain.solver as solver
from duplotrain import SolverConfig, build_chain, default_catalog
from duplotrain.editor import Session
from duplotrain.layout import layout_from_dict
from tests.editor_support import complete


@pytest.fixture
def tracked_fields(monkeypatch):
    references = []
    original = solver.CollisionField

    def track(*args, **kwargs):
        instance = original(*args, **kwargs)
        references.append(weakref.ref(instance))
        return instance

    monkeypatch.setattr(solver, "CollisionField", track)
    enabled = gc.isenabled()
    gc.collect()
    gc.disable()
    try:
        yield references
    finally:
        if enabled:
            gc.enable()
        gc.collect()


@pytest.mark.parametrize("mode", ["loop", "completion", "node_limit", "piece_limit"])
def test_solver_releases_fields_on_every_normal_stop(mode, tracked_fields):
    catalog = default_catalog()
    base = None if mode == "loop" else build_chain([(catalog["curve"], 0, 1)] * 8)
    inventory = {"curve": 12} if base is None else {"curve": 4, "straight": 2}
    config = SolverConfig(min_pieces=0, max_results=1000,
                          max_nodes=1 if mode == "node_limit" else 100000,
                          max_pieces=2 if mode == "piece_limit" else None)
    result = solver.solve(inventory, catalog, config, base=base)
    assert result.stats.stop_reason == (mode if mode.endswith("limit") else "exhausted")
    assert tracked_fields and all(ref() is None for ref in tracked_fields)
    # Keeping results and making another search must not keep the old fields alive.
    again = solver.solve(inventory, catalog, config, base=base)
    assert result.solutions == again.solutions
    assert all(ref() is None for ref in tracked_fields)


def test_a_closed_bridge_search_releases_every_stage_field(tracked_fields):
    data = json.loads((Path(__file__).parent / "fixtures/bridge-gap.json").read_text())
    base = layout_from_dict(data, default_catalog())
    for _ in range(3):
        session = Session(history=[base], unlimited=True)
        job = complete(session)
        assert len(job.solutions) == 8 and job.nodes == 1878
        job.close()
        assert all(ref() is None for ref in tracked_fields)
    assert tracked_fields


@pytest.mark.parametrize("mode", ["loop", "completion"])
def test_callback_errors_do_not_leave_recursive_workspace_cycles(mode, tracked_fields):
    catalog = default_catalog()

    def fail(*args):
        raise RuntimeError("intentional callback failure")

    base = None if mode == "loop" else build_chain([(catalog["curve"], 0, 1)] * 6)
    inventory = {"curve": 12} if base is None else {"curve": 6, "straight": 4}
    config = SolverConfig(min_pieces=0, solution_filter=fail)
    # Do not retain the exception/traceback: tracebacks intentionally own frames.
    caught = False
    try:
        solver.solve(inventory, catalog, config, base=base)
    except RuntimeError:
        caught = True
    assert caught
    assert tracked_fields and all(ref() is None for ref in tracked_fields)


def test_network_enumeration_releases_its_field_and_tables(monkeypatch):
    import duplotrain.networks as networks

    tracked = []
    for name in ("CollisionField", "_CompletionReachability"):
        original = getattr(networks, name)

        def track(*args, original=original, **kwargs):
            instance = original(*args, **kwargs)
            tracked.append(weakref.ref(instance))
            return instance

        monkeypatch.setattr(networks, name, track)
    enabled = gc.isenabled()
    gc.collect()
    gc.disable()
    try:
        result = networks.enumerate_networks(
            {"curve": 12, "straight": 2}, default_catalog(),
            networks.NetworkConfig(max_pieces=14, max_results=5))
        assert result.layouts and len(tracked) == 2
        assert all(ref() is None for ref in tracked)
    finally:
        if enabled:
            gc.enable()
