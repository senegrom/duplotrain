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
@pytest.mark.parametrize("retain_tables", [False, True])
def test_solver_releases_fields_on_every_normal_stop(mode, retain_tables, tracked_fields):
    catalog = default_catalog()
    base = None if mode == "loop" else build_chain([(catalog["curve"], 0, 1)] * 8)
    inventory = {"curve": 12} if base is None else {"curve": 4, "straight": 2}
    tables = {} if retain_tables else None
    config = SolverConfig(min_pieces=0, max_results=1000,
                          max_nodes=1 if mode == "node_limit" else 100000,
                          max_pieces=2 if mode == "piece_limit" else None)
    result = solver.solve(inventory, catalog, config, base=base, tables=tables)
    assert result.stats.stop_reason == (mode if mode.endswith("limit") else "exhausted")
    assert tracked_fields and all(ref() is None for ref in tracked_fields)
    if retain_tables and base is not None:
        assert tables  # User-owned reachability tables deliberately survive.
    # Keeping results and making another search must not keep the old fields alive.
    again = solver.solve(inventory, catalog, config, base=base, tables=tables)
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


@pytest.mark.parametrize("callback", ["filter", "progress"])
def test_callback_errors_do_not_leave_recursive_workspace_cycles(callback, tracked_fields):
    catalog = default_catalog()

    def fail(*args):
        raise RuntimeError("intentional callback failure")

    if callback == "filter":
        base = None
        inventory = {"curve": 12}
        config = SolverConfig(solution_filter=fail)
    else:
        data = json.loads((Path(__file__).parent / "fixtures/bridge-gap.json").read_text())
        base = layout_from_dict(data, catalog)
        inventory = {"curve": 20, "straight": 20}
        config = SolverConfig(min_pieces=0, max_nodes=10000, completion_lookahead=0,
                              max_pieces=26, progress=fail)
    # Do not retain the exception/traceback: tracebacks intentionally own frames.
    caught = False
    try:
        solver.solve(inventory, catalog, config, base=base)
    except RuntimeError:
        caught = True
    assert caught
    assert tracked_fields and all(ref() is None for ref in tracked_fields)
