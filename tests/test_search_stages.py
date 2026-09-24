"""Interactive searches follow the documented stage order under reversing and slop."""
import json
from pathlib import Path

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.editor import Session
from duplotrain.editor_search import SearchJob
from duplotrain.layout import layout_from_dict


@pytest.fixture(scope="module")
def gap():
    path = Path(__file__).parent / "fixtures/bridge-gap.json"
    return layout_from_dict(json.loads(path.read_text()), default_catalog())


def run(gap, body, nodes=None):
    job = SearchJob(Session(history=[gap], unlimited=True), dict(body))
    stages = []
    for _ in range(100_000):
        if job.status != "running" or (nodes is not None and job.nodes > nodes):
            break
        job.tick()
        if not stages or stages[-1] != job.stage:
            stages.append(job.stage)
    return job, stages


def test_allowing_reversing_loops_keeps_the_ordinary_and_bridge_stages(gap):
    # Reversing is ticked by default whenever a direction stone is owned. Only the
    # full-inventory fallback searches reversing closures, as /api/solve does.
    exact, _ = run(gap, {})
    reversing, stages = run(gap, {"reversing": True})
    try:
        assert "standard bridge" in stages and "full inventory" not in stages
        assert reversing.status == "results_ready"
        assert [s.layout for s in reversing.solutions] == [s.layout for s in exact.solutions]
    finally:
        exact.close()
        reversing.close()


def test_a_one_direction_stage_runs_before_the_next_stage_starts(gap):
    # A forced fit grows from one end: its plain stage (25,000 nodes) must run to
    # its own limit before the bridge stage starts, and is never resumed after it.
    job, stages = run(gap, {"slop": 1}, nodes=30_000)
    try:
        assert stages == ["templates", "plain track", "standard bridge"]
    finally:
        job.close()
