"""Exact input, immutable snapshots, and bounded exhaustive classification."""

import copy
import importlib
import json
import pickle
from itertools import islice

import pytest
from click.testing import CliRunner

from duplotrain import (
    ORIGIN,
    ClassificationLimitError,
    Layout,
    build_chain,
    classify,
    default_catalog,
    layout_to_dict,
    parse_piece,
)
from duplotrain.catalog import ACCESSORIES
from duplotrain.cli import main
from duplotrain.drive import _tongue_assignments
from duplotrain.exact import Alg
from duplotrain.gui import Session
from duplotrain.pieces import Arc


@pytest.mark.parametrize("degrees", [30.9, -30.9, 30.000000001, "30.9", float("inf"),
                                     float("nan"), True, False, None])
def test_arc_rejects_angle_without_rounding(degrees):
    with pytest.raises(ValueError, match="whole multiple of 15"):
        parse_piece({"id": "bad_arc", "paths": [{"segments": [
            {"type": "arc", "radius": 256, "degrees": degrees},
        ]}]})
    with pytest.raises(ValueError, match="whole multiple of 15"):
        Arc(Alg(256), degrees)


@pytest.mark.parametrize("degrees", [30, 30.0, "30", -300, 390])
def test_integral_arc_angles_retain_their_full_sweep(degrees):
    arc = Arc(Alg(256), degrees)
    assert type(arc.degrees) is int
    assert arc.degrees == int(degrees)
    assert arc.turn_steps == int(degrees) // 15 % 24


def test_layout_copies_and_freezes_constructor_collections():
    chain = build_chain([(default_catalog()["straight"], 0, 1)] * 2)
    placements, links, stones = list(chain.placements), dict(chain.links), [[0, "stone_horn"]]
    layout = Layout(placements, links, stones)
    placements.clear()
    links.clear()
    stones[0][1] = "stone_stop"
    assert layout.placements == chain.placements
    assert layout.links == chain.links
    assert layout.accessories == ((0, "stone_horn"),)
    with pytest.raises(TypeError):
        layout.links[(0, 1)] = (1, 1)


@pytest.mark.parametrize("restore", [copy.copy, copy.deepcopy,
                                     lambda obj: pickle.loads(pickle.dumps(obj))])
def test_immutable_layout_still_supports_copy_and_pickle(restore):
    chain = build_chain([(default_catalog()["straight"], 0, 1)] * 2)
    restored = restore(chain)
    assert restored == chain
    with pytest.raises(TypeError):
        restored.links[(0, 1)] = (1, 1)


def test_session_state_metadata_is_independent_between_responses_and_sessions():
    session = Session()
    before = copy.deepcopy(ACCESSORIES)
    state = session.state()
    state["stones"]["catalog"]["stone_horn"]["name"] = "changed"
    del state["stones"]["catalog"]["stone_direction"]
    assert ACCESSORIES == before
    assert session.state()["stones"]["catalog"] == before
    assert Session().state()["stones"]["catalog"] == before


def switches(count):
    layout = Layout()
    switch = default_catalog()["switch"]
    for _ in range(count):
        layout, _ = layout.with_piece(switch, ORIGIN)
    return layout


def test_tongue_assignments_can_yield_a_small_prefix_of_a_large_product():
    assignments = list(islice(_tongue_assignments(switches(24)), 3))
    assert len(assignments) == 3
    assert all(len(a) == 24 for a in assignments)
    assert len({tuple(a.items()) for a in assignments}) == 3
    assignments[0].clear()
    assert len(assignments[1]) == 24


def test_large_classification_fails_before_any_simulation(monkeypatch):
    def unexpected_drive(*args, **kwargs):
        pytest.fail("classification must check its budget before simulation")

    monkeypatch.setattr(importlib.import_module("duplotrain.drive"), "drive", unexpected_drive)
    with pytest.raises(ClassificationLimitError, match="1,207,959,552 runs"):
        classify(switches(24))


def test_classification_budget_is_explicit_and_never_returns_a_partial_verdict():
    layout = switches(1)
    with pytest.raises(ClassificationLimitError, match="6 runs"):
        classify(layout, max_runs=5)
    bounded = classify(layout, max_runs=6)
    assert bounded == classify(layout, max_runs=None)
    assert bounded.runs == 6 and not bounded.locally_looping


@pytest.mark.parametrize("budget", [0, -1, 1.5, True])
def test_classification_rejects_invalid_budget(budget):
    with pytest.raises(ValueError, match="max_runs"):
        classify(switches(1), max_runs=budget)


def test_cli_classification_limit_has_no_verdict_or_traceback(tmp_path):
    path = tmp_path / "switch.json"
    path.write_text(json.dumps(layout_to_dict(switches(1))))
    runner = CliRunner()
    result = runner.invoke(main, ["classify", str(path), "--max-runs", "5"])
    assert result.exit_code != 0
    assert "increase --max-runs" in result.output
    assert "Traceback" not in result.output and "locally looping" not in result.output
    result = runner.invoke(main, ["classify", str(path), "--max-runs", "6"])
    assert result.exit_code == 0 and "6 simulated runs" in result.output
