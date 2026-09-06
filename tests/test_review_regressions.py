"""Regressions for the review: real engine/session objects, not geometry stand-ins."""

import copy
import importlib.util
import json
from pathlib import Path

import pytest
from click.testing import CliRunner

from duplotrain import SolverConfig, default_catalog, solve
from duplotrain.cli import main
from duplotrain.gui import Session, dispatch_session
from duplotrain.layout import build_chain, layout_from_dict, layout_to_dict
from duplotrain.validation import check_layout_json


def half_circle_session():
    session = Session(inventory={"curve": 12})
    for i in range(6):
        session.attach("curve", 0, None if i == 0 else (i - 1, 1))
    session.solve_gap(None, None, slop=0, max_results=3)
    assert session.candidates
    return session


def long_gap_session():
    catalog = default_catalog()
    layout = build_chain([(catalog["straight"], 0, 1)] * 34)
    for index in range(32, 0, -1):
        layout = layout.remove(index)
    return Session(catalog=catalog, inventory={"straight": 34}, history=[layout])


def test_clear_is_undoable():
    session = half_circle_session()
    before = session.layout
    session.clear()
    assert len(session.layout) == 0
    assert session.state()["can_undo"]
    session.undo()
    assert session.layout == before


@pytest.mark.parametrize("change", ["inventory", "sandbox", "set"])
def test_inventory_changes_invalidate_candidates(change):
    session = half_circle_session()
    revision = session.revision
    if change == "inventory":
        session.set_inventory({"curve": 6})
    elif change == "sandbox":
        session.set_unlimited(True)
    else:
        session.add_set("10882")
    assert not session.candidates
    assert session.revision > revision
    with pytest.raises(ValueError, match="stale"):
        session.apply_candidate(0, revision)


def test_candidate_application_rechecks_inventory_even_without_setter():
    session = half_circle_session()
    session.inventory["curve"] = 6
    with pytest.raises(ValueError, match="inventory"):
        session.apply_candidate(0)
    assert len(session.layout) == 6


def test_old_candidate_revision_cannot_select_a_new_candidate():
    session = half_circle_session()
    old_revision = session.revision
    session.set_inventory({"curve": 13})
    session.solve_gap(None, None, 0, 3)
    with pytest.raises(ValueError, match="stale"):
        session.apply_candidate(0, old_revision)


@pytest.mark.parametrize("counts", [
    {"curve": 9, "invalid": 1}, {"curve": 9, "straight": "no"},
    {"curve": 9, "straight": 1.5}, {"curve": 9, "straight": True},
    {"curve": 9, "straight": -1}, {"curve": 9, "straight": 10001}, [],
])
def test_inventory_update_is_atomic(counts):
    session = Session()
    before = session.snapshot(), session.revision
    with pytest.raises(ValueError):
        session.set_inventory(counts)
    assert (session.snapshot(), session.revision) == before


def test_session_recovery_round_trips_geometry_inventory_and_stones():
    source = half_circle_session()
    source.set_inventory({"straight": 17, "stone_direction": 3})
    source.set_unlimited(True)
    checkpoint = json.loads(json.dumps(source.snapshot()))
    restored = Session()
    dispatch_session(restored, "/api/restore", {"data": checkpoint, "revision": 0})
    assert restored.snapshot() == checkpoint
    assert restored.layout == source.layout
    assert restored.candidates == []


def test_failed_restore_preserves_entire_session():
    session = half_circle_session()
    before = session.snapshot(), session.revision, list(session.candidates)
    bad = copy.deepcopy(session.snapshot())
    bad["inventory"]["curve"] = 123
    bad["layout"]["placements"][0]["frame"]["x"][0] = "1e999999999"
    with pytest.raises(ValueError):
        session.restore(bad)
    assert (session.snapshot(), session.revision, session.candidates) == before


def test_piece_depth_limit_is_not_a_proof_of_impossibility():
    session = long_gap_session()
    outcome = session.solve_gap((0, 1), (1, 0), 0, 3)
    assert outcome["found"] == 0
    assert not outcome["aborted"]
    assert not outcome["complete"]
    assert outcome["stop_reason"] == "piece_limit"
    assert outcome["max_pieces_searched"] == 26
    deeper = session.solve_gap((0, 1), (1, 0), 0, 3, max_pieces=64)
    assert deeper["found"] == 1
    assert deeper["complete"]
    assert session.candidates[0].piece_count == 34


def test_node_and_result_caps_report_incomplete():
    catalog = default_catalog()
    stopped = solve({"curve": 12}, catalog, SolverConfig(max_nodes=1))
    assert stopped.stats.aborted
    assert not stopped.stats.complete
    assert stopped.stats.stop_reason == "node_limit"
    capped = solve({"curve": 12}, catalog, SolverConfig(max_results=1))
    assert capped.solutions
    assert not capped.stats.complete
    assert capped.stats.stop_reason == "result_limit"
    exhausted = solve({"straight": 1}, catalog)
    assert exhausted.stats.complete
    assert exhausted.stats.stop_reason == "exhausted"


@pytest.mark.parametrize("coefficient", [
    "1e5000", "1e999999999", "1/0", "0/0", "nan", "inf", "9" * 49,
    10**100, "1000000001", 0.5, True, None, {}, [],
])
def test_untrusted_coefficients_fail_before_layout_construction(coefficient):
    catalog = default_catalog()
    data = layout_to_dict(build_chain([(catalog["straight"], 0, 1)]))
    data["placements"][0]["frame"]["x"][0] = coefficient
    with pytest.raises(ValueError):
        check_layout_json(data)
    with pytest.raises(ValueError):
        layout_from_dict(data, catalog)


def test_exact_rationals_remain_supported():
    catalog = default_catalog()
    data = layout_to_dict(build_chain([(catalog["curve"], 0, 1)]))
    data["placements"][0]["frame"]["x"] = ["1/3", "-2/7", "3/11", "0"]
    assert layout_to_dict(layout_from_dict(data, catalog)) == data


def test_coefficient_arity_and_format_version_are_checked():
    data = layout_to_dict(Session().layout)
    data["format"] = "duplotrain-layout/99"
    with pytest.raises(ValueError, match="format"):
        check_layout_json(data)
    data = layout_to_dict(build_chain([(default_catalog()["straight"], 0, 1)]))
    data["placements"][0]["frame"]["x"] = ["0"] * 3
    with pytest.raises(ValueError, match="exactly 4"):
        check_layout_json(data)


def test_cli_continues_json_export_without_matplotlib(monkeypatch, tmp_path):
    import duplotrain.cli as cli

    real_import = cli.importlib.import_module

    def without_matplotlib(name, *args, **kwargs):
        if name == "matplotlib":
            raise ModuleNotFoundError("No module named matplotlib", name="matplotlib")
        return real_import(name, *args, **kwargs)

    monkeypatch.setattr(cli.importlib, "import_module", without_matplotlib)
    out = tmp_path / "layouts"
    result = CliRunner().invoke(main, ["solve", "--curve", "12", "-o", str(out)])
    assert result.exit_code == 0, result.output
    assert "writing layout JSON only" in " ".join(result.output.split())
    assert list(out.glob("*.json"))
    assert not list(out.glob("*.png"))
    result = CliRunner().invoke(main, ["render", str(next(out.glob("*.json")))])
    assert result.exit_code != 0
    assert "duplotrain[render]" in result.output


def test_pyodide_adapter_uses_same_validation_and_recovery():
    path = Path(__file__).parents[1] / "webapp" / "adapter.py"
    spec = importlib.util.spec_from_file_location("review_adapter", path)
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    for body in ("not JSON", "[]", '{"data": null}'):
        assert "__error" in json.loads(adapter.dispatch("/api/restore", body))
    source = half_circle_session().snapshot()
    body = json.dumps({"data": source, "revision": 0})
    result = json.loads(adapter.dispatch("/api/restore", body))
    assert result["snapshot"] == source
