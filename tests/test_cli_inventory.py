"""Inventory validation belongs before any lossy CLI conversion or merging."""

import json

import pytest
from click.testing import CliRunner

import duplotrain.cli as cli
from duplotrain import default_catalog
from duplotrain.sets import inventory_for_sets
from duplotrain.solver import SolveResult, SolveStats


@pytest.mark.parametrize("count", [
    -1, -0.1, 0.5, 12.0, 12.75, True, False, None, "12", {}, [],
    float("nan"), float("inf"),
])
def test_invalid_json_counts_are_rejected_before_merging(tmp_path, monkeypatch, count):
    def search(*args, **kwargs):
        pytest.fail("invalid inventory reached the search engine")

    monkeypatch.setattr(cli, "solve", search)
    path = tmp_path / "box.json"
    path.write_text(json.dumps({"curve": count}))
    result = CliRunner().invoke(cli.main, ["solve", "--curve", "20", "--inventory", str(path)])
    assert result.exit_code != 0
    assert "bad inventory file" in result.output and "non-negative integer" in result.output
    assert "Traceback" not in result.output


@pytest.mark.parametrize("data", [[], None, 12, "box", {"missing": 0}])
def test_inventory_document_must_be_a_known_id_mapping(tmp_path, data):
    path = tmp_path / "box.json"
    path.write_text(json.dumps(data))
    result = CliRunner().invoke(cli.main, ["solve", "--inventory", str(path)])
    assert result.exit_code != 0 and "bad inventory file" in result.output
    assert "Traceback" not in result.output


@pytest.mark.parametrize("piece", sorted(default_catalog()))
def test_all_piece_flags_reject_negative_counts(piece):
    result = CliRunner().invoke(cli.main, [
        "solve", "--" + piece.replace("_", "-"), "-1",
    ])
    assert result.exit_code == 2 and "Invalid value" in result.output


def test_valid_flags_sets_and_json_counts_are_still_additive(tmp_path, monkeypatch):
    calls = []

    def search(inventory, *args, **kwargs):
        calls.append(inventory)
        return SolveResult([], SolveStats(complete=True, stop_reason="exhausted"))

    monkeypatch.setattr(cli, "solve", search)
    path = tmp_path / "box.json"
    path.write_text(json.dumps({"curve": 3, "straight": 0}))
    result = CliRunner().invoke(cli.main, [
        "solve", "--curve", "2", "--set", "10874", "--inventory", str(path),
    ])
    assert result.exit_code == 0, result.output
    expected, _ = inventory_for_sets(["10874"])
    expected["curve"] = expected.get("curve", 0) + 5
    expected.setdefault("straight", 0)
    assert calls == [expected]


def test_inventory_read_errors_are_reported_politely(tmp_path):
    result = CliRunner().invoke(cli.main, ["solve", "--inventory", str(tmp_path)])
    assert result.exit_code != 0 and "bad inventory file" in result.output
    assert "Traceback" not in result.output
