"""CLI smoke tests: the documented flows work, and bad input fails politely."""

import json

import pytest
from click.testing import CliRunner

from duplotrain.cli import main


@pytest.fixture()
def runner():
    return CliRunner()


def test_pieces_lists_catalog(runner):
    result = runner.invoke(main, ["pieces"])
    assert result.exit_code == 0
    assert "curve" in result.output


def test_unknown_piece_in_inventory_fails_politely(runner, tmp_path):
    bad = tmp_path / "box.json"
    bad.write_text(json.dumps({"curve": 12, "kurve": 4}))
    result = runner.invoke(main, ["solve", "--inventory", str(bad)])
    assert result.exit_code != 0
    assert "unknown piece" in result.output
    assert "Traceback" not in result.output


def test_malformed_catalog_fails_politely(runner, tmp_path):
    bad = tmp_path / "cat.json"
    bad.write_text(json.dumps({"pieces": [{"id": "shorty", "paths": [
        {"segments": [{"type": "straight", "length": 64}]}]}]}))
    result = runner.invoke(main, ["solve", "--catalog", str(bad), "--curve", "12"])
    assert result.exit_code != 0
    assert "bad catalogue file" in result.output
    assert "Traceback" not in result.output


def test_solve_check_render_round_trip(runner, tmp_path):
    out = tmp_path / "out"
    result = runner.invoke(
        main, ["solve", "--curve", "12", "-o", str(out), "--top", "1"]
    )
    assert result.exit_code == 0, result.output
    saved = out / "loop_01.json"
    assert saved.exists()
    assert (out / "loop_01.png").exists()

    result = runner.invoke(main, ["check", str(saved)])
    assert result.exit_code == 0
    assert "Fully closed" in result.output

    target = tmp_path / "picture.png"
    result = runner.invoke(main, ["render", str(saved), "-o", str(target)])
    assert result.exit_code == 0
    assert target.exists()


def test_sets_command_lists_known_sets(runner):
    result = runner.invoke(main, ["sets"])
    assert result.exit_code == 0
    for code in ("10874", "10875", "10872", "10882"):
        assert code in result.output


def test_solve_with_set_shortcut(runner):
    # 10872 alone (straights + bridge) cannot loop; the CLI should say so politely.
    result = runner.invoke(main, ["solve", "--set", "10872"])
    assert result.exit_code == 0, result.output
    assert "No closed loop fits" in result.output

    result = runner.invoke(main, ["solve", "--set", "9999"])
    assert result.exit_code != 0
    assert "unknown set" in result.output


def test_check_rejects_garbage_layout(runner, tmp_path):
    bad = tmp_path / "layout.json"
    bad.write_text(json.dumps({"format": "duplotrain-layout/1", "placements": [
        {"piece": "hovercraft", "frame": {"x": ["0", "0", "0", "0"],
                                          "y": ["0", "0", "0", "0"],
                                          "z": ["0", "0", "0", "0"],
                                          "heading": 0}}], "links": []}))
    result = runner.invoke(main, ["check", str(bad)])
    assert result.exit_code != 0
    assert "bad layout file" in result.output
    assert "Traceback" not in result.output