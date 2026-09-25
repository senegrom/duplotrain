"""CLI smoke tests: the documented flows work, and bad input fails politely."""

import json
from pathlib import Path

import pytest
from click.testing import CliRunner

import duplotrain.cli as cli
from duplotrain import ORIGIN, Layout, build_chain, classify, default_catalog
from duplotrain.cli import main
from duplotrain.layout import layout_to_dict
from duplotrain.scoring import score_solution
from duplotrain.solver import SolverConfig, SolveResult, SolveStats, solve
from tests.test_drive import switches


@pytest.fixture()
def runner():
    return CliRunner()


def test_pieces_lists_catalog(runner):
    result = runner.invoke(main, ["pieces"])
    assert result.exit_code == 0
    assert "curve" in result.output


def test_pieces_json_lists_every_piece_with_its_port_count(runner, tmp_path):
    catalog = default_catalog()
    result = runner.invoke(main, ["pieces", "--json"])
    assert result.exit_code == 0
    listed = {piece["id"]: piece for piece in json.loads(result.output)}
    assert list(listed) == list(catalog)
    assert {pid: piece["ports"] for pid, piece in listed.items()} == {
        pid: len(piece.ports) for pid, piece in catalog.items()}
    assert (listed["straight"]["ports"], listed["switch"]["ports"],
            listed["crossing"]["ports"]) == (2, 3, 4)
    # A --catalog file overrides a built-in piece by its id (the README example).
    mine = tmp_path / "my-measurements.json"
    mine.write_text(json.dumps({"pieces": [{
        "id": "ramp", "name": "Bridge ramp (my callipers)", "category": "bridge", "width": 64,
        "paths": [{"segments": [{"type": "ramp", "run": 320, "rise": 60}]}],
        "port_names": ["low", "high"]}]}))
    result = runner.invoke(main, ["pieces", "--json", "--catalog", str(mine)])
    overridden = {piece["id"]: piece for piece in json.loads(result.output)}
    assert list(overridden) == list(catalog)
    assert overridden["ramp"]["name"] == "Bridge ramp (my callipers)"
    assert overridden["ramp"]["ports"] == 2 and not overridden["ramp"]["provisional"]


def captured_configs(monkeypatch):
    configs = []

    def search(inventory, catalog, config):
        configs.append(config)
        return SolveResult([], SolveStats(complete=True, stop_reason="exhausted"))

    monkeypatch.setattr(cli, "solve", search)
    return configs


@pytest.mark.parametrize("args, reversing, announced", [
    (["--set", "10874"], True, True),   # the Steam Train box has a direction stone
    (["--set", "10874", "--no-reversing"], False, False),
    (["--set", "10882"], False, False),  # Train Tracks: a stop stone only
    (["--curve", "12"], False, False),
    (["--curve", "12", "--reversing"], True, False),
])
def test_reversing_follows_a_sets_direction_stone_unless_chosen(runner, monkeypatch, args,
                                                                reversing, announced):
    configs = captured_configs(monkeypatch)
    result = runner.invoke(main, ["solve", *args])
    assert result.exit_code == 0, result.output
    assert [config.reversing_loops for config in configs] == [reversing]
    assert ("reversing loops enabled" in " ".join(result.output.split())) is announced


@pytest.mark.parametrize("use_all", [False, True])
def test_use_all_keeps_only_loops_that_use_every_owned_piece(runner, monkeypatch, tmp_path,
                                                             use_all):
    monkeypatch.setattr(cli, "_get_renderer", lambda required=True: None)  # JSON only
    out = tmp_path / "out"
    result = runner.invoke(main, ["solve", "--curve", "12", "--straight", "2", "-o", str(out),
                                  *(["--use-all"] if use_all else [])])
    assert result.exit_code == 0, result.output
    sizes = sorted(len(json.loads(path.read_text())["placements"])
                   for path in out.glob("loop_*.json"))
    # The circle leaves both straights in the box; only the oval uses them all.
    assert sizes == ([14] if use_all else [12, 14])


def test_solve_saves_and_lists_loops_best_first(runner, monkeypatch, tmp_path):
    monkeypatch.setattr(cli, "_get_renderer", lambda required=True: None)  # JSON only
    inventory = {"curve": 12, "straight": 4}
    out = tmp_path / "out"
    result = runner.invoke(main, ["solve", "--curve", "12", "--straight", "4",
                                  "-o", str(out), "--top", "25"])
    assert result.exit_code == 0, result.output
    found = solve(inventory, default_catalog(), SolverConfig(min_pieces=4, max_results=25))
    score = {json.dumps(layout_to_dict(sol.layout)): score_solution(sol, inventory).total
             for sol in found.solutions}
    saved = sorted(out.glob("loop_*.json"))
    assert len(saved) == len(found.solutions) >= 3
    totals = [score[json.dumps(json.loads(path.read_text()))] for path in saved]
    assert totals == sorted(totals, reverse=True) and totals[0] > totals[-1]
    # The table lists them in the same order, numbered from the best.
    shown = [round(float(row.split("│")[2])) for row in result.output.splitlines()
             if row.count("│") > 3 and row.split("│")[1].strip().isdigit()]
    assert shown == [round(total) for total in totals]


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


def test_check_reports_each_pair_of_open_ends_and_their_gap(runner, tmp_path):
    half = build_chain([(default_catalog()["curve"], 0, 1)] * 6)
    path = tmp_path / "half.json"
    path.write_text(json.dumps(layout_to_dict(half)))
    result = runner.invoke(main, ["check", str(path)])
    assert result.exit_code == 1
    assert "2 open end(s)" in result.output
    # The half circle's two ends face each other across its 512 mm diameter.
    assert "Open ends (0, 0) <-> (5, 1): gap 512 mm" in result.output


def test_cli_check_reports_the_complete_crossing_length(tmp_path):
    layout, _ = Layout().with_piece(default_catalog()["crossing"], ORIGIN)
    path = tmp_path / "crossing.json"
    path.write_text(json.dumps(layout_to_dict(layout)))
    result = CliRunner().invoke(main, ["check", str(path)])
    assert "26 cm of track" in result.output
    assert "13 cm of track" not in result.output


def test_classify_prints_the_first_failing_run(runner, tmp_path):
    bar = build_chain([(default_catalog()["straight"], 0, 1)] * 2)
    path = tmp_path / "bar.json"
    path.write_text(json.dumps(layout_to_dict(bar)))
    result = runner.invoke(main, ["classify", str(path)])
    assert result.exit_code == 0
    (start, tongues, outcome) = classify(bar).counterexample
    assert (start, tongues, outcome) == ((0, 0), {}, "derailed")
    assert ("first failure: a train entering piece 0 via port 0 -> derailed"
            in " ".join(result.output.split()))


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


# Out-of-range counts and slop are covered in test_cli_failures.py.
@pytest.mark.parametrize("args", [["--slop", "nan"], ["--top", "-1", "-o", "out"]])
def test_invalid_solve_options_fail_politely(runner, tmp_path, args):
    with runner.isolated_filesystem(temp_dir=tmp_path):
        result = runner.invoke(main, ["solve", "--curve", "12", *args])
        assert result.exit_code != 0 and not Path("out").exists()
    assert isinstance(result.exception, SystemExit)  # a polite exit, not a crash


@pytest.mark.parametrize("contents", [
    "[" * 100_000 + "]" * 100_000,                              # absurd nesting
    json.dumps({"pieces": [{"id": "x", "paths": 5}]}),          # wrong shapes
    json.dumps({"pieces": ["id"]}),
    json.dumps({"pieces": [{"id": "x", "paths": [{"segments": [
        {"type": "straight", "run": "1e16000000"}]}]}]}),     # an enormous number
    json.dumps({"pieces": [{"id": "x", "paths": [{"segments": [
        {"type": "straight", "run": "1/0"}]}]}]}),
    json.dumps({"pieces": [{"id": "x", "paths": [{"segments": [
        {"type": "straight", "run": 10**400}]}]}]}),       # a JSON integer, not text
    json.dumps({"pieces": [{"id": "x", "width": 1e12, "paths": [{"segments": [
        {"type": "straight", "run": 128}]}]}]}),
], ids=["nesting", "paths-shape", "piece-shape", "huge-number", "zero-division",
        "huge-integer", "huge-width"])
def test_bad_catalogue_and_layout_files_fail_politely(runner, tmp_path, contents):
    bad = tmp_path / "bad.json"
    bad.write_text(contents)
    for args in (["pieces", "--catalog", str(bad)], ["check", str(bad)],
                 ["classify", str(bad)], ["solve", "--inventory", str(bad)]):
        result = runner.invoke(main, args)
        assert result.exit_code != 0 and isinstance(result.exception, SystemExit), args


def test_image_names_and_unwritable_targets(runner, tmp_path):
    pytest.importorskip("matplotlib")
    with runner.isolated_filesystem(temp_dir=tmp_path):
        result = runner.invoke(main, ["demo", "-o", "noext"])
        assert result.exit_code == 0 and "noext.png" in result.output
        assert Path("noext.png").exists()
        for target in ("picture.xyz", str(Path("missing") / "p.png")):
            result = runner.invoke(main, ["demo", "-o", target])
            assert result.exit_code == 1 and "cannot write" in result.output


def test_classify_and_gui_reject_impossible_requests(runner, tmp_path):
    empty = tmp_path / "empty.json"
    empty.write_text(json.dumps({"format": "duplotrain-layout/1", "placements": [],
                                 "links": []}))
    result = runner.invoke(main, ["classify", str(empty)])
    assert result.exit_code == 1 and "nothing to classify" in result.output
    result = runner.invoke(main, ["gui", "--port", "70000", "--no-browser"])
    assert result.exit_code == 2 and "70000" in result.output


def test_classify_refuses_track_whose_joints_cannot_exist(runner, tmp_path):
    # A bar of straights "linked" from its far end back to its start: the model
    # would drive through a 512 mm joint as if it were track.
    catalog = default_catalog()
    bar = build_chain([(catalog["straight"], 0, 1)] * 4)
    impossible = bar.join((3, 1), (0, 0), force=True).with_accessory(0, "stone_direction")
    path = tmp_path / "impossible.json"
    path.write_text(json.dumps(layout_to_dict(impossible)))
    result = runner.invoke(main, ["classify", str(path)])
    assert result.exit_code == 1 and "joints fit exactly" in result.output


def test_a_solve_that_finds_nothing_still_replaces_earlier_results(runner, monkeypatch,
                                                                   tmp_path):
    monkeypatch.setattr(cli, "_get_renderer", lambda required=True: None)  # JSON only
    out = tmp_path / "out"
    assert runner.invoke(main, ["solve", "--curve", "12", "-o", str(out)]).exit_code == 0
    assert list(out.glob("loop_*.json"))
    result = runner.invoke(main, ["solve", "--set", "10872", "-o", str(out)])
    assert result.exit_code == 0 and "No closed loop fits" in result.output
    assert not list(out.glob("loop_*"))


def test_json_files_may_start_with_a_byte_order_mark(runner, tmp_path):
    catalog = default_catalog()
    circle = build_chain([(catalog["curve"], 0, 1)] * 12).join((11, 1), (0, 0))
    layout = tmp_path / "circle.json"
    layout.write_bytes(json.dumps(layout_to_dict(circle)).encode("utf-8-sig"))
    inventory = tmp_path / "box.json"
    inventory.write_bytes(json.dumps({"curve": 12}).encode("utf-8-sig"))
    extra = tmp_path / "extra.json"
    extra.write_bytes(json.dumps({"pieces": []}).encode("utf-8-sig"))
    assert runner.invoke(main, ["check", str(layout)]).exit_code == 0
    result = runner.invoke(main, ["solve", "--inventory", str(inventory), "--catalog", str(extra)])
    assert result.exit_code == 0 and "distinct loop(s) found" in result.output


def test_an_inventory_of_zero_counts_asks_what_you_own(runner, tmp_path):
    inventory = tmp_path / "empty-box.json"
    inventory.write_text(json.dumps({"curve": 0, "straight": 0}))
    result = runner.invoke(main, ["solve", "--inventory", str(inventory)])
    assert result.exit_code == 2 and "Tell me what you own" in result.output
