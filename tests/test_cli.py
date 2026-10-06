"""CLI smoke tests: the documented flows work, and bad input fails politely."""

import json
import re
from pathlib import Path

import pytest
from click.testing import CliRunner

import duplotrain.cli as cli
from duplotrain import ORIGIN, Layout, build_chain, classify, default_catalog
from duplotrain.cli import main
from duplotrain.layout import layout_from_dict, layout_to_dict
from duplotrain.scoring import score_solution
from duplotrain.solver import SolverConfig, SolveResult, SolveStats, solve
from tests.test_drive import switches


@pytest.fixture()
def runner():
    return CliRunner()


def test_version_is_the_package_version(runner):
    from duplotrain import __version__

    result = runner.invoke(main, ["--version"])
    assert result.exit_code == 0 and result.output == f"duplotrain, version {__version__}\n"


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
    assert listed["buffer"]["sealed_ports"] == [1] and listed["curve"]["sealed_ports"] == []
    assert listed["span"]["port_kinds"] == ["arch_foot", "track"]
    # A --catalog file overrides a built-in piece by its id (the README example).
    mine = tmp_path / "my-measurements.json"
    mine.write_text(json.dumps({"pieces": [{
        "id": "ramp", "name": "Bridge ramp (my callipers)", "category": "bridge", "width": 64,
        "paths": [{"segments": [{"type": "ramp", "run": 320, "rise": 60}]}],
        "port_names": ["low", "high"], "port_kinds": ["track", "ramp_top"]}]}))
    result = runner.invoke(main, ["pieces", "--json", "--catalog", str(mine)])
    overridden = {piece["id"]: piece for piece in json.loads(result.output)}
    assert list(overridden) == list(catalog)
    assert overridden["ramp"]["name"] == "Bridge ramp (my callipers)"
    assert overridden["ramp"]["ports"] == 2 and not overridden["ramp"]["provisional"]
    # The override keeps the bridge joint only by naming it.
    assert overridden["ramp"]["port_kinds"] == ["track", "ramp_top"]


def captured_configs(monkeypatch):
    configs = []

    def search(inventory, catalog, config):
        configs.append(config)
        return SolveResult([], SolveStats(complete=True, stop_reason="exhausted"))

    monkeypatch.setattr(cli, "solve", search)
    return configs


def table_rows(output):
    """The cells of each row of solve's table, the lines of a wrapped cell joined."""
    rows = []
    for line in output.splitlines():
        cells = [cell.strip() for cell in line.split("│")[1:-1]]
        if len(cells) < 7 or cells[0] == "#":
            continue
        if cells[0]:
            rows.append(cells)
        elif rows:  # a cell too wide for its column goes on below
            rows[-1] = [" ".join(filter(None, pair)) for pair in zip(rows[-1], cells, strict=True)]
    return rows


def pieces_in(row):
    """How many pieces a row of solve's table lists: 12 for "11xcurve 1xswitch"."""
    return sum(int(count.partition("x")[0]) for count in row[2].split())


def states_searched(output):
    return re.search(r"([\d,]+) states searched", " ".join(output.split())).group(1)


@pytest.mark.parametrize("args, reversing, announced", [
    (["--set", "10874", "--switch", "1"], True, True),  # the Steam Train box: a direction stone
    (["--set", "10874", "--switch", "1", "--no-reversing"], False, False),
    (["--set", "10882"], False, False),  # Train Tracks: a stop stone only
    (["--curve", "12", "--switch", "1", "--straight", "1"], False, False),
    (["--curve", "12", "--switch", "1", "--straight", "1", "--reversing"], True, False),
])
def test_reversing_follows_a_sets_direction_stone_unless_chosen(runner, monkeypatch, args,
                                                                reversing, announced):
    # Loops are searched for first; with reversing on, teardrops (which close into
    # the switch and carry their stone on a straight) in a search of their own.
    configs = captured_configs(monkeypatch)
    result = runner.invoke(main, ["solve", *args])
    assert result.exit_code == 0, result.output
    assert [config.reversing_loops for config in configs] == (
        [False, True] if reversing else [False])
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
    shown = [round(float(row[1])) for row in table_rows(result.output)]
    assert shown == [round(total) for total in totals]


def test_solve_lists_loops_on_the_floor_before_loops_on_bricks(runner):
    result = runner.invoke(main, ["solve", "--curve", "12", "--straight", "2", "--ramp", "2",
                                  "--span", "2", "--max-results", "200"])
    assert result.exit_code == 0, result.output
    ranked = [(int(row[6]), -int(row[1])) for row in table_rows(result.output)]
    assert ranked[0][0] == 0 and ranked[-1][0] > 0
    assert ranked == sorted(ranked)  # fewest pieces on bricks first, then the best score


def test_malformed_catalog_fails_politely(runner, tmp_path):
    bad = tmp_path / "cat.json"
    bad.write_text(json.dumps({"pieces": [{"id": "shorty", "paths": [
        {"segments": [{"type": "straight", "length": 64}]}]}]}))
    result = runner.invoke(main, ["solve", "--catalog", str(bad), "--curve", "12"])
    assert result.exit_code == 2
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
    assert "38507" in result.output  # a set's notes: the stop stone's part number


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
    # Each could join the other, so neither is named alone.
    assert "with no other end to join" not in result.output


def test_check_names_ends_that_meet_but_cannot_join(runner, tmp_path):
    catalog = default_catalog()
    ramp, straight = catalog["ramp"], catalog["straight"]
    layout, _ = Layout().with_piece(ramp, ORIGIN)
    layout, flat = layout.with_piece(straight, straight.frame_for(0, layout.pose_of((0, 1))))
    path = tmp_path / "butted.json"
    path.write_text(json.dumps(layout_to_dict(layout)))
    result = runner.invoke(main, ["check", str(path)])
    assert result.exit_code == 1
    assert f"Open ends (0, 1) <-> ({flat}, 0) meet but cannot join" in result.output
    # No near miss of 0 mm, and never a piece's own two ends.
    assert "gap 0 mm" not in result.output and "(0, 0) <-> (0, 1)" not in result.output
    # The ramp's top takes only an arch's foot, and there is none; each track end
    # could join another.
    assert "Open end (0, 1): ramp 'high', with no other end to join" in result.output
    assert result.output.count("with no other end to join") == 1


def test_check_names_open_ends_that_no_other_end_could_join(runner, tmp_path):
    # A lone straight: a piece's own two ends never join each other.
    lone = build_chain([(default_catalog()["straight"], 0, 1)])
    path = tmp_path / "lone.json"
    path.write_text(json.dumps(layout_to_dict(lone)))
    result = runner.invoke(main, ["check", str(path)])
    assert result.exit_code == 1 and "2 open end(s)" in result.output
    assert "Open end (0, 0): straight 'a', with no other end to join" in result.output
    assert "Open end (0, 1): straight 'b', with no other end to join" in result.output


def test_solve_passes_its_piece_limit_and_says_when_the_search_runs_out(runner, monkeypatch):
    # Twelve curves close no loop of eleven pieces: the search stops at the limit it
    # was given, and says which.
    output = " ".join(runner.invoke(main, ["solve", "--curve", "12", "--max-pieces", "11"])
                      .output.split())
    assert "stopped: piece_limit" in output and (
        "a closure may still exist (loops of more than --max-pieces 11 were not searched)."
        in output)
    # A ramp with no arch can stand only at a teardrop's open end: every loop of all
    # the other pieces was looked for, and none closes, but a teardrop that takes the
    # ramp too is a piece longer than --max-pieces.
    output = " ".join(runner.invoke(main, [
        "solve", "--curve", "12", "--switch", "1", "--straight", "2", "--ramp", "1",
        "--reversing", "--use-all", "--max-pieces", "15"]).output.split())
    assert "stopped: piece_limit" in output and (
        "a closure may still exist (loops of more than --max-pieces 15 were not searched)."
        in output)
    configs = captured_configs(monkeypatch)
    assert runner.invoke(main, ["solve", "--curve", "12", "--max-pieces", "20"]).exit_code == 0
    assert configs[0].max_pieces == 20
    # The advice names the limit the search ran into; a stop no limit explains
    # names none.
    for reason, args, advice in (
        ("node_limit", [], " (a higher --max-nodes searches further)."),
        ("piece_limit", ["--max-pieces", "20"],
         " (loops of more than --max-pieces 20 were not searched)."),
        ("piece_limit", [], " (loops that long are beyond the search's depth)."),
        ("not_started", [], "."),
    ):
        monkeypatch.setattr(cli, "solve", lambda *_args, reason=reason: SolveResult(
            [], SolveStats(complete=False, stop_reason=reason)))
        output = " ".join(runner.invoke(main, ["solve", "--curve", "12", *args]).output.split())
        assert f"a closure may still exist{advice}" in output, reason
    # With every loop looked for, the teardrops' search speaks when it stopped short.
    monkeypatch.setattr(cli, "solve", lambda _inventory, _catalog, config: SolveResult(
        [], SolveStats(complete=not config.reversing_loops,
                       stop_reason="node_limit" if config.reversing_loops else "exhausted")))
    output = " ".join(runner.invoke(main, ["solve", "--curve", "12", "--switch", "1",
                                           "--straight", "1", "--reversing"]).output.split())
    assert "stopped: node_limit" in output and (
        "a closure may still exist (a higher --max-nodes searches further)." in output)
    # Both stopped short: the loops' limit comes first, as their search does.
    monkeypatch.setattr(cli, "solve", lambda _inventory, _catalog, config: SolveResult(
        [], SolveStats(complete=False,
                       stop_reason="node_limit" if config.reversing_loops else "piece_limit")))
    output = " ".join(runner.invoke(main, ["solve", "--curve", "12", "--switch", "1",
                                           "--straight", "1", "--reversing",
                                           "--max-pieces", "13"]).output.split())
    assert "stopped: piece_limit" in output and (
        "a closure may still exist (loops of more than --max-pieces 13 were not searched)."
        in output)


@pytest.mark.parametrize("args, advice", [
    ([], "--max-results 1, shortest first; raise it, or --min-pieces, for longer loops."),
    (["--use-all"], "--max-results 1; raise it for more."),
    (["--switch", "1", "--reversing"], "--max-results 1, shortest first; raise it, or "
                                       "--min-pieces, for longer loops and teardrops."),
    (["--switch", "1", "--reversing", "--use-all"],
     "--max-results 1 teardrops, shortest first; raise it for more."),
])
def test_a_search_stopped_at_max_results_says_how_to_list_more(runner, args, advice):
    # Every loop that takes all the pieces is as long as the next: more, not longer.
    # Without --use-all teardrops are looked for only as far as the loops went, so
    # the loops' limit holds them back too. With the switch no loop takes every piece
    # but teardrops do: only their search stops at the limit, and the header names
    # that stop all the same.
    result = runner.invoke(main, ["solve", "--curve", "12", "--straight", "4",
                                  "--max-results", "1", *args])
    assert result.exit_code == 0, result.output
    printed = " ".join(result.output.split())
    assert "stopped: result_limit" in printed
    assert f"The search stopped at {advice}" in printed


def test_solve_help_explains_each_bound_on_the_search(runner):
    helped = " ".join(runner.invoke(main, ["solve", "--help"]).output.split())
    options = {param.name: param for param in cli.solve_cmd.params}
    for name in ("min_pieces", "max_pieces", "max_results", "max_nodes"):
        assert options[name].help and " ".join(options[name].help.split()) in helped, name


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
    # A file check cannot read is no verdict on a layout (exit 1): exit 2.
    assert result.exit_code == 2
    assert "bad layout file" in result.output
    assert "Traceback" not in result.output


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
    # Whichever file it is, input a command cannot read exits 2, like a bad option,
    # and the error names the file it could not read.
    for args, kind in ((["pieces", "--catalog", str(bad)], "catalogue"),
                       (["check", str(bad)], "layout"), (["classify", str(bad)], "layout"),
                       (["solve", "--inventory", str(bad)], "inventory")):
        result = runner.invoke(main, args)
        assert result.exit_code == 2 and isinstance(result.exception, SystemExit), args
        assert f"bad {kind} file" in result.output, args


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
    buffers = tmp_path / "buffer.json"  # a lone buffer holds no train
    buffers.write_text(json.dumps(layout_to_dict(
        build_chain([(default_catalog()["buffer"], 0, 1)]))))
    result = runner.invoke(main, ["classify", str(buffers)])
    assert result.exit_code == 1 and "no drivable track" in result.output
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


@pytest.mark.parametrize("encoding", ["utf-8-sig", "utf-16"])
def test_json_files_may_be_saved_in_any_unicode_encoding(runner, tmp_path, encoding):
    catalog = default_catalog()
    circle = build_chain([(catalog["curve"], 0, 1)] * 12).join((11, 1), (0, 0))
    layout = tmp_path / "circle.json"
    layout.write_bytes(json.dumps(layout_to_dict(circle)).encode(encoding))
    inventory = tmp_path / "box.json"
    inventory.write_bytes(json.dumps({"curve": 12}).encode(encoding))
    extra = tmp_path / "extra.json"
    extra.write_bytes(json.dumps({"pieces": []}).encode(encoding))
    assert runner.invoke(main, ["check", str(layout)]).exit_code == 0
    result = runner.invoke(main, ["solve", "--inventory", str(inventory), "--catalog", str(extra)])
    assert result.exit_code == 0 and "distinct loop(s) found" in result.output


def test_catalogue_text_and_paths_are_printed_as_they_are(runner, tmp_path):
    # Brackets are rich markup: "[/]" used to crash the table, "[v2]" to vanish;
    # ":ok:" is an emoji code, and a closing backslash came out doubled.
    catalogue = tmp_path / "mine.json"
    catalogue.write_text(json.dumps({"pieces": [{
        "id": "arc[/]", "name": "My arc [v2] :ok: v2\\", "part_numbers": ["[x]"], "width": 64,
        "paths": [{"segments": [{"type": "arc", "radius": 256, "degrees": 30}]}]}]}))
    result = runner.invoke(main, ["pieces", "--catalog", str(catalogue)])
    assert result.exit_code == 0, result.output
    assert "arc[/]" in result.output and "My arc [v2]" in result.output
    assert ":ok: v2\\ " in result.output  # the name wraps in its column
    box = tmp_path / "box.json"
    box.write_text(json.dumps({"arc[/]": 12}))
    out = tmp_path / "out [new]"
    cli_args = ["solve", "--catalog", str(catalogue), "--inventory", str(box), "-o", str(out)]
    result = runner.invoke(main, cli_args)
    assert result.exit_code == 0, result.output
    printed = "".join(result.output.split())  # rich wraps long lines
    assert "12xarc[/]" in printed and "out[new]" in printed


@pytest.mark.parametrize("args, tip, not_tip", [
    (["--curve", "12", "--straight", "1", "--use-all"], "without --use-all", None),
    (["--set", "10872", "--slop", "10"], "more curves", "--slop 5"),
    (["--curve", "12", "--min-pieces", "13", "--slop", "2"], "--slop 5", "more curves"),
])
def test_no_loop_advice_suggests_only_what_the_run_did_not_try(runner, args, tip, not_tip):
    result = runner.invoke(main, ["solve", *args])
    assert result.exit_code == 0 and "No closed loop fits" in result.output
    assert tip in result.output
    assert not_tip is None or not_tip not in result.output


def test_saved_pictures_carry_the_same_closure_label_as_the_table(runner, monkeypatch, tmp_path):
    titles = []

    def render(layout, path, title):
        titles.append(title)
        Path(path).write_bytes(b"")

    monkeypatch.setattr(cli, "_get_renderer", lambda required=True: render)
    result = runner.invoke(main, ["solve", "--curve", "12", "--straight", "2", "--switch", "1",
                                  "--reversing", "--top", "50", "-o", str(tmp_path)])
    assert result.exit_code == 0, result.output
    assert any("reversing" in title for title in titles)


def test_reversing_lists_only_teardrops_that_turn_the_train_back(runner, monkeypatch,
                                                                   tmp_path):
    # A branch-tailed teardrop takes the train into its lobe for good, and one
    # without a straight on its tail has nowhere for the stone. Each one listed is
    # saved with its stone: a train there runs forever.
    from dataclasses import replace

    from duplotrain.explore import is_stem_tailed

    results, configs = [], []

    def recording(inventory, catalog, config):
        configs.append(config)
        results.append(solve(inventory, catalog, config))
        return results[-1]

    monkeypatch.setattr(cli, "solve", recording)
    monkeypatch.setattr(cli, "_get_renderer", lambda required=True: None)
    result = runner.invoke(main, ["solve", "--curve", "12", "--switch", "1", "--straight", "2",
                                  "--reversing", "--top", "50", "-o", str(tmp_path)])
    assert result.exit_code == 0, result.output
    # The loops' search comes first, the teardrops' own second.
    teardrops = results[1].solutions
    assert len(teardrops) == 2 and all(
        s.kind == "reversing" and is_stem_tailed(s, default_catalog()) for s in teardrops)
    saved = [layout_from_dict(json.loads(path.read_text()), default_catalog())
             for path in sorted(tmp_path.glob("loop_*.json"))]
    stoned = [layout for layout in saved if layout.accessories]
    assert len(stoned) == 2 and all(classify(layout).locally_looping for layout in stoned)
    # Every other teardrop the same search met is counted once as not listed.
    met = solve({"curve": 12, "switch": 1, "straight": 2}, default_catalog(),
                replace(configs[1], solution_filter=None, max_results=10**6))
    others = sum(s.kind == "reversing" for s in met.solutions) - len(teardrops)
    assert others > 0
    assert (f"Not listed: {others} teardrop(s) that cannot bring the train back"
            in " ".join(result.output.split()))
    # Thirteen pieces of twelve curves, a switch and a straight close no loop; of the
    # four teardrops, three are branch-tailed and the fourth has no tail for the stone.
    result = runner.invoke(main, ["solve", "--curve", "12", "--switch", "1", "--straight", "1",
                                  "--reversing", "--min-pieces", "13", "--max-pieces", "13"])
    printed = " ".join(result.output.split())
    assert result.exit_code == 0 and not table_rows(result.output)
    assert "Not listed: 4 teardrop(s) that cannot bring the train back" in printed


def test_teardrops_are_listed_beside_loops_that_fill_max_results(runner):
    # Shortest first, plain loops alone fill the places: teardrops are looked for in
    # a search of their own, as far as the loops went, so none is longer than the
    # longest loop, and the loops are those listed without reversing.
    args = ["solve", "--curve", "12", "--straight", "4", "--switch", "1", "--max-results", "3"]
    result = runner.invoke(main, [*args, "--reversing"])
    assert result.exit_code == 0, result.output
    rows = table_rows(result.output)
    loops = [row for row in rows if "reversing" not in row[4]]
    teardrops = [row for row in rows if "reversing" in row[4]]
    plain = table_rows(runner.invoke(main, [*args, "--no-reversing"]).output)
    assert sorted(row[1:] for row in loops) == sorted(row[1:] for row in plain)
    assert len(loops) == 3 and teardrops
    assert max(map(pieces_in, teardrops)) <= max(map(pieces_in, loops))
    # Neither search ran out of nodes, and the teardrops were looked for.
    printed = " ".join(result.output.split())
    assert "ran out of --max-nodes" not in printed
    assert "No teardrops were looked for" not in printed
    # From sixteen pieces up, teardrops as long as the loops fill --max-results places
    # of their own, and the loops' hint speaks for both searches.
    result = runner.invoke(main, [*args, "--reversing", "--min-pieces", "16"])
    assert result.exit_code == 0, result.output
    assert sorted(row[4] for row in table_rows(result.output)) == (
        ["exact"] * 3 + ["exact reversing"] * 3)
    assert " ".join(result.output.split()).count("The search stopped at") == 1


@pytest.mark.parametrize("box, turned_on", [
    (["--set", "10874"], []),  # reversing by itself: a direction stone, but no switch
    (["--curve", "12", "--switch", "1"], ["--reversing"]),  # no straight for the stone
    # Each way into a crossing leads on to one track only: no teardrop closing into it
    # brings the train back.
    (["--curve", "12", "--straight", "4", "--crossing", "1"], ["--reversing"]),
    # An inventory file may list a piece the box holds none of.
    ({"curve": 12, "straight": 4, "switch": 0}, ["--reversing"]),
])
def test_a_box_that_cannot_build_a_teardrop_searches_for_loops_alone(runner, tmp_path, box,
                                                                     turned_on):
    # A teardrop closes into a junction a train can leave two ways, a switch, and
    # carries its stone on a straight: a box short of one or the other searches for
    # loops alone, as without reversing, stops at their limit and says nothing of
    # teardrops.
    if isinstance(box, dict):
        listed = tmp_path / "box.json"
        listed.write_text(json.dumps(box))
        box = ["--inventory", str(listed)]
    args = ["solve", *box, "--max-results", "1"]
    reversing = runner.invoke(main, [*args, *turned_on])
    plain = runner.invoke(main, [*args, "--no-reversing"])
    assert reversing.exit_code == plain.exit_code == 0, reversing.output
    printed = " ".join(reversing.output.split())
    assert turned_on or "reversing loops enabled" in printed  # by the set's own stone
    assert states_searched(reversing.output) == states_searched(plain.output)
    assert table_rows(reversing.output) == table_rows(plain.output)
    assert "stopped: result_limit" in printed and (
        "The search stopped at --max-results 1, shortest first; raise it, or --min-pieces, "
        "for longer loops." in printed)
    assert "teardrop" not in printed


def test_teardrops_are_searched_to_the_full_depth_once_every_loop_is_found(runner):
    # A ramp with no arch for its top can stand only at a teardrop's open end: the
    # loops, all found, have 12 pieces and their search went to 14 (every piece but
    # the ramp), yet the teardrop that takes the ramp too, 15 pieces, is listed.
    box = ["solve", "--curve", "12", "--straight", "1", "--switch", "1", "--ramp", "1",
           "--reversing"]
    result = runner.invoke(main, box)
    assert result.exit_code == 0, result.output
    rows = table_rows(result.output)
    assert sorted(pieces_in(row) for row in rows if "reversing" not in row[4]) == [12, 12]
    assert sorted(pieces_in(row) for row in rows if "reversing" in row[4]) == [14, 15]
    assert "stopped" not in result.output
    # The full depth is as far as --max-pieces allows.
    result = runner.invoke(main, [*box, "--max-pieces", "14"])
    assert result.exit_code == 0, result.output
    assert [pieces_in(row) for row in table_rows(result.output) if "reversing" in row[4]] == [14]


def test_under_use_all_teardrops_are_searched_to_their_own_stock(runner, monkeypatch):
    # Every layout under --use-all is as long as its stock, and a teardrop's may hold
    # a ramp at its tail's tip, where no loop can place one: the loops that fill
    # --max-results, of every piece but the ramp, do not hold the teardrops to their
    # length.
    results = []

    def recording(inventory, catalog, config):
        results.append(solve(inventory, catalog, config))
        return results[-1]

    monkeypatch.setattr(cli, "solve", recording)
    result = runner.invoke(main, ["solve", "--curve", "11", "--switch", "1", "--straight", "2",
                                  "--ramp", "1", "--reversing", "--use-all", "--max-results", "1"])
    assert result.exit_code == 0, result.output
    loops, teardrops = (searched.stats for searched in results)
    assert (loops.stop_reason, loops.max_pieces_searched) == ("result_limit", 14)
    assert teardrops.complete and teardrops.max_pieces_searched == 15
    # Each of them, ramp and all, is branch-tailed or has no straight on its tail.
    assert "Not listed: 7 teardrop(s) that cannot bring the train back" in " ".join(
        result.output.split())


def test_teardrops_are_searched_with_the_nodes_the_loops_left(runner, monkeypatch):
    # --max-nodes bounds the whole run: the teardrops' search gets what the loops
    # left, and the states and seconds reported are both searches' together.
    searches = []

    def recording(inventory, catalog, config):
        result = solve(inventory, catalog, config)
        result.stats.duration_s = 1.0 + len(searches)  # one second, then two
        searches.append((config, result))
        return result

    monkeypatch.setattr(cli, "solve", recording)
    args = ["solve", "--curve", "12", "--straight", "4", "--switch", "1", "--reversing",
            "--max-results", "3"]
    result = runner.invoke(main, [*args, "--max-nodes", "1000"])
    assert result.exit_code == 0, result.output
    (_, loops), (config, teardrops) = searches
    assert config.max_nodes == 1000 - loops.stats.nodes
    assert teardrops.stats.stop_reason == "node_limit"
    printed = " ".join(result.output.split())
    assert f"({loops.stats.nodes + teardrops.stats.nodes:,} states searched in 3.0s" in printed
    # Both stopped short: the header names the loops' stop, a note the teardrops'.
    assert "3.0s, stopped: result_limit)" in printed
    assert "The search for teardrops ran out of --max-nodes." in printed
    # Loops that run out of the budget leave the teardrops no search at all, and a
    # note below them says so; without reversing no teardrop was wanted.
    searches.clear()
    result = runner.invoke(main, [*args, "--max-nodes", "100"])
    printed = " ".join(result.output.split())
    assert result.exit_code == 0 and len(searches) == 1, result.output
    assert "stopped: node_limit" in printed and "teardrops ran out" not in printed
    assert table_rows(result.output) and (
        "No teardrops were looked for: the loops used up --max-nodes." in printed)
    plain = runner.invoke(main, [*args, "--no-reversing", "--max-nodes", "100"]).output
    assert table_rows(plain) == table_rows(result.output)
    assert "No teardrops" not in " ".join(plain.split())

    # Loops that finish on the budget's last node did not run out of it: the
    # teardrops are still looked for, with one node.
    def finishing_on_the_last_node(inventory, catalog, config):
        searched = recording(inventory, catalog, config)
        if not config.reversing_loops:
            searched.stats.nodes = config.max_nodes  # the loops' search, every node spent
        return searched

    monkeypatch.setattr(cli, "solve", finishing_on_the_last_node)
    searches.clear()
    result = runner.invoke(main, [*args, "--max-nodes", "1000"])
    assert result.exit_code == 0 and len(searches) == 2, result.output
    assert searches[1][0].max_nodes == 1
    assert "The search for teardrops ran out of --max-nodes." in " ".join(result.output.split())
    # Nor did loops all found by then. Under --use-all no loop takes every piece of
    # this box, but a teardrop does: with nothing listed, a closure may still exist.
    searches.clear()
    result = runner.invoke(main, ["solve", "--curve", "12", "--straight", "1", "--switch", "1",
                                  "--reversing", "--use-all", "--max-nodes", "1000"])
    assert result.exit_code == 0 and len(searches) == 2, result.output
    assert searches[0][1].stats.complete and searches[1][0].max_nodes == 1
    assert not table_rows(result.output) and (
        "No loop found within the search limits; a closure may still exist (a higher "
        "--max-nodes searches further)." in " ".join(result.output.split()))


def test_the_stubs_column_counts_dangling_switch_branches_not_teardrop_tails(runner):
    # A teardrop's tail ends open by design, where its stone clips on; a plain loop
    # through a switch leaves the switch's third branch dangling.
    result = runner.invoke(main, ["solve", "--curve", "12", "--switch", "1", "--straight", "2",
                                  "--reversing"])
    assert result.exit_code == 0, result.output
    rows = table_rows(result.output)
    teardrops = {row[5] for row in rows if "reversing" in row[4]}
    branched = {row[5] for row in rows if "reversing" not in row[4] and "switch" in row[2]}
    assert (teardrops, branched) == ({"0"}, {"1"})


def test_check_names_an_empty_layout_once(runner, tmp_path):
    path = tmp_path / "empty.json"
    path.write_text(json.dumps({"format": "duplotrain-layout/1", "placements": []}))
    result = runner.invoke(main, ["check", str(path)])
    assert result.exit_code == 1 and "Empty layout" in result.output
    assert "open end" not in result.output


def test_check_blames_open_ends_not_the_slop_budget(runner, tmp_path):
    # One forced joint within the budget, and an open switch branch.
    catalog = default_catalog()
    ring = build_chain([(catalog["switch"], 0, 1)] + [(catalog["curve"], 0, 1)] * 5
                       + [(catalog["straight"], 0, 1)] + [(catalog["curve"], 0, 1)] * 6)
    path = tmp_path / "open.json"
    path.write_text(json.dumps(layout_to_dict(ring.join((12, 1), (0, 0), force=True))))
    result = runner.invoke(main, ["check", str(path), "--slop", "1000"])
    assert result.exit_code == 1 and "open end" in result.output
    assert "slop budget" not in result.output
