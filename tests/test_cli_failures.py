"""The CLI reports output it cannot write, a taken port and real open ends plainly."""

import json
import socket

import pytest
from click.testing import CliRunner

from duplotrain.catalog import default_catalog
from duplotrain.cli import main
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, build_chain, layout_to_dict


@pytest.fixture()
def runner():
    return CliRunner()


def test_solve_output_under_a_file_is_refused_without_a_traceback(runner, tmp_path,
                                                                 monkeypatch):
    blocker = tmp_path / "afile.txt"
    blocker.write_text("not a directory")
    # Refused before the search, which could take minutes.
    monkeypatch.setattr("duplotrain.cli.solve", lambda *args: pytest.fail("searched first"))
    result = runner.invoke(main, ["solve", "--curve", "12", "--top", "1",
                                  "-o", str(blocker / "sub")])
    assert result.exit_code == 1 and "cannot create" in result.output
    assert result.exception is None or isinstance(result.exception, SystemExit)


def test_solve_output_that_is_a_directory_is_refused_without_a_traceback(runner, tmp_path):
    (tmp_path / "loop_01.json").mkdir()
    result = runner.invoke(main, ["solve", "--curve", "12", "--top", "1", "-o", str(tmp_path)])
    assert result.exit_code == 1 and "cannot write" in result.output
    assert result.exception is None or isinstance(result.exception, SystemExit)


def test_solve_output_replaces_an_earlier_runs_loops(runner, monkeypatch, tmp_path):
    # A second, smaller run must leave neither the first run's extra loops nor its
    # pictures of other loops beside the JSON it saves; other files stay.
    from duplotrain import cli

    monkeypatch.setattr(cli, "_get_renderer", lambda required=True: None)  # JSON only
    for rank in range(1, 6):
        (tmp_path / f"loop_{rank:02d}.json").write_text("{}")
        (tmp_path / f"loop_{rank:02d}.png").write_bytes(b"old picture")
    (tmp_path / "loop_07.png").mkdir()
    for name in ("notes.txt", "loop_01.json.bak", "loop_1.json"):
        (tmp_path / name).write_text("mine")
    result = runner.invoke(main, ["solve", "--curve", "12", "--top", "3", "-o", str(tmp_path)])
    assert result.exit_code == 0, result.output
    assert sorted(path.name for path in tmp_path.iterdir()) == [
        "loop_01.json", "loop_01.json.bak", "loop_07.png", "loop_1.json", "notes.txt"]
    assert len(json.loads((tmp_path / "loop_01.json").read_text())["placements"]) == 12


def test_a_solve_that_finds_nothing_still_replaces_earlier_results(runner, monkeypatch,
                                                                   tmp_path):
    from duplotrain import cli

    monkeypatch.setattr(cli, "_get_renderer", lambda required=True: None)  # JSON only
    out = tmp_path / "out"
    assert runner.invoke(main, ["solve", "--curve", "12", "-o", str(out)]).exit_code == 0
    assert list(out.glob("loop_*.json"))
    result = runner.invoke(main, ["solve", "--set", "10872", "-o", str(out)])
    assert result.exit_code == 0 and "No closed loop fits" in result.output
    assert not list(out.glob("loop_*"))


def test_gui_on_a_port_in_use_fails_politely(runner):
    with socket.socket() as taken:
        taken.bind(("127.0.0.1", 0))
        taken.listen()
        port = taken.getsockname()[1]
        result = runner.invoke(main, ["gui", "--no-browser", "--port", str(port)])
    assert result.exit_code == 1 and f"cannot serve on port {port}" in result.output
    assert result.exception is None or isinstance(result.exception, SystemExit)


def test_check_reports_open_ends_behind_many_buffer_faces(runner, tmp_path):
    # Three buffered bars list their sealed faces among the first gaps; the half
    # circle's two real open ends must still be reported.
    catalog = default_catalog()
    parts = [build_chain([(catalog["curve"], 0, 1)] * 6)]
    for k in range(3):
        straight = build_chain([(catalog["straight"], 0, 1)], start=Pose.make(x=2000 + 500 * k))
        capped, _ = straight.attach(catalog["buffer"], 0, (0, 1))
        capped, _ = capped.attach(catalog["buffer"], 0, (0, 0))
        parts.append(capped)
    placements, links = [], {}
    for part in parts:
        offset = len(placements)
        placements += part.placements
        links.update({(a + offset, ap): (b + offset, bp)
                      for (a, ap), (b, bp) in part.links.items()})
    layout = Layout(placements, links)
    path = tmp_path / "layout.json"
    path.write_text(json.dumps(layout_to_dict(layout)))
    result = runner.invoke(main, ["check", str(path)])
    assert "2 open end(s)" in result.output
    assert any(f"Open ends {pair}" in result.output
               for pair in ("(0, 0) <-> (5, 1)", "(5, 1) <-> (0, 0)"))


@pytest.mark.parametrize("option, value", [
    ("--min-pieces", "-1"), ("--max-results", "0"), ("--max-nodes", "0"), ("--slop", "-1"),
])
def test_solve_rejects_out_of_range_options_like_the_other_commands(runner, option, value):
    result = runner.invoke(main, ["solve", "--curve", "12", option, value])
    assert result.exit_code == 2 and option in result.output
