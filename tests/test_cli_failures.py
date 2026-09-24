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


def test_solve_output_under_a_file_is_refused_without_a_traceback(runner, tmp_path):
    blocker = tmp_path / "afile.txt"
    blocker.write_text("not a directory")
    result = runner.invoke(main, ["solve", "--curve", "12", "--top", "1",
                                  "-o", str(blocker / "sub")])
    assert result.exit_code == 1 and "cannot create" in result.output
    assert result.exception is None or isinstance(result.exception, SystemExit)


def test_solve_output_that_is_a_directory_is_refused_without_a_traceback(runner, tmp_path):
    (tmp_path / "loop_01.json").mkdir()
    result = runner.invoke(main, ["solve", "--curve", "12", "--top", "1", "-o", str(tmp_path)])
    assert result.exit_code == 1 and "cannot write" in result.output
    assert result.exception is None or isinstance(result.exception, SystemExit)


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
