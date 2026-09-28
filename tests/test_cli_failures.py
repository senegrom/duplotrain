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


def test_results_are_shown_before_earlier_results_are_replaced(runner, monkeypatch, tmp_path):
    # An earlier run's file that cannot be deleted (open elsewhere, read-only) must
    # not hide what the search found.
    import click

    from duplotrain import cli

    def locked(out_dir):
        raise click.ClickException("cannot replace the earlier results")

    monkeypatch.setattr(cli, "_clear_earlier_results", locked)
    result = runner.invoke(main, ["solve", "--curve", "12", "-o", str(tmp_path)])
    assert result.exit_code == 1 and "Loops, nicest first" in result.output


def test_render_never_draws_over_its_own_layout_file(runner, tmp_path):
    source = tmp_path / "ring.png"  # a layout saved under a picture's name
    layout = build_chain([(default_catalog()["curve"], 0, 1)] * 12)
    source.write_text(json.dumps(layout_to_dict(layout)))
    result = runner.invoke(main, ["render", str(source)])
    assert result.exit_code == 2 and "would replace the layout file" in result.output
    assert json.loads(source.read_text()) == layout_to_dict(layout)


def test_a_layout_file_takes_at_most_2_mb(runner, tmp_path):
    big = tmp_path / "big.json"
    big.write_bytes(b" " * (2 * 1024 * 1024 + 1))
    result = runner.invoke(main, ["check", str(big)])
    assert result.exit_code == 1 and "larger than 2 MB" in result.output


def test_an_empty_output_name_is_refused_not_ignored(runner):
    result = runner.invoke(main, ["solve", "--curve", "12", "-o", ""])
    assert result.exit_code == 2 and "-o needs a directory name" in result.output


def test_a_format_that_needs_latex_is_reported_politely(tmp_path):
    import click

    from duplotrain import cli

    def pgf(layout, path, **options):  # matplotlib without a LaTeX installation
        raise RuntimeError("'xelatex' not found")

    with pytest.raises(click.ClickException, match="cannot write x.pgf: 'xelatex' not found"):
        cli._write_image(pgf, None, "x.pgf")


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
    ("--slop", "inf"), ("--slop", "nan"), ("--curve", "10001"), ("--top", "-1"),
])
def test_solve_rejects_out_of_range_options_like_the_other_commands(runner, option, value):
    result = runner.invoke(main, ["solve", "--curve", "12", option, value])
    assert result.exit_code == 2 and option in result.output


def test_an_output_directory_that_cannot_be_written_is_refused_before_the_search(
        runner, monkeypatch, tmp_path):
    from duplotrain import cli

    def denied(**kwargs):
        raise PermissionError("Access is denied")

    denying = type("Denied", (), {"TemporaryFile": staticmethod(denied)})
    monkeypatch.setattr(cli, "tempfile", denying)
    monkeypatch.setattr(cli, "solve", lambda *args: pytest.fail("searched first"))
    result = runner.invoke(main, ["solve", "--curve", "12", "-o", str(tmp_path / "out")])
    assert result.exit_code == 1 and "cannot write to" in result.output
