"""A recorded link is not evidence that two physical connectors meet."""

import json
from fractions import Fraction

import pytest
from click.testing import CliRunner

from duplotrain.catalog import default_catalog
from duplotrain.cli import main
from duplotrain.geometry import Pose
from duplotrain.gui import Session
from duplotrain.layout import Layout, Placement, build_chain, layout_from_dict, layout_to_dict


def circle():
    layout = build_chain([(default_catalog()["curve"], 0, 1)] * 12)
    return layout.join(*layout.connectable_ends())


def moved_piece(layout, *, dx=0, dz=0, turn=0):
    placed = list(layout.placements)
    old = placed[0]
    frame = old.frame
    placed[0] = Placement(
        old.piece, Pose(frame.x + dx, frame.y, frame.z + dz, frame.heading + turn)
    )
    return Layout(tuple(placed), layout.links, layout.accessories)


def check_layout(tmp_path, layout, *options):
    path = tmp_path / "layout.json"
    path.write_text(json.dumps(layout_to_dict(layout)))
    return CliRunner().invoke(main, ["check", str(path), *options])


def test_exact_circle_has_no_joint_issues(tmp_path):
    layout = circle()
    assert layout.joint_issues() == []
    result = check_layout(tmp_path, layout)
    assert result.exit_code == 0
    assert "every connector is exactly mated" in result.output


def test_single_straight_fake_closure_is_not_accepted(tmp_path):
    layout = build_chain([(default_catalog()["straight"], 0, 1)])
    layout = layout.join(*layout.connectable_ends(), force=True)
    assert layout.is_closed  # explicitly topological, kept for solver compatibility
    issues = layout.joint_issues()
    assert len(issues) == 1
    assert issues[0]["gap_mm"] == 128
    result = check_layout(tmp_path, layout)
    assert result.exit_code == 1
    assert "Fully linked, but not exactly closed" in result.output
    assert "128 mm" in result.output
    assert "Fully closed" not in result.output


def test_forced_fit_round_trip_keeps_warnings_and_total_slop(tmp_path):
    layout = moved_piece(circle(), dx=1)
    loaded = layout_from_dict(layout_to_dict(layout), default_catalog())
    assert loaded == layout
    assert loaded.joint_issues() == layout.joint_issues()
    assert len(loaded.joint_issues()) == 2
    assert sum(j["gap_mm"] for j in loaded.joint_issues()) == pytest.approx(2)
    for budget in ("0", "1.5"):
        assert check_layout(tmp_path, loaded, "--slop", budget).exit_code == 1
    result = check_layout(tmp_path, loaded, "--slop", "2")
    assert result.exit_code == 0
    assert "Forced fit" in result.output
    assert "physical fit not verified" in result.output
    assert "Fully closed" not in result.output


@pytest.mark.parametrize(("change", "problem"), [
    ({"dz": 1}, "elevation mismatch"), ({"turn": 1}, "heading mismatch"),
])
def test_planar_slop_does_not_hide_incompatible_joints(tmp_path, change, problem):
    layout = moved_piece(circle(), **change)
    assert problem in layout.joint_issues()[0]["problems"]
    result = check_layout(tmp_path, layout, "--slop", "999")
    assert result.exit_code == 1
    assert problem in result.output
    assert "Incompatible" in result.output


def test_sub_display_precision_gap_is_not_mistaken_for_exact():
    layout = moved_piece(circle(), dx=Fraction(1, 10**12))
    assert layout.joint_issues()
    assert not Session(history=[layout]).state()["layout"]["exactly_closed"]


def test_editor_recomputes_geometry_after_session_restore():
    source = Session(history=[moved_piece(circle(), dx=1)])
    restored = Session()
    restored.restore(json.loads(json.dumps(source.snapshot())))
    result = restored.state()["layout"]
    assert result["closed"]
    assert not result["exactly_closed"]
    assert result["joint_issues"] == source.layout.joint_issues()


def test_empty_and_open_layouts_fail_closed_check(tmp_path):
    for layout in (Layout(), build_chain([(default_catalog()["straight"], 0, 1)])):
        result = check_layout(tmp_path, layout)
        assert result.exit_code == 1
        assert "Fully closed" not in result.output


def test_sealed_buffer_faces_are_not_open_connectors(tmp_path):
    catalog = default_catalog()
    layout = build_chain([(catalog["straight"], 0, 1)])
    for end in layout.connectable_ends():
        layout, _ = layout.attach(catalog["buffer"], 0, end)
    assert layout.is_closed
    assert len(layout.open_ends()) == 2  # bumpers, not real open connectors
    result = check_layout(tmp_path, layout)
    assert result.exit_code == 0
    assert "exactly mated" in result.output


def test_imported_overhanging_plates_report_incompatible(tmp_path):
    piece = default_catalog()["level_crossing"]
    layout = build_chain([(piece, 0, 1)])
    host = layout.pose_of((0, 1))
    layout, index = layout.with_piece(piece, piece.frame_for(0, host))
    layout = Layout(layout.placements, {(0, 1): (index, 0), (index, 0): (0, 1)})
    issues = layout.joint_issues()
    assert issues[0]["problems"] == ["overlapping connector plates"]
    result = check_layout(tmp_path, layout, "--slop", "999")
    assert result.exit_code == 1
    assert "overlapping connector plates" in result.output


@pytest.mark.parametrize("budget", ["nan", "inf", "-1"])
def test_slop_must_be_finite_nonnegative(tmp_path, budget):
    result = check_layout(tmp_path, circle(), "--slop", budget)
    assert result.exit_code == 2
