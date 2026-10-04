"""Check layout: a read-only report of closure, of overlaps under the solver's height
rules and of track and stone shortages, sandbox or not.

The bounds-index path is compared with the all-pairs scan in test_editor_optimisations.py.
"""

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.editor import Session
from duplotrain.editor_tools import check_session
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, Placement, build_chain
from tests.editor_support import unchanged


def test_diagnostics_distinguish_closed_from_overlapping_and_missing():
    c = default_catalog()
    layout = build_chain([(c["curve"], 0, 1)] * 24).join((0, 0), (23, 1))
    s = Session(history=[layout], inventory={"curve": 2})
    before = unchanged(s)
    report = check_session(s)
    assert report["connector_closed"]
    assert report["overlaps"]
    assert report["missing"][0]["missing"] == 22
    assert report["overlap_check_complete"]
    assert unchanged(s) == before


@pytest.mark.parametrize("z,expected", [(0, True), (200, False)])
def test_diagnostics_use_existing_height_collision_rules(z, expected):
    c = default_catalog()
    layout = Layout((Placement(c["straight"], Pose.make()),
                     Placement(c["straight"], Pose.make(z=z))))
    report = check_session(Session(history=[layout]))
    assert bool(report["overlaps"]) == expected


def test_ends_that_meet_unjoined_are_no_overlap():
    # A ring closed by hand but never joined: its two ends only touch.
    c = default_catalog()
    ring = build_chain([(c["curve"], 0, 1)] * 12)
    report = check_session(Session(history=[ring]))
    assert not report["overlaps"] and len(report["open_ends"]) == 2


def test_bridge_ends_that_meet_but_cannot_join_are_a_bad_joint_not_an_overlap():
    # A straight butted against a ramp's top: the pieces only touch, but a ramp's
    # top takes only an arch's foot. Close all gaps, which joins every pair of
    # meeting ends, cannot start.
    from duplotrain.editor import dispatch_session

    c = default_catalog()
    layout, _ = Layout().with_piece(c["ramp"], Pose.make())
    straight = c["straight"]
    layout, flat = layout.with_piece(straight, straight.frame_for(0, layout.pose_of((0, 1))))
    session = Session(history=[layout])
    report = check_session(session)
    assert not report["overlaps"] and not report["connector_closed"]
    assert [(j["a"], j["b"], j["problems"]) for j in report["joint_issues"]] == [
        ([0, 1], [flat, 0], ["mismatched bridge joint"])]
    with pytest.raises(ValueError, match=r"Pieces #1 and #2 meet but cannot join .*; move one"):
        dispatch_session(session, "/api/search/start",
                         {"revision": session.revision, "all_gaps": True})


def test_diagnostics_reports_stone_shortages_even_in_sandbox():
    s = Session(unlimited=True, stones={})
    s.attach("straight", 0, None)
    s.toggle_stone(0, "stone_stop")
    report = check_session(s)
    assert report["sandbox"]
    assert report["missing"][0]["piece"] == "stone_stop"
    assert report["missing"][0]["missing"] == 1
