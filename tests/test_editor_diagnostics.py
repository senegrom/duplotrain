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


def test_diagnostics_reports_stone_shortages_even_in_sandbox():
    s = Session(unlimited=True, stones={})
    s.attach("straight", 0, None)
    s.toggle_stone(0, "stone_stop")
    report = check_session(s)
    assert report["sandbox"]
    assert report["missing"][0]["piece"] == "stone_stop"
    assert report["missing"][0]["missing"] == 1
