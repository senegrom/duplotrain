"""Real presentation metadata supplies marker heights without changing saved layouts."""
from fractions import Fraction

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.editor import Session
from duplotrain.exact import Alg
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, Placement


@pytest.mark.parametrize("piece_id", ["straight", "ramp", "span", "switch", "crossing"])
@pytest.mark.parametrize("height", [0, Fraction(768, 5), -256])
@pytest.mark.parametrize("heading", [0, 6])
def test_marker_height_metadata_matches_real_geometry(piece_id, height, heading):
    catalog = default_catalog()
    placement = Placement(catalog[piece_id], Pose(Alg(100), Alg(-200), Alg(height), heading))
    session = Session(catalog=catalog, history=[Layout([placement])])
    snapshot = session.snapshot()
    state = session.state()
    drawing = state["layout"]["placements"][0]
    midpoint = drawing["lines"][0][len(drawing["lines"][0]) // 2]
    assert drawing["mid"] == midpoint[:2]  # The existing two-dimensional contract remains.
    assert drawing["mid_z"] == midpoint[2]
    assert [port["z"] for port in drawing["ports"]] == [
        round(float(placement.port_pose(port).z), 2)
        for port in range(len(placement.piece.ports))
    ]
    # A fresh response owns fresh containers; metadata must not alter exact saved state.
    drawing["mid_z"] = 999999
    drawing["ports"][0]["z"] = 999999
    fresh = session.state()["layout"]["placements"][0]
    assert fresh["mid_z"] == midpoint[2]
    assert fresh["ports"][0]["z"] == round(float(placement.port_pose(0).z), 2)
    assert session.snapshot() == snapshot
