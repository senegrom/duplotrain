"""Layout assembly, the classic identities, and serialisation."""

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.exact import Alg
from duplotrain.geometry import ORIGIN
from duplotrain.layout import Layout, build_chain, layout_from_dict, layout_to_dict


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def chain_end(layout: Layout) -> tuple:
    """(pose of the last piece's open exit)."""
    open_ends = layout.open_ends()
    # build_chain leaves exactly the first entry and last exit open.
    return layout.pose_of(open_ends[-1])


LEFT = (0, 1)  # enter a curve at port a: turn left
RIGHT = (1, 0)  # enter at port b: turn right


def test_twelve_curves_close_a_circle(catalog):
    curve = catalog["curve"]
    layout = build_chain([(curve, *LEFT)] * 12)
    end = chain_end(layout)
    assert end == ORIGIN  # back at the anchor, exactly
    closed = layout.join(layout.open_ends()[1], layout.open_ends()[0])
    assert closed.is_closed
    # Outer diameter of the circle: centreline square of 512 plus one track width.
    width, height = closed.size()
    assert width == pytest.approx(512 + 64, abs=1.0)
    assert height == pytest.approx(512 + 64, abs=1.0)


def test_classic_starter_oval_closes_exactly(catalog):
    """12 curves + 4 straights: the layout in every DUPLO starter set."""
    curve, straight = catalog["curve"], catalog["straight"]
    pieces = (
        [(straight, 0, 1)] * 2
        + [(curve, *LEFT)] * 6
        + [(straight, 0, 1)] * 2
        + [(curve, *LEFT)] * 6
    )
    layout = build_chain(pieces)
    assert chain_end(layout) == ORIGIN
    closed = layout.join(layout.open_ends()[1], layout.open_ends()[0])
    assert closed.is_closed
    width, height = closed.size()
    # 832 x 576 mm outer envelope, from the research dossier's arithmetic.
    assert sorted((round(width), round(height))) == [576, 832]


def test_lane_change_identity(catalog):
    """L+R is a lane change: ahead two straights' worth, sideways 2R(1-cos30)."""
    curve = catalog["curve"]
    layout = build_chain([(curve, *LEFT), (curve, *RIGHT)])
    end = chain_end(layout)
    assert end.heading == 0
    assert end.x == Alg(256)
    assert end.y == Alg(512, 0, -256, 0)  # 2 * (256 - 128*sqrt3) ~ 68.6 mm
    assert float(end.y) == pytest.approx(68.595, abs=1e-3)


def test_lrrl_snake_equals_four_straights(catalog):
    """L,R,R,L advances exactly 4 straights with zero net offset."""
    curve = catalog["curve"]
    layout = build_chain(
        [(curve, *LEFT), (curve, *RIGHT), (curve, *RIGHT), (curve, *LEFT)]
    )
    end = chain_end(layout)
    assert end == ORIGIN.then(512, 0, 0, 0)


def test_rrll_is_a_documented_near_miss(catalog):
    """R,R,L,L ('Regel 3') is famously 4.59 mm short of 3.5 straights' advance."""
    curve = catalog["curve"]
    layout = build_chain(
        [(curve, *RIGHT), (curve, *RIGHT), (curve, *LEFT), (curve, *LEFT)]
    )
    end = chain_end(layout)
    assert end.heading == 0
    assert end.x == Alg(0, 0, 256, 0)  # 256*sqrt3 exactly
    assert 3.5 * 128 - float(end.x) == pytest.approx(4.59, abs=0.01)


def test_ramp_chain_returns_to_ground(catalog):
    ramp, span = catalog["ramp"], catalog["span"]
    layout = build_chain(
        [(ramp, 0, 1), (span, 0, 1), (span, 0, 1), (ramp, 1, 0)]
    )
    end = chain_end(layout)
    assert end == ORIGIN.then(1024, 0, 0, 0)  # 8 straights of run, back at z=0
    # Mid-bridge the track is elevated.
    mid = layout.placements[1].port_pose(0)
    assert float(mid.z) == pytest.approx(76.8)


def test_attach_rejects_occupied_end(catalog):
    curve = catalog["curve"]
    layout = build_chain([(curve, *LEFT), (curve, *LEFT)])
    with pytest.raises(ValueError, match="already connected"):
        layout.attach(curve, 0, (0, 1))  # (0,1) is already linked to piece 1


def test_join_rejects_non_meeting_ends(catalog):
    curve = catalog["curve"]
    layout = build_chain([(curve, *LEFT), (curve, *LEFT)])
    a, b = layout.open_ends()
    with pytest.raises(ValueError, match="do not meet"):
        layout.join(a, b)
    forced = layout.join(a, b, force=True)
    assert forced.is_closed


def test_serialisation_round_trip_is_exact(catalog):
    curve, straight = catalog["curve"], catalog["straight"]
    layout = build_chain([(curve, *LEFT)] * 3 + [(straight, 0, 1)])
    data = layout_to_dict(layout)
    rebuilt = layout_from_dict(data, catalog)
    assert rebuilt == layout
    # Exactness survives JSON: the reloaded end pose still compares equal.
    assert rebuilt.pose_of(rebuilt.open_ends()[-1]) == layout.pose_of(layout.open_ends()[-1])


def test_walk_traverses_the_loop(catalog):
    curve = catalog["curve"]
    layout = build_chain([(curve, *LEFT)] * 12)
    layout = layout.join(layout.open_ends()[1], layout.open_ends()[0])
    steps = list(layout.walk(start=(0, 0)))
    assert len(steps) == 12
    assert [i for i, _, _ in steps] == list(range(12))
