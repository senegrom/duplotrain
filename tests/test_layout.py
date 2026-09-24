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


def test_bridge_chain_returns_to_ground(catalog):
    """Ramp up, arch up to the crest, arch down, ramp down: 1024 mm, back at z=0."""
    ramp, span = catalog["ramp"], catalog["span"]
    layout = build_chain(
        [(ramp, 0, 1), (span, 0, 1), (span, 1, 0), (ramp, 1, 0)]
    )
    end = chain_end(layout)
    assert end == ORIGIN.then(1024, 0, 0, 0)  # 8 straights of run, back at z=0
    # Ramp top sits at 3 bricks; the crest between the two arches at 4 bricks.
    ramp_top = layout.placements[1].port_pose(0)
    assert float(ramp_top.z) == pytest.approx(57.6)
    crest = layout.placements[1].port_pose(1)
    assert float(crest.z) == pytest.approx(76.8)


def test_level_crossing_reports_its_plate_footprint(catalog):
    """Bounds grow perpendicular to travel plus the declared end overhang: the level
    crossing is a 160 x 160 plate, not 288 x 160."""
    lc = build_chain([(catalog["level_crossing"], 0, 1)])
    width, height = lc.size()
    assert (round(width), round(height)) == (160, 160)


def test_overhanging_plates_refuse_to_mate(catalog):
    lc = catalog["level_crossing"]
    layout = build_chain([(lc, 0, 1)])
    with pytest.raises(ValueError, match="overlap"):
        layout.attach(lc, 0, layout.open_ends()[-1])
    # A plain straight on the same end is fine.
    layout.attach(catalog["straight"], 0, layout.open_ends()[-1])


def test_bridge_dimensions_are_exact(catalog):
    from fractions import Fraction

    from duplotrain.exact import Alg

    ramp, span = catalog["ramp"], catalog["span"]
    assert ramp.exit_delta(0, 1)[2] == Alg(Fraction(288, 5))  # 57.6 mm
    assert span.exit_delta(0, 1)[2] == Alg(Fraction(96, 5))  # 19.2 mm
    layout = build_chain([(ramp, 0, 1), (span, 0, 1), (span, 1, 0), (ramp, 1, 0)])
    crest = layout.placements[1].port_pose(1)
    assert crest.z == Alg(Fraction(384, 5))  # exactly 76.8 mm at the mid-bridge joint


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


@pytest.mark.parametrize("links", [
    [[0, 1, 1, 0], [0, 1, 2, 0]],  # one end linked to two others: asymmetric
    [[0, 1, 1, 0], [2, 0, 1, 0]],  # the same, named from the other side
    [[0, 1, 1, 0], [1, 0, 0, 1]],  # the same joint listed twice
    [[1, 1, 1, 1]],                # an end linked to itself
])
def test_import_rejects_ends_linked_more_than_once(catalog, links):
    data = layout_to_dict(build_chain([(catalog["straight"], 0, 1)] * 3))
    data["links"] = links
    with pytest.raises(ValueError, match="linked twice"):
        layout_from_dict(data, catalog)


@pytest.mark.parametrize("links", [[[1, 1, 0, 0]], [[0, 0, 1, 1]]])
def test_import_rejects_a_link_onto_a_sealed_buffer_face(catalog, links):
    # The buffer's port 1 is its bumper: it never mates, whichever side names it.
    layout = build_chain([(catalog["straight"], 0, 1), (catalog["buffer"], 0, 1)])
    assert layout.is_sealed((1, 1))
    data = layout_to_dict(layout)
    data["links"] = [[0, 1, 1, 0], *links]
    with pytest.raises(ValueError, match="sealed faces cannot be linked"):
        layout_from_dict(data, catalog)
    data["links"] = [[0, 1, 1, 0]]
    assert layout_from_dict(data, catalog) == layout


def test_walk_traverses_the_loop(catalog):
    curve = catalog["curve"]
    layout = build_chain([(curve, *LEFT)] * 12)
    layout = layout.join(layout.open_ends()[1], layout.open_ends()[0])
    steps = list(layout.walk(start=(0, 0)))
    assert len(steps) == 12
    assert [i for i, _, _ in steps] == list(range(12))


def test_joint_audit_since_is_the_full_audit_restricted_to_later_placements(catalog):
    from duplotrain.geometry import Pose
    from duplotrain.layout import Placement

    curve = catalog["curve"]
    layout = build_chain([(curve, *LEFT)] * 5)
    a, b = layout.open_ends()
    layout = layout.join(a, b, force=True)  # a forced joint between pieces 0 and 4
    p = layout.placements[2]  # and one piece a millimetre off: two more forced joints
    shifted = Placement(p.piece, Pose.make(p.frame.x + 1, p.frame.y, p.frame.z, p.frame.heading))
    layout = Layout(layout.placements[:2] + (shifted,) + layout.placements[3:],
                    dict(layout.links), layout.accessories)
    full = layout.joint_issues()
    assert sorted(tuple(sorted((i["a"][0], i["b"][0]))) for i in full) == [(0, 4), (1, 2), (2, 3)]
    port_poses = {end: layout.pose_of(end) for pair in layout.links.items() for end in pair}
    for since in range(len(layout) + 2):
        expected = [i for i in full if max(i["a"][0], i["b"][0]) >= since]
        assert layout.joint_issues(since=since) == expected
        assert layout.joint_issues(port_poses, since=since) == expected
    assert layout.joint_issues(since=3) == [full[0], full[2]]
    assert layout.joint_issues(since=5) == []


def test_track_length_needs_no_congruence_origin(monkeypatch, catalog):
    # The exact average of points with unrelated denominators can run to tens of
    # thousands of digits, and a length never needs that origin.
    import math

    import duplotrain._congruence as congruence

    monkeypatch.setattr(congruence, "_normalise", lambda layout: pytest.fail("origin computed"))
    circle = build_chain([(catalog["curve"], 0, 1)] * 12)
    assert circle.track_length() == pytest.approx(2 * math.pi * 256)


@pytest.mark.parametrize("columns", [20, 1])
def test_the_closest_gaps_come_first_without_measuring_every_pair(monkeypatch, catalog, columns):
    # A grid of loose crossings, or a single column of them, plus buffers whose
    # sealed faces must never be paired. Equal gaps keep end order.
    from duplotrain.geometry import Pose
    from duplotrain.layout import Placement

    placements = [Placement(catalog["crossing"], Pose.make(400 * (i % columns), 400 * (i // columns)))
                  for i in range(100)]
    placements += [Placement(catalog["buffer"], Pose.make(-1000, 300 * i)) for i in range(4)]
    layout = Layout(tuple(placements))
    full = layout.gaps()
    assert not any(layout.is_sealed(end) for a, b, _gap in full for end in (a, b))
    measured = []
    original = Pose.distance_to
    monkeypatch.setattr(Pose, "distance_to",
                        lambda self, other: measured.append(1) or original(self, other))
    for limit in (1, 5, 12):
        assert layout.gaps(limit=limit) == full[:limit]
    assert len(measured) < len(full) // 20
    assert layout.gaps(limit=0) == [] and len(layout.gaps(limit=len(full) + 7)) == len(full)
