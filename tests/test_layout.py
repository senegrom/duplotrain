"""Layout assembly, the classic identities, and serialisation."""

import copy
import math
import pickle
from dataclasses import replace
from fractions import Fraction

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.exact import Alg
from duplotrain.geometry import ORIGIN, Pose
from duplotrain.gui import Session
from duplotrain.layout import Layout, Placement, build_chain, layout_from_dict, layout_to_dict
from duplotrain.pieces import Arc, Straight, parse_piece
from duplotrain.validation import check_layout_json
from tests.test_congruence import built, track, transform


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


def test_mating_hints_never_offer_overlapping_road_plates(catalog):
    layout, a = Layout().with_piece(catalog["level_crossing"], Pose.make())
    layout, b = layout.with_piece(catalog["level_crossing"], Pose.make(x=128))
    layout, c = layout.with_piece(catalog["straight"], Pose.make(x=128))
    assert ((a, 1), (b, 0)) not in layout.matable_pairs()
    assert ((a, 1), (c, 0)) in layout.matable_pairs()
    assert [[a, 1], [b, 0]] not in Session(history=[layout]).state()["matable"]
    for first, second in layout.matable_pairs():
        layout.join(first, second)  # each advertised joint can actually be made


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


def test_even_a_forced_joint_cannot_link_an_end_to_itself(catalog):
    layout = build_chain([(catalog["straight"], 0, 1)])
    with pytest.raises(ValueError, match="itself"):
        layout.join((0, 0), (0, 0), force=True)
    assert not layout.links


def test_layout_copies_and_freezes_constructor_collections():
    chain = build_chain([(default_catalog()["straight"], 0, 1)] * 2)
    placements, links, stones = list(chain.placements), dict(chain.links), [[0, "stone_horn"]]
    layout = Layout(placements, links, stones)
    placements.clear()
    links.clear()
    stones[0][1] = "stone_stop"
    assert layout.placements == chain.placements
    assert layout.links == chain.links
    assert layout.accessories == ((0, "stone_horn"),)
    with pytest.raises(TypeError):
        layout.links[(0, 1)] = (1, 1)


@pytest.mark.parametrize("restore", [copy.copy, copy.deepcopy,
                                     lambda obj: pickle.loads(pickle.dumps(obj))])
def test_immutable_layout_still_supports_copy_and_pickle(restore):
    chain = build_chain([(default_catalog()["straight"], 0, 1)] * 2)
    restored = restore(chain)
    assert restored == chain
    with pytest.raises(TypeError):
        restored.links[(0, 1)] = (1, 1)


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


@pytest.mark.parametrize("coefficient", [
    "1e5000", "1e999999999", "1/0", "0/0", "nan", "inf", "9" * 49,
    10**100, "1000000001", 0.5, True, None, {}, [],
])
def test_untrusted_coefficients_fail_before_layout_construction(coefficient):
    catalog = default_catalog()
    data = layout_to_dict(build_chain([(catalog["straight"], 0, 1)]))
    data["placements"][0]["frame"]["x"][0] = coefficient
    with pytest.raises(ValueError):
        check_layout_json(data)
    with pytest.raises(ValueError):
        layout_from_dict(data, catalog)


def test_exact_rationals_remain_supported():
    catalog = default_catalog()
    data = layout_to_dict(build_chain([(catalog["curve"], 0, 1)]))
    data["placements"][0]["frame"]["x"] = ["1/3", "-2/7", "3/11", "0"]
    assert layout_to_dict(layout_from_dict(data, catalog)) == data


def test_coefficient_arity_and_format_version_are_checked():
    data = layout_to_dict(Session().layout)
    data["format"] = "duplotrain-layout/99"
    with pytest.raises(ValueError, match="format"):
        check_layout_json(data)
    data = layout_to_dict(build_chain([(default_catalog()["straight"], 0, 1)]))
    data["placements"][0]["frame"]["x"] = ["0"] * 3
    with pytest.raises(ValueError, match="exactly 4"):
        check_layout_json(data)


def test_walk_traverses_the_loop(catalog):
    curve = catalog["curve"]
    layout = build_chain([(curve, *LEFT)] * 12)
    layout = layout.join(layout.open_ends()[1], layout.open_ends()[0])
    steps = list(layout.walk(start=(0, 0)))
    assert len(steps) == 12
    assert [i for i, _, _ in steps] == list(range(12))


def straights(count):
    straight = default_catalog()["straight"]
    return Layout(tuple(Placement(straight, Pose.make(x=128 * i)) for i in range(count)))


def test_exact_pose_index_agrees_with_pairwise_reference():
    catalog = default_catalog()
    layout = Layout()
    # Includes irrational coordinates, all headings, ramps, sealed buffer ends,
    # duplicate positions, different heights and an almost-but-not-exact match.
    for i in range(24):
        piece = catalog[("straight", "curve", "ramp", "buffer")[i % 4]]
        frame = Pose.make(x=(i % 3) * 128, y=(i % 2) * 128, z=i % 2, heading=i)
        layout, _ = layout.with_piece(piece, frame)
    for x, z in [(128, 0), (128, 0), (128, 1), (128 + Fraction(1, 10**20), 0)]:
        layout, _ = layout.with_piece(catalog["straight"], Pose.make(x=x, z=z))
    layout, _ = layout.with_piece(catalog["straight"], Pose.make())
    ends = layout.connectable_ends()
    expected = [(a, b) for i, a in enumerate(ends) for b in ends[i + 1:]
                if layout.pose_of(a).connects_to(layout.pose_of(b))]
    assert expected
    assert layout.matable_pairs() == expected
    a, b = expected[0]
    linked = layout.join(a, b)
    assert all(a not in pair and b not in pair for pair in linked.matable_pairs())


def test_pose_index_computes_each_endpoint_once(monkeypatch):
    layout = straights(128)
    calls = []
    original = Layout.pose_of

    def counted(self, end):
        calls.append(end)
        return original(self, end)

    monkeypatch.setattr(Layout, "pose_of", counted)
    pairs = layout.matable_pairs()
    assert len(pairs) == 127
    assert calls == layout.connectable_ends()
    assert Session(history=[layout]).state()["matable"] == [
        [list(a), list(b)] for a, b in pairs
    ]


def test_track_length_needs_no_congruence_origin(monkeypatch, catalog):
    # The exact average of points with unrelated denominators can run to tens of
    # thousands of digits, and a length never needs that origin.
    import math

    import duplotrain._congruence as congruence

    monkeypatch.setattr(congruence, "_normalise", lambda layout: pytest.fail("origin computed"))
    circle = build_chain([(catalog["curve"], 0, 1)] * 12)
    assert circle.track_length() == pytest.approx(2 * math.pi * 256)


@pytest.mark.parametrize("pid", list(default_catalog()))
def test_total_length_includes_every_stock_route(pid):
    piece = default_catalog()[pid]
    layout, _ = Layout().with_piece(piece, ORIGIN)
    assert layout.track_length() == pytest.approx(sum(path.length() for path in piece.paths))


@pytest.mark.parametrize("kind", ["straight", "ramp", "arc"])
def test_length_unions_shared_paths_and_uneven_splits(kind):
    if kind == "arc":
        whole = [{"type": "arc", "radius": 128, "degrees": 90}]
        split = [{"type": "arc", "radius": 128, "degrees": d} for d in (15, 30, 45)]
        expected = 64 * math.pi
    elif kind == "ramp":
        whole = [{"type": "ramp", "run": 256, "rise": 28}]
        split = [{"type": "ramp", "run": run, "rise": rise}
                 for run, rise in ((67, "469/64"), (189, "1323/64"))]
        expected = math.hypot(256, 28)
    else:
        whole = [{"type": "straight", "run": "2559/10"}]
        split = [{"type": "straight", "run": run} for run in ("73/3", "6947/30")]
        expected = 255.9
    piece = parse_piece({"id": "duplicate", "paths": [
        {"segments": whole}, {"segments": split},
    ]})
    layout, _ = Layout().with_piece(piece, ORIGIN)
    for heading in range(24):
        for mirror in (False, True):
            moved = transform(layout, heading, mirror, dx=Alg(431, 0, 2))
            assert moved.track_length() == pytest.approx(expected)


def test_length_includes_both_arms_but_counts_a_shared_prefix_once():
    piece = parse_piece({"id": "branch", "paths": [
        {"segments": [{"type": "straight", "run": 64},
                      {"type": "arc", "radius": 128, "degrees": d}]}
        for d in (30, -30)
    ]})
    layout, _ = Layout().with_piece(piece, ORIGIN)
    assert layout.track_length() == pytest.approx(64 + 128 * math.pi / 3)


def test_length_unions_partial_overlaps_but_not_gaps_or_parallel_layers():
    first = track([{"type": "straight", "run": 100}])
    second = track([{"type": "straight", "run": 100}], start=Pose.make(60, 0, 0))
    gap = track([{"type": "straight", "run": 100}], start=Pose.make(101, 0, 0))
    raised = track([{"type": "straight", "run": 100}], start=Pose.make(0, 0, 1))
    assert Layout(first.placements + second.placements).track_length() == 160
    assert Layout(first.placements + gap.placements).track_length() == 200
    assert Layout(first.placements + raised.placements).track_length() == 200
    assert Layout(first.placements * 2).track_length() == 100
    assert Layout().track_length() == 0


@pytest.mark.parametrize("turn", [-720, -360, 360, 720])
def test_multi_turn_arc_length_counts_its_curve_once(turn):
    layout = built([Arc(Alg(128), turn)])  # beyond what a catalogue accepts
    assert layout.track_length() == pytest.approx(256 * math.pi)


def test_unknown_segment_uses_declared_length_not_its_endpoint_distance():
    class Measured(Straight):
        def length(self):
            return 177.0

    piece = default_catalog()["straight"]
    path = replace(piece.paths[0], segments=(Measured(Alg(128)),))
    custom = replace(piece, paths=(path,))
    assert build_chain([(custom, 0, 1)]).track_length() == 177.0


@pytest.mark.parametrize("columns", [20, 1])
def test_the_closest_gaps_come_first_without_measuring_every_pair(monkeypatch, catalog, columns):
    # A grid of loose crossings, or a single column of them, plus buffers whose
    # sealed faces must never be paired. Equal gaps keep end order.
    from duplotrain.geometry import Pose
    from duplotrain.layout import Placement

    placements = [
        Placement(catalog["crossing"], Pose.make(400 * (i % columns), 400 * (i // columns)))
        for i in range(100)
    ]
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
