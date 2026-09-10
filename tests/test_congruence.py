"""Curve identity must be independent of pieces, segment splits and traversal."""

from dataclasses import replace

import pytest

from duplotrain import Layout, Placement, Pose, build_chain, default_catalog, parse_piece
from duplotrain._congruence import _compare
from duplotrain.exact import Alg
from duplotrain.explore import congruence_key
from duplotrain.pieces import Arc, Straight


def track(segments, *, start=None):
    piece = parse_piece({"id": "custom", "width": 64, "paths": [{"segments": segments}]})
    return build_chain([(piece, 0, 1)], start=start)


def line(run):
    return {"type": "straight", "run": run}


def arc(degrees):
    return {"type": "arc", "radius": 128, "degrees": degrees}


def transform(layout, heading, mirror):
    placements = []
    for placement in layout:
        piece, frame = placement.piece, placement.frame
        if mirror:
            # Reflect the local paths as well as the placement frame: changing
            # only the frame is not a reflection of a handed curve.
            paths = tuple(replace(
                path, start=path.start.mirrored(),
                segments=tuple(replace(seg, degrees=-seg.degrees) if type(seg) is Arc else seg
                               for seg in path.segments),
            ) for path in piece.paths)
            ports = tuple(replace(port, pose=port.pose.mirrored()) for port in piece.ports)
            piece = replace(piece, paths=paths, ports=ports)
            frame = frame.mirrored()
        frame = frame.rotated_about_origin(heading)
        frame = Pose.make(frame.x + 431, frame.y - 781, frame.z + 19, frame.heading)
        placements.append(Placement(piece, frame))
    return Layout(tuple(placements), dict(layout.links), layout.accessories)


@pytest.mark.parametrize("spacing", [7.0, 8.0, 11.3])
@pytest.mark.parametrize("kind", ["line", "arc", "ramp"])
def test_arbitrary_primitive_splits_are_congruent_after_all_rigid_motions(kind, spacing):
    if kind == "line":
        whole, segments = [line(256)], [line("73/3"), line("695/3")]
    elif kind == "arc":
        whole, segments = [arc(-105)], [arc(-15), arc(-30), arc(-60)]
    else:
        whole = [{"type": "ramp", "run": 256, "rise": 28}]
        segments = [
            {"type": "ramp", "run": 67, "rise": "469/64"},
            {"type": "ramp", "run": 189, "rise": "1323/64"},
        ]
    # Test both multiple segments in one piece and splits into separate pieces.
    split = track(segments)
    separate = build_chain([
        (parse_piece({"id": f"part{i}", "paths": [{"segments": [seg]}]}), 0, 1)
        for i, seg in enumerate(segments)
    ])
    expected = congruence_key(track(whole), spacing)
    for candidate in (split, separate):
        for heading in range(24):
            for mirror in (False, True):
                assert congruence_key(transform(candidate, heading, mirror), spacing) == expected


def test_mixed_curve_duplicates_and_reordered_placements_do_not_change_key():
    catalog = default_catalog()
    layout = build_chain([(catalog[pid], 0, 1) for pid in (
        "straight", "straight", "curve", "ramp", "span", "curve",
    )])
    expected = congruence_key(layout)
    # Geometry is a union: repeated routes/placements carry no multiplicity.
    duplicate = Layout(tuple(reversed(layout.placements)) + layout.placements)
    for heading in range(24):
        for mirror in (False, True):
            assert congruence_key(transform(duplicate, heading, mirror)) == expected


def test_partial_overlap_on_a_line_does_not_insert_extra_boundaries():
    whole = track([line(256)])
    inside = track([line(96)], start=Pose.make(33, 0, 0))
    assert congruence_key(Layout(whole.placements + inside.placements)) == congruence_key(whole)
    overlap = track([line(128)], start=Pose.make(64, 0, 0))
    split = track([line(128)])
    assert congruence_key(Layout(split.placements + overlap.placements)) == (
        congruence_key(track([line(192)]))
    )


def test_a_gap_or_change_in_grade_is_not_merged():
    first = track([line(100)])
    second = track([line(100)], start=Pose.make(101, 0, 0))
    assert congruence_key(Layout(first.placements + second.placements)) != (
        congruence_key(track([line(201)]))
    )
    bent = track([{"type": "ramp", "run": 128, "rise": 28}, line(128)])
    straight_grade = track([{"type": "ramp", "run": 256, "rise": 28}])
    assert congruence_key(bent) != congruence_key(straight_grade)


@pytest.mark.parametrize("turn", [-360, 360, 720])
def test_full_circles_share_one_sector_union(turn):
    full = track([arc(turn)])
    split = track([arc(15 if turn > 0 else -15)] * (abs(turn) // 15))
    assert congruence_key(full) == congruence_key(split) == congruence_key(track([arc(360)]))


def test_degenerate_segments_do_not_reweight_a_line_or_arc():
    assert congruence_key(track([line(64), line(0), line(192)])) == (
        congruence_key(track([line(256)]))
    )
    assert congruence_key(track([arc(30), arc(0), arc(60)])) == (
        congruence_key(track([arc(90)]))
    )


def test_unknown_segment_subclasses_keep_their_own_shape():
    class Bowed(Straight):
        def sample(self, spacing):
            return [(x, 10.0 if 0 < x < float(self.run) else 0.0, z, h)
                    for x, _y, z, h in super().sample(spacing)]

    piece = default_catalog()["straight"]
    path = replace(piece.paths[0], segments=(Bowed(Alg(128)),))
    custom = replace(piece, paths=(path,))
    assert congruence_key(build_chain([(custom, 0, 1)])) != (
        congruence_key(build_chain([(piece, 0, 1)]))
    )


def test_interval_ordering_does_not_round_away_a_nonzero_field_element():
    p, q = 1, 0
    for _ in range(80):
        p, q = p + 2 * q, p + q
    assert p * p - 2 * q * q == 1
    tiny_negative = Alg(-p, q)
    assert tiny_negative != 0
    assert _compare(tiny_negative, Alg(0)) < 0
    assert _compare(-tiny_negative, Alg(0)) > 0
    assert _compare(tiny_negative, tiny_negative) == 0


@pytest.mark.parametrize("spacing", [0, -1, float("inf"), float("nan")])
def test_invalid_congruence_spacing_is_rejected(spacing):
    with pytest.raises(ValueError, match="spacing"):
        congruence_key(track([line(128)]), spacing)
