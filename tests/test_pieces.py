"""Piece parsing and the derived ports, routes and deltas."""

from fractions import Fraction

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.exact import Alg
from duplotrain.geometry import ORIGIN, degrees_to_steps
from duplotrain.pieces import Arc, parse_length, parse_piece

# The lateral kick of one 30-degree curve: R(1 - cos30) = 256 - 128*sqrt(3).
CURVE_KICK = Alg(256, 0, -128, 0)


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def test_parse_length_forms():
    assert parse_length(128) == Alg(128)
    assert parse_length(152.5) == Alg(Fraction(305, 2))
    assert parse_length("384/5") == Alg(Fraction(384, 5))
    assert parse_length({"alg": [0, 0, -48, 0]}) == -48 * Alg(0, 0, 1, 0)
    # Chord of a 30-degree R=256 arc: 2*256*sin(15).
    chord = parse_length({"chord": {"radius": 256, "degrees": 30}})
    assert float(chord) == pytest.approx(132.5155, abs=1e-3)


def test_straight_geometry(catalog):
    straight = catalog["straight"]
    assert len(straight.ports) == 2
    end = straight.paths[0].end()
    assert end == ORIGIN.then(128, 0, 0, 0)


def test_curve_advances_exactly_one_straight(catalog):
    """The system's design identity: R sin30 = L, so a curve advances 128 mm."""
    curve = catalog["curve"]
    end = curve.paths[0].end()
    assert end.x == Alg(128)
    assert end.y == CURVE_KICK
    assert end.degrees == 30
    assert float(end.y) == pytest.approx(34.2975, abs=1e-3)


def test_curve_entered_backwards_turns_the_other_way(catalog):
    """Genderless connectors: one physical curve is both the left and right turn."""
    curve = catalog["curve"]
    dx, dy, dz, dheading = curve.exit_delta(1, 0)
    assert dx == Alg(128)
    assert dy == -CURVE_KICK
    assert not dz
    assert dheading == degrees_to_steps(-30)


def test_switch_shares_a_stem(catalog):
    switch = catalog["switch"]
    assert len(switch.ports) == 3  # two paths collapsed onto one shared stem
    assert switch.is_junction
    names = [p.name for p in switch.ports]
    assert names == ["stem", "left", "right"]
    # From the stem you may go either way; from a branch, only back to the stem.
    assert {exit_ for exit_, _ in switch.transit(0)} == {1, 2}
    assert {exit_ for exit_, _ in switch.transit(1)} == {0}
    # The two branch exits sit 60 degrees apart, mirror images across the stem axis:
    # both a full straight-length ahead of the stem, kicked sideways opposite ways.
    left = switch.ports[1].pose
    right = switch.ports[2].pose
    assert (left.heading - right.heading) % 24 == degrees_to_steps(60)
    assert left.x == right.x == Alg(128)
    assert left.y == CURVE_KICK
    assert right.y == -CURVE_KICK


def test_crossing_has_two_independent_routes(catalog):
    crossing = catalog["crossing"]
    assert len(crossing.ports) == 4
    # Straight through on each route; never a turn onto the other route.
    assert {exit_ for exit_, _ in crossing.transit(0)} == {1}
    assert {exit_ for exit_, _ in crossing.transit(2)} == {3}
    # Each route is exactly one straight module (BlueBrick-measured, LDraw-calibrated).
    dx, dy, dz, dheading = crossing.exit_delta(0, 1)
    assert (dx, dy, dheading) == (Alg(128), Alg(0), 0)
    # Route B's ports sit at (32, -32*sqrt3) and (96, 32*sqrt3), 60 deg to route A.
    poses = {(p.pose.x, p.pose.y) for p in crossing.ports}
    assert (Alg(32), Alg(0, 0, -32, 0)) in poses
    assert (Alg(96), Alg(0, 0, 32, 0)) in poses


def test_ramp_rises(catalog):
    ramp = catalog["ramp"]
    dx, dy, dz, dheading = ramp.exit_delta(0, 1)
    # 3 DUPLO bricks over 320 mm; a 4-brick rise cannot fit the real part's height.
    assert (float(dx), float(dz)) == (320.0, pytest.approx(57.6))
    # Entered downhill, it descends.
    dx2, _dy2, dz2, _ = ramp.exit_delta(1, 0)
    assert float(dz2) == pytest.approx(-57.6)


def test_span_keeps_rising_to_the_crest(catalog):
    span = catalog["span"]
    dx, _dy, dz, _ = span.exit_delta(0, 1)
    assert (float(dx), float(dz)) == (192.0, pytest.approx(19.2))


def test_a_user_catalogue_overrides_a_built_in_piece_by_id(tmp_path, catalog):
    """The README's own "custom catalogue" example: re-measured bridge ramps."""
    import json

    from duplotrain.catalog import load_catalog

    readme_example = {"pieces": [{
        "id": "ramp",
        "name": "Bridge ramp (my callipers)", "category": "bridge", "width": 64,
        "paths": [{"segments": [{"type": "ramp", "run": 320, "rise": 60}]}],
        "port_names": ["low", "high"],
    }]}
    path = tmp_path / "my-measurements.json"
    path.write_text(json.dumps(readme_example))
    loaded = load_catalog(path)
    ramp = loaded["ramp"]
    assert ramp.name == "Bridge ramp (my callipers)"
    assert [port.name for port in ramp.ports] == ["low", "high"]
    dx, _dy, dz, _heading = ramp.exit_delta(0, 1)
    assert (dx, dz) == (Alg(320), Alg(60))  # not the built-in 57.6 mm rise
    assert catalog["ramp"].exit_delta(0, 1)[2] == Alg(Fraction(288, 5))
    # Every other piece is still the built-in one, in the built-in order.
    assert list(loaded) == list(catalog)
    assert all(loaded[pid] == catalog[pid] for pid in catalog if pid != "ramp")
    # A later file overrides an earlier one, too.
    later = tmp_path / "later.json"
    later.write_text(json.dumps([{**readme_example["pieces"][0], "name": "Later ramp"}]))
    assert load_catalog(path, later)["ramp"].name == "Later ramp"


@pytest.mark.parametrize("degrees", [30.9, -30.9, 30.000000001, "30.9", float("inf"),
                                     float("nan"), True, False, None])
def test_arc_rejects_angle_without_rounding(degrees):
    with pytest.raises(ValueError, match="whole multiple of 15"):
        parse_piece({"id": "bad_arc", "paths": [{"segments": [
            {"type": "arc", "radius": 256, "degrees": degrees},
        ]}]})
    with pytest.raises(ValueError, match="whole multiple of 15"):
        Arc(Alg(256), degrees)


@pytest.mark.parametrize("degrees", [30, 30.0, "30", -300, 390])
def test_integral_arc_angles_retain_their_full_sweep(degrees):
    arc = Arc(Alg(256), degrees)
    assert type(arc.degrees) is int
    assert arc.degrees == int(degrees)
    assert arc.turn_steps == int(degrees) // 15 % 24


@pytest.mark.parametrize("spec", [
    {"start": {"heading_deg": "30.0000000001"}, "segments": [{"type": "straight", "run": 128}]},
    {"segments": [{"type": "straight", "run": {"chord": {"radius": 256,
                                                         "degrees": "60.0000000001"}}}]},
])
def test_catalogue_angles_a_hair_off_the_lattice_are_refused(spec):
    # As arc degrees are: a start heading or chord angle is never snapped.
    with pytest.raises(ValueError, match="not a multiple"):
        parse_piece({"id": "p", "paths": [spec]})


def test_duplicate_piece_ids_rejected():
    from duplotrain.pieces import parse_pieces

    spec = {"id": "twin", "paths": [{"segments": [{"type": "straight", "run": 128}]}]}
    with pytest.raises(ValueError, match="duplicate"):
        parse_pieces([spec, dict(spec)])


def test_unknown_segment_type_rejected():
    with pytest.raises(ValueError, match="unknown segment"):
        parse_piece(
            {"id": "bad", "paths": [{"segments": [{"type": "teleport", "run": 1}]}]}
        )


@pytest.mark.parametrize("change,message", [
    ({"sealed_ports": [0, 1]}, "seals every port"),
    ({"width": float("nan")}, "finite width"),
    ({"end_overhang": float("-inf")}, "non-negative end overhang"),
    ({"paths": [{"segments": [{"type": "straight", "run": "1e16000000"}]}]}, "catalogue number"),
    ({"paths": [{"segments": [{"type": "straight", "run": "1/0"}]}]}, "divides by zero"),
    ({"paths": [{"segments": [{"type": "straight", "run": 20_000}]}]}, "at most 10000 mm"),
    ({"paths": [{"segments": [{"type": "arc", "radius": 256, "degrees": "1e9999"}]}]},
     "whole multiple of 15"),
    # A JSON integer is no text: its own bound applies, wherever a number goes.
    ({"paths": [{"segments": [{"type": "straight", "run": 10**400}]}]}, "512 bits"),
    ({"paths": [{"start": {"x": 10**400}, "segments": [{"type": "straight", "run": 64}]}]},
     "512 bits"),
    ({"paths": [{"segments": [{"type": "straight", "run": {"alg": [0, 10**400, 0, 0]}}]}]},
     "512 bits"),
    ({"width": 10**400}, "finite width"),
    ({"width": True}, "finite width"),
    ({"width": 1001}, "from 8 to 1000 mm"),
    # Narrower tracks could cross between the 8 mm collision samples.
    ({"width": 7.5}, "from 8 to 1000 mm"),
    ({"end_overhang": 1e12}, "at most 1000 mm"),
    # A zero or negative length folds a piece onto itself: it would pass as a loop.
    ({"paths": [{"segments": [{"type": "straight", "run": -128}]}]}, "positive run"),
    ({"paths": [{"segments": [{"type": "straight", "run": 0}]}]}, "positive run"),
    ({"paths": [{"segments": [{"type": "ramp", "run": 0, "rise": 5}]}]}, "positive run"),
    ({"paths": [{"segments": [{"type": "arc", "radius": -256, "degrees": 30}]}]},
     "positive radius"),
    ({"paths": [{"segments": [{"type": "arc", "radius": 256, "degrees": 0}]}]}, "nonzero angle"),
    ({"paths": [{"segments": [{"type": "straight", "run": 8}]}] * 17}, "at most 16 paths"),
    ({"paths": [{"segments": [{"type": "straight", "run": 8}] * 65}]}, "at most 64 segments"),
    ({"paths": [{"start": {"x": 10_001}, "segments": [{"type": "straight", "run": 64}]}]},
     "at most 10000 mm from"),
    # Types are checked, never coerced: "false" is a true string, "10" two ports.
    ({"underpass": "false"}, "true or false"),
    ({"provisional": "no"}, "true or false"),
    ({"sealed_ports": [1.9]}, "list of port numbers"),
    ({"sealed_ports": [True]}, "list of port numbers"),
    ({"sealed_ports": "10"}, "list of port numbers"),
    ({"sealed_ports": 5}, "list of port numbers"),
    ({"name": 5}, "name must be text"),
    ({"part_numbers": [6377]}, "list of texts"),
    ({"port_names": ["a", 1]}, "list of texts"),
    ({"paths": [{"segments": [{"type": "straight", "run": {"alg": "1234"}}]}]},
     "four numbers"),
])
def test_catalogue_values_are_bounded_and_meaningful(change, message):
    spec = {"id": "odd", "paths": [{"segments": [{"type": "straight", "run": 64}]}], **change}
    with pytest.raises(ValueError, match=message):
        parse_piece(spec)


def test_the_bounds_admit_every_value_the_text_format_reads():
    longest = "9" * 60 + "e64"
    assert parse_length(longest) == Alg(Fraction(longest))
    widest = parse_piece({"id": "wide", "width": 1000, "end_overhang": 1000,
                          "paths": [{"segments": [{"type": "straight", "run": 128}]}]})
    assert widest.width == widest.end_overhang == 1000


@pytest.mark.parametrize("piece_id", [None, "", 7])
def test_a_piece_needs_a_text_id(piece_id):
    spec = {"paths": [{"segments": [{"type": "straight", "run": 64}]}]}
    if piece_id is not None:
        spec["id"] = piece_id
    with pytest.raises(ValueError, match="needs an id"):
        parse_piece(spec)
