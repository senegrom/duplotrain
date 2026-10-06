"""Piece parsing and the derived ports, routes and deltas."""

import json
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


def test_a_pieces_lowest_point_takes_in_every_path(catalog):
    # Every built-in piece is level or climbs evenly: its lowest point is a port.
    for piece in catalog.values():
        assert piece.minimum_z == min(port.pose.z for port in piece.ports)
    # A custom piece may dip between level ends, or carry a lower route.
    dip = parse_piece({"id": "dip", "paths": [{"segments": [
        {"type": "ramp", "run": 128, "rise": "-1/7"},
        {"type": "ramp", "run": 128, "rise": "1/7"}]}]})
    assert dip.minimum_z == Alg(Fraction(-1, 7))
    lower = parse_piece({"id": "lower", "paths": [
        {"segments": [{"type": "straight", "run": 256}]},
        {"start": {"y": 200, "z": -40}, "segments": [{"type": "straight", "run": 256}]}]})
    assert lower.minimum_z == -40


def test_an_unknown_segment_is_bounded_by_its_own_samples():
    # A Segment subclass built in Python has no exact height profile: its own
    # samples stand in, as they do for its collisions and drawing.
    from dataclasses import dataclass

    from duplotrain.exact import alg
    from duplotrain.pieces import Path, PieceType, Port, Route, Segment

    @dataclass(frozen=True)
    class Sag(Segment):
        def delta(self):
            return alg(128), alg(0), alg(0)

        def length(self):
            return 128.0

        def sample(self, spacing):
            # Level ends, 16 mm down at the middle.
            return [(x, 0.0, -16.0 * (1 - abs(64 - x) / 64), 0.0) for x in range(1, 129)]

    @dataclass(frozen=True)
    class Descent(Segment):
        def delta(self):
            return alg(256), alg(0), alg(Fraction(-288, 5))

        def length(self):
            return 262.4

        def sample(self, spacing):
            # Down 57.6 mm evenly: the last sample, float(-57.6), lies a hair under the end.
            return [(x, 0.0, -57.6 * x / 256, 0.0) for x in range(1, 257)]

    def piece(segment):
        path = Path(ORIGIN, (segment,))
        return PieceType("p", "p", "track", (path,),
                         (Port("a", ORIGIN.reversed()), Port("b", path.end())), (Route(0, 1, 0),))

    assert piece(Sag()).minimum_z == -16
    # Float noise at an exact end is no dip: track ending on the floor stays on it.
    assert piece(Descent()).minimum_z == Alg(Fraction(-288, 5))


@pytest.mark.parametrize("spec", [
    {"id": "x", "paths": "abc"},
    {"id": "x", "paths": [{"segments": [5]}]},
    {"id": "x", "paths": [{"start": "s", "segments": [{"type": "straight", "run": 1}]}]},
    {"id": "x", "paths": [{"segments": "abc"}]},
    # Lengths of the wrong shape are bad input too, never a TypeError.
    {"id": "x", "paths": [{"segments": [{"type": "straight", "run": True}]}]},
    {"id": "x", "paths": [{"segments": [{"type": "straight", "run": None}]}]},
    {"id": "x", "paths": [{"segments": [{"type": "straight", "run": [128]}]}]},
    {"id": "x", "paths": [{"segments": [{"type": "straight", "run": {"chord": 5}}]}]},
    "not a piece",
])
def test_malformed_catalogue_entries_are_bad_input(spec):
    with pytest.raises(ValueError):
        parse_piece(spec)


def test_a_chord_without_its_radius_is_bad_input():
    # parse_length is public: its callers get bad input, not a KeyError.
    with pytest.raises(ValueError, match="cannot read a length from None"):
        parse_length({"chord": {"degrees": 30}})


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
    # A full turn or more: one piece would coil over itself or join its own ends.
    ({"paths": [{"segments": [{"type": "arc", "radius": 256, "degrees": 360}]}]},
     "below a full turn"),
    ({"paths": [{"segments": [{"type": "arc", "radius": 256, "degrees": -390}]}]},
     "below a full turn"),
    ({"paths": [{"segments": [{"type": "arc", "radius": 128, "degrees": 15}] * 24}]},
     "two connectors at one point"),
    ({"paths": [{"segments": [{"type": "straight", "run": 6000}] * 2}]}, "at most 10000 mm long"),
    # Exact signs: this run is -3.2e-14 mm, though its float image is +7.3e-12.
    ({"paths": [{"segments": [{"type": "straight",
                               "run": {"alg": [4114, 11592, 10472, -15777]}}]}]},
     "positive run"),
    ({"paths": [{"segments": [{"type": "straight", "run": {"alg": [0, 0, 1_000_001, 0]}}]}]},
     "at most 1,000,000 in size"),
    # Each 30-degree chord grows the coefficients: the bound applies after it too.
    ({"paths": [{"segments": [{"type": "straight", "run": {"chord": {
        "radius": {"chord": {"radius": 900_000, "degrees": 30}}, "degrees": 30}}}]}]},
     "at most 1,000,000 in size"),
    ({"paths": [{"segments": [{"type": "straight",
                               "run": {"chord": {"radius": 256, "degrees": 45}}}]}]},
     "45 deg is not a multiple of 30 deg"),
    # Catalogue text is printed: no terminal commands in it.
    ({"name": "Arc \x1b]0;title\x07"}, "control characters"),
    ({"id": "odd\x9b2J"}, "control characters"),
    ({"part_numbers": ["6377\r"]}, "control characters"),
    # No terminal can print a lone surrogate, which JSON's \ud800 escape makes.
    ({"notes": "a\ud800b"}, "unpaired surrogates"),
    # A layout names its pieces by id in at most 40 characters: so does a catalogue.
    ({"id": "p" * 41}, "1 to 40 characters"),
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
    ({"port_kinds": ["track"]}, "'odd': 1 port kinds for 2 ports"),
    ({"port_names": ["a"]}, "'odd': 1 port names for 2 ports"),
    ({"port_kinds": ["track", "bridge"]}, "port_kinds must be a list of track"),
    ({"port_kinds": "track"}, "port_kinds must be a list"),
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


@pytest.mark.parametrize("piece_id", [None, "", 7, " ", "\t", "a\nb"])
def test_a_piece_needs_a_text_id(piece_id):
    spec = {"paths": [{"segments": [{"type": "straight", "run": 64}]}]}
    if piece_id is not None:
        spec["id"] = piece_id
    with pytest.raises(ValueError, match="needs an id"):
        parse_piece(spec)


def test_port_kinds_name_how_each_end_joins():
    spec = {"id": "deck", "paths": [{"segments": [{"type": "straight", "run": 64}]}]}
    piece = parse_piece({**spec, "port_kinds": ["arch_foot", "track"]})
    assert [port.kind for port in piece.ports] == ["arch_foot", "track"]
    assert [port.kind for port in parse_piece(spec).ports] == ["track", "track"]
    catalog = default_catalog()
    assert [port.kind for port in catalog["ramp"].ports] == ["track", "ramp_top"]
    assert [port.kind for port in catalog["span"].ports] == ["arch_foot", "track"]
    # A straight has one move, its two readings alike; ends of different kinds
    # make those readings different moves.
    from duplotrain.solver import _moves_for

    assert (len(_moves_for(parse_piece(spec))), len(_moves_for(piece))) == (1, 2)


def test_catalogue_notes_may_run_over_several_lines():
    piece = parse_piece({"id": "note", "notes": "measured twice:\n\tthen cut",
                         "paths": [{"segments": [{"type": "straight", "run": 64}]}]})
    assert piece.notes == "measured twice:\n\tthen cut"


def test_a_catalogue_file_nests_at_most_64_levels(tmp_path):
    from duplotrain.catalog import load_catalog

    path = tmp_path / "deep.json"
    path.write_text("[" * 65 + "]" * 65)
    with pytest.raises(ValueError, match="nested more than 64 levels"):
        load_catalog(path)


def test_a_catalogue_file_takes_at_most_2_mb(tmp_path):
    from duplotrain.catalog import load_catalog

    path = tmp_path / "big.json"
    path.write_bytes(b"[" + b" " * (2 * 1024 * 1024) + b"]")
    with pytest.raises(ValueError, match="larger than 2 MB"):
        load_catalog(path)


@pytest.mark.parametrize("contents", ["[5]", "null", '{"pieces": 5}', '[["id"]]',
                                      '[{"id": []}]'])
def test_a_catalogue_file_of_the_wrong_shape_is_bad_input(tmp_path, contents):
    from duplotrain.catalog import load_catalog

    path = tmp_path / "odd.json"
    path.write_text(contents)
    with pytest.raises(ValueError):
        load_catalog(path)


def test_a_catalogue_file_names_each_piece_once(tmp_path):
    from duplotrain.catalog import load_catalog

    straight = {"paths": [{"segments": [{"type": "straight", "run": 64}]}]}
    path = tmp_path / "twice.json"
    path.write_text(json.dumps([{"id": "mine", **straight}, {"id": "mine", **straight}]))
    with pytest.raises(ValueError, match="appears twice"):
        load_catalog(path)
