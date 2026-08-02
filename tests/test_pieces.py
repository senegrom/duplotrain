"""Piece parsing and the derived ports, routes and deltas."""

from fractions import Fraction

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.exact import Alg
from duplotrain.geometry import ORIGIN, degrees_to_steps
from duplotrain.pieces import parse_length, parse_piece

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
    dx, dy, dz, dheading = crossing.exit_delta(0, 1)
    assert (dx, dy, dheading) == (Alg(192), Alg(0), 0)


def test_ramp_rises(catalog):
    ramp = catalog["ramp"]
    dx, dy, dz, dheading = ramp.exit_delta(0, 1)
    assert (float(dx), float(dz)) == (320.0, pytest.approx(76.8))
    # Entered downhill, it descends.
    dx2, _dy2, dz2, _ = ramp.exit_delta(1, 0)
    assert float(dz2) == pytest.approx(-76.8)


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
