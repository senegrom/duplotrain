"""Poses on the heading lattice."""

import math

import pytest

from duplotrain.exact import Alg
from duplotrain.geometry import (
    HEADING_STEPS,
    ORIGIN,
    Pose,
    cos_sin,
    degrees_to_steps,
    steps_to_degrees,
)


def test_cos_sin_table_matches_floats():
    for k in range(HEADING_STEPS):
        c, s = cos_sin(k)
        angle = math.radians(steps_to_degrees(k))
        assert float(c) == pytest.approx(math.cos(angle), abs=1e-12)
        assert float(s) == pytest.approx(math.sin(angle), abs=1e-12)


def test_degrees_to_steps_round_trip():
    for k in range(HEADING_STEPS):
        assert degrees_to_steps(steps_to_degrees(k)) == k
    assert degrees_to_steps(-30) == HEADING_STEPS - 2
    assert degrees_to_steps(360) == 0


def test_off_lattice_angle_rejected():
    with pytest.raises(ValueError):
        degrees_to_steps(22.5)


def test_then_composes_rotation_and_translation():
    # Walk east 100, turn left 90, walk (north) 50: land at (100, 50) facing north.
    pose = ORIGIN.then(100, 0, 0, degrees_to_steps(90)).then(50, 0, 0, 0)
    assert pose == Pose.make(100, 50, 0, degrees_to_steps(90))


def test_then_matches_float_composition():
    pose = ORIGIN
    x, y, theta = 0.0, 0.0, 0.0
    for dx, dy, turn_deg in [(128, 0, 30), (64, 10, -60), (30, -5, 90), (128, 0, 165)]:
        c, s = math.cos(theta), math.sin(theta)
        x, y = x + c * dx - s * dy, y + s * dx + c * dy
        theta += math.radians(turn_deg)
        pose = pose.then(dx, dy, 0, degrees_to_steps(turn_deg))
        assert pose.xy() == (pytest.approx(x), pytest.approx(y))
        assert pose.degrees == pytest.approx(math.degrees(theta) % 360)


def test_reversed_and_connects_to():
    a = Pose.make(10, 20, 0, degrees_to_steps(30))
    assert a.connects_to(a.reversed())
    assert not a.connects_to(a)
    # Same point, same heading: not a legal joint (both face the same way).
    assert not a.connects_to(Pose.make(10, 20, 0, degrees_to_steps(30)))
    # Different height: no joint even if planar position matches.
    lifted = Pose(a.x, a.y, Alg(50), a.heading + HEADING_STEPS // 2)
    assert not a.connects_to(lifted)


def test_mirror_and_rotation():
    p = Pose.make(3, 4, 0, degrees_to_steps(30))
    assert p.mirrored() == Pose.make(3, -4, 0, degrees_to_steps(-30))
    q = p.rotated_about_origin(degrees_to_steps(90))
    assert q == Pose.make(-4, 3, 0, degrees_to_steps(120))


def test_pose_is_hashable_and_exact():
    p1 = ORIGIN.then(128, 0, 0, 2).then(128, 0, 0, -2)
    p2 = ORIGIN.then(256, 0, 0, 0)
    assert p1 != p2  # the turn moved us off the straight line
    assert len({ORIGIN, Pose.make(0, 0, 0, 0)}) == 1
