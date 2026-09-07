"""Exact results, cache isolation and bounded retention, not fragile wall-clock limits."""

import copy
import math
import pickle
import random
from dataclasses import FrozenInstanceError, replace
from fractions import Fraction

import pytest

from duplotrain.catalog import _default_catalog_items, default_catalog
from duplotrain.collision import CollisionField
from duplotrain.exact import Alg, _exact_fraction
from duplotrain.geometry import ORIGIN, Pose
from duplotrain.gui import Session
from duplotrain.layout import (
    Layout,
    Placement,
    _heading_trig,
    _local_footprint_bounds,
    _port_pose,
    _rotated_local_pose,
)
from duplotrain.pieces import _sample_paths
from duplotrain.solver import (
    Solution,
    _cached_canonical_traversals,
    _cached_mirror_ports,
    _cached_mirror_traversals,
    _cached_moves,
    _max_span,
    _moves_for,
    _turn_capacity,
)


def full_product(x, y):
    a, b, c, d = x.coeffs()
    e, f, g, h = y.coeffs()
    return (a * e + 2 * b * f + 3 * c * g + 6 * d * h,
            a * f + b * e + 3 * c * h + 3 * d * g,
            a * g + c * e + 2 * b * h + 2 * d * f,
            a * h + d * e + b * g + c * f)


def test_fast_arithmetic_matches_full_field_product():
    rng = random.Random(20260906)
    values = [Alg(), Alg(1), Alg(-1), Alg(0, 1), Alg(0, 0, 1), Alg(0, 0, 0, 1)]
    values += [Alg(*(Fraction(rng.randint(-100, 100), rng.randint(1, 17))
                     for _ in range(4))) for _ in range(80)]
    values += [Alg(Fraction(rng.randint(-100, 100), rng.randint(1, 17))) for _ in range(30)]
    for x in values:
        for y in values:
            assert (x * y).coeffs() == full_product(x, y)
            expected = tuple(a - b for a, b in zip(x.coeffs(), y.coeffs(), strict=True))
            assert (x - y).coeffs() == expected
    # Scalar entry points, including reflected subtraction, keep exact coercion.
    x = Alg(1, 2, 3, 4)
    for scalar in (0, 1, -3, Fraction(7, 13), 152.4):
        y = Alg(scalar)
        assert (x * scalar).coeffs() == full_product(x, y)
        assert (scalar * x).coeffs() == full_product(y, x)
        assert scalar - x == y - x


def test_fraction_reuse_does_not_retain_subclass_behaviour():
    value = Fraction(7, 13)
    assert _exact_fraction(value) is value

    class CustomFraction(Fraction):
        pass

    assert type(_exact_fraction(CustomFraction(7, 13))) is Fraction
    assert Alg(152.4).a == Fraction(762, 5)


@pytest.mark.parametrize("pid", list(default_catalog()))
def test_cached_piece_data_is_exact_and_callers_own_containers(pid):
    piece = default_catalog()[pid]
    _cached_moves.cache_clear()
    first = _moves_for(piece)
    expected = copy.deepcopy(first)
    assert tuple(first) == _cached_moves.__wrapped__(piece)
    first.clear()
    assert _moves_for(piece) == expected
    assert _cached_moves.cache_info().hits >= 1

    for spacing in (8.0, 10.0, 17.0):
        expected_lines = [path.sample(spacing) for path in piece.paths]
        lines = piece.all_centrelines(spacing)
        assert lines == expected_lines
        lines[0].clear()
        lines.append([(123, 456, 789)])
        assert piece.all_centrelines(spacing) == expected_lines


@pytest.mark.parametrize("heading", range(24))
def test_port_cache_agrees_with_uncached_transform(heading):
    piece = default_catalog()["switch"]
    frame = Pose(Alg(2, -1, 3, 4), Alg(-8, 2), Alg(9), heading)
    placement = Placement(piece, frame)
    for port, local in enumerate(piece.ports):
        expected = frame.then(local.pose.x, local.pose.y, local.pose.z, local.pose.heading)
        assert placement.port_pose(port) == expected
        assert placement.port_pose(port) == expected


def test_caches_key_geometry_not_piece_id_or_current_layout():
    piece = default_catalog()["straight"]
    original = _moves_for(piece)
    original_lines = piece.all_centrelines()
    longer_path = replace(piece.paths[0], segments=(replace(piece.paths[0].segments[0],
                                                          run=Alg(1234)),))
    longer_port = replace(piece.ports[1], pose=Pose.make(x=1234))
    custom = replace(piece, paths=(longer_path,), ports=(piece.ports[0], longer_port))
    assert custom.id == piece.id
    assert _moves_for(custom) != original
    assert custom.all_centrelines() != original_lines
    assert Placement(custom, ORIGIN).port_pose(1) != Placement(piece, ORIGIN).port_pose(1)
    assert _moves_for(piece) == original
    assert piece.all_centrelines() == original_lines


def test_all_shared_caches_are_bounded():
    assert _cached_moves.cache_parameters()["maxsize"] == 128
    assert _sample_paths.cache_parameters()["maxsize"] == 128
    assert _port_pose.cache_parameters()["maxsize"] == 4096
    assert _rotated_local_pose.cache_parameters()["maxsize"] == 2048
    assert _heading_trig.cache_parameters()["maxsize"] == 24
    assert _local_footprint_bounds.cache_parameters()["maxsize"] == 2048
    assert _cached_canonical_traversals.cache_parameters()["maxsize"] == 128
    assert _cached_mirror_ports.cache_parameters()["maxsize"] == 128
    assert _cached_mirror_traversals.cache_parameters()["maxsize"] == 128
    assert _turn_capacity.cache_parameters()["maxsize"] == 128
    assert _max_span.cache_parameters()["maxsize"] == 128
    assert _default_catalog_items.cache_parameters()["maxsize"] == 1
    _port_pose.cache_clear()
    for i in range(4100):
        _port_pose(Pose.make(x=i), ORIGIN)
    assert _port_pose.cache_info().currsize == 4096
    piece = default_catalog()["straight"]
    _cached_moves.cache_clear()
    _sample_paths.cache_clear()
    for i in range(130):
        _moves_for(replace(piece, name=str(i)))
        piece.all_centrelines(8.0 + i)
    assert _cached_moves.cache_info().currsize == 128
    assert _sample_paths.cache_info().currsize == 128


def test_default_catalog_reuses_immutable_pieces_but_not_the_mapping():
    _default_catalog_items.cache_clear()
    first = default_catalog()
    second = default_catalog()
    assert first == second
    assert first is not second
    assert first["straight"] is second["straight"]
    first.pop("straight")
    assert "straight" in default_catalog()
    assert _default_catalog_items.cache_info().hits >= 2


def test_rotated_transform_caches_match_direct_geometry():
    piece = default_catalog()["switch"]
    _rotated_local_pose.cache_clear()
    _heading_trig.cache_clear()
    for heading in range(24):
        frame = Pose.make(x=Alg(5, 1), y=Alg(-7, 0, 1), z=3, heading=heading)
        placement = Placement(piece, frame)
        for port, local in enumerate(piece.ports):
            expected = frame.then(local.pose.x, local.pose.y, local.pose.z, local.pose.heading)
            assert placement.port_pose(port) == expected
        for spacing in (8.0, 10.0, 17.0):
            theta = math.radians(frame.degrees)
            c, s = math.cos(theta), math.sin(theta)
            ox, oy, oz = frame.xyz()
            expected_lines = [
                [(ox + c * x - s * y, oy + s * x + c * y, oz + z) for x, y, z in line]
                for line in piece.all_centrelines(spacing)
            ]
            assert placement.centrelines(spacing) == expected_lines


def test_collision_pop_restores_exact_previous_grid_and_width():
    field = CollisionField()
    first = [(0.0, 0.0, 0.0), (5.0, 5.0, 0.0), (10.0, 10.0, 0.0)]
    second = [(1.0, 1.0, 0.0), (6.0, 6.0, 0.0), (11.0, 11.0, 0.0)]
    field.add(0, first, 80.0)
    grid_before = {key: list(bucket) for key, bucket in field._grid.items()}
    field.add(1, second, 32.0)
    assert field._max_half_width == 80.0
    field.pop()
    assert field._max_half_width == 80.0
    assert field._grid == grid_before
    field.pop()
    assert field._max_half_width == 0.0
    assert field._grid == {}


def test_state_and_candidate_return_values_cannot_poison_later_responses(monkeypatch):
    session = Session()
    session.attach("curve", 0, None)
    session.candidates = [Solution(layout=session.layout, steps=(), gap=0,
                                   exact=False, open_stubs=2, signature=())]
    expected = session.state()
    returned = session.state()
    returned["palette"][0]["variants"].clear()
    returned["layout"]["placements"][0]["ports"][0]["x"] = 1e9
    returned["layout"]["placements"][0]["lines"][0].clear()
    returned["candidates"][0]["preview"]["placements"].clear()
    returned["candidates"][0]["size_cm"].clear()
    assert session.state() == expected

    calls = []
    original = Layout.size

    def measured_size(layout):
        calls.append(layout)
        return original(layout)

    monkeypatch.setattr(Layout, "size", measured_size)
    candidate = session._candidate_json(0, session.candidates[0])
    assert calls == [session.layout]  # the preview already computes the size
    candidate["size_cm"][0] = -1
    assert candidate["preview"]["size_cm"][0] != -1


def test_shared_exact_values_are_immutable_and_still_copyable():
    value = Alg(1, 2, 3, 4)
    for name in ("a", "b", "c", "d"):
        with pytest.raises(FrozenInstanceError):
            setattr(value, name, Fraction(999))
        with pytest.raises(FrozenInstanceError):
            delattr(value, name)
    assert copy.copy(value) == value
    assert copy.deepcopy(value) == value
    assert pickle.loads(pickle.dumps(value)) == value
    move = _moves_for(default_catalog()["straight"])[0]
    with pytest.raises(FrozenInstanceError):
        move.dx.a = Fraction(999)
    pose = Placement(default_catalog()["straight"], ORIGIN).port_pose(1)
    with pytest.raises(FrozenInstanceError):
        pose.x.a = Fraction(999)


def test_collision_groups_points_per_cell_and_reuses_query_neighbourhood():
    class CountingGrid(dict):
        gets = 0

        def get(self, key, default=None):
            self.gets += 1
            return super().get(key, default)

    field = CollisionField()
    field._grid = CountingGrid()
    stored = [(float(x), 0.0, 0.0) for x in range(0, 65, 4)]
    field.add(0, stored, 32.0)
    # All points fit one 96 mm cell, represented by one placement group rather
    # than repeating width/index/underpass metadata on every sample.
    assert len(field._grid[(0, 0)]) == 1
    assert field._grid[(0, 0)][0].points == stored

    # A same-cell query consults the 3x3 neighbourhood once, not once per point.
    # Keep it far enough in z that every scanned point is non-colliding.
    query = [(float(x), 0.0, 200.0) for x in range(0, 65, 4)]
    assert not field.clashes(query, 32.0, ignore=set())
    assert field._grid.gets == 9


def test_state_reuses_each_exact_port_transform_once(monkeypatch):
    piece = default_catalog()["straight"]
    layout = Layout()
    for x in (0, 300, 600):
        layout, _ = layout.with_piece(piece, Pose.make(x=x))
    session = Session()
    session.history = [layout]

    calls = []
    original = Placement.port_pose

    def measured_port_pose(placement, port):
        calls.append((placement, port))
        return original(placement, port)

    monkeypatch.setattr(Placement, "port_pose", measured_port_pose)
    state = session.state()
    assert len(calls) == 6  # two ports x three pieces; matable/layout JSON reuse them
    assert len(state["layout"]["placements"]) == 3


def test_cached_local_footprint_matches_direct_layout_bounds():
    _local_footprint_bounds.cache_clear()
    for piece in default_catalog().values():
        for heading in range(24):
            frame = Pose.make(x=123.25, y=-89.75, heading=heading)
            layout = Layout((Placement(piece, frame),))
            cached = layout.bounds()
            # Translation of the cached local envelope must preserve the public
            # footprint to far below any displayed or physical precision.
            bx0, by0, bx1, by1 = _local_footprint_bounds(
                piece.paths, piece.width, piece.end_overhang, heading
            )
            x0, y0 = frame.xy()
            assert cached == pytest.approx(
                (x0 + bx0, y0 + by0, x0 + bx1, y0 + by1), abs=1e-12
            )
    assert _local_footprint_bounds.cache_info().hits > 0
