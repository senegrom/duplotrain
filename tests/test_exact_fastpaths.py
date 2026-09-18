"""Algebraic shortcuts must agree coefficient-for-coefficient with the full formulas."""

import copy
import random
from dataclasses import FrozenInstanceError, asdict, replace
from fractions import Fraction

import pytest

from duplotrain import SolverConfig, build_chain, default_catalog, solve
from duplotrain.exact import Alg
from duplotrain.geometry import Pose, cos_sin
from duplotrain.layout import _port_pose, _rotated_local_pose
from tests.test_performance_contracts import full_product


def generic_add(x, y):
    y = Alg.coerce(y)
    return Alg(*(a + b for a, b in zip(x.coeffs(), y.coeffs(), strict=True)))


def generic_sub(x, y):
    y = Alg.coerce(y)
    return Alg(*(a - b for a, b in zip(x.coeffs(), y.coeffs(), strict=True)))


def generic_neg(x):
    return Alg(*(-a for a in x.coeffs()))


def generic_mul(x, y):
    return Alg(*full_product(x, Alg.coerce(y)))


def generic_rotation(x, y, steps):
    c, s = cos_sin(steps)
    return (generic_sub(generic_mul(c, x), generic_mul(s, y)),
            generic_add(generic_mul(s, x), generic_mul(c, y)))


@pytest.mark.parametrize("mask", range(16))
def test_sparse_and_dense_products_are_exact(mask):
    rng = random.Random(20260918 + mask)
    values = [Alg(), Alg(1), Alg(-1), Alg(Fraction(288, 5)),
              Alg(Fraction(10**60 + 1, 10**50 + 3), 0, Fraction(-37, 53))]
    values += [Alg(*(Fraction(rng.randint(-100, 100), rng.randint(1, 97))
                     if mask & (1 << i) else 0 for i in range(4))) for _ in range(20)]
    # Always exercise the Q(sqrt3) path against all coefficient masks, so one
    # nonzero sqrt2/sqrt6 coefficient on EITHER operand must retain the full product.
    values += [Alg(Fraction(rng.randint(-100, 100), 17), 0,
                   Fraction(rng.randint(-100, 100), 31)) for _ in range(10)]
    for x in values:
        for y in values:
            actual = x * y
            expected = Alg(*full_product(x, y))
            assert actual.coeffs() == expected.coeffs()
            assert hash(actual) == hash(expected)
            assert all(type(c) is Fraction for c in actual.coeffs())
            assert x + y == generic_add(x, y)
            assert x - y == generic_sub(x, y)
            assert -x == generic_neg(x)


@pytest.mark.parametrize("scalar", [0, 1, -1, Fraction(0), Fraction(1), Fraction(-1),
                                    0.0, -0.0, 1.0, -1.0])
def test_identity_fastpaths_keep_scalar_coercion_and_immutability(scalar):
    value = Alg(Fraction(3, 7), -2, Fraction(5, 11), 4)
    before = copy.deepcopy(value)
    for actual, expected in ((value + scalar, generic_add(value, scalar)),
                             (scalar + value, generic_add(value, scalar)),
                             (value - scalar, generic_sub(value, scalar)),
                             (scalar - value, generic_sub(Alg(scalar), value)),
                             (value * scalar, generic_mul(value, scalar)),
                             (scalar * value, generic_mul(value, scalar))):
        assert actual.coeffs() == expected.coeffs()
        assert hash(actual) == hash(expected)
        with pytest.raises(FrozenInstanceError):
            actual.a = Fraction(99)
        assert value == before
        assert replace(actual, a=17).a == 17
        assert actual == expected


@pytest.mark.parametrize("heading", range(24))
def test_every_heading_matches_full_rotation_and_composition(heading):
    values = [Alg(), Alg(Fraction(1, 19)), Alg(10**55, 0, Fraction(-13, 17)),
              Alg(Fraction(-7, 13), 2, Fraction(1, 37), -3)]
    for x in values:
        for y in values:
            pose = Pose(x, y, Alg(Fraction(288, 5)), heading)
            for turn in (-48, -7, 0, 6, 12, 18, 25, 72):
                rx, ry = generic_rotation(x, y, turn)
                expected = Pose(rx, ry, pose.z, heading + turn)
                assert pose.rotated_about_origin(turn) == expected
                assert hash(pose.rotated_about_origin(turn)) == hash(expected)
            dx, dy = y, -x
            rx, ry = generic_rotation(dx, dy, heading)
            actual = pose.then(dx, dy, Fraction(-96, 5), -29)
            expected = Pose(generic_add(x, rx), generic_add(y, ry), Alg(Fraction(192, 5)),
                            heading - 29)
            assert actual == expected
            assert hash(actual) == hash(expected)


@pytest.mark.parametrize("heading", [0, 6, 12, 18])
def test_quarter_turns_do_not_multiply_field_elements(heading, monkeypatch):
    def unexpected(*args):
        raise AssertionError("A quarter turn needs no field multiplication")

    pose = Pose.make(Alg(1, 2, 3, 4), Alg(-5, 6, -7, 8), 41, heading)
    expected_xy = generic_rotation(pose.x, pose.y, heading)
    monkeypatch.setattr(Alg, "__mul__", unexpected)
    assert pose.rotated_about_origin(heading).xy() == tuple(map(float, expected_xy))
    pose.then(Alg(1, 2, 3, 4), Alg(-5, 6, -7, 8), 0, 2)


@pytest.mark.parametrize("steps", [0.0, 6.0, 12.0, 18.0, 1.5, "6", None])
def test_rotation_still_rejects_non_integer_steps(steps):
    # The old table lookup rejected even whole floats; shortcut branches must
    # not accidentally accept them just because 6.0 == 6.
    with pytest.raises(TypeError):
        Pose.make().rotated_about_origin(steps)


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("slop", [0.0, 5.0])
@pytest.mark.parametrize("switch", [False, True])
def test_complete_search_results_and_counters_match_full_arithmetic(
    engine, slop, switch, monkeypatch
):
    import duplotrain.geometry as geometry

    catalog = default_catalog()
    start = Pose.make(x=317, y=-123, z=41, heading=5 if engine == "field" else 4)
    chain = ["switch"] if switch else ["curve"] * 8
    base = build_chain([(catalog[pid], 0, 1) for pid in chain], start=start)
    config = SolverConfig(min_pieces=0, max_results=10000, max_nodes=100000,
                          engine=engine, slop=slop, reversing_loops=switch)
    stock = {"curve": 12} if switch else {"curve": 4, "straight": 2}
    optimized = solve(stock, catalog, config, base=base)
    assert optimized.stats.complete and optimized.solutions
    monkeypatch.setattr(Alg, "__add__", generic_add)
    monkeypatch.setattr(Alg, "__radd__", generic_add)
    monkeypatch.setattr(Alg, "__sub__", generic_sub)
    monkeypatch.setattr(Alg, "__neg__", generic_neg)
    monkeypatch.setattr(Alg, "__mul__", generic_mul)
    monkeypatch.setattr(Alg, "__rmul__", generic_mul)
    monkeypatch.setattr(geometry, "_rotate_xy", generic_rotation)
    _port_pose.cache_clear()
    _rotated_local_pose.cache_clear()
    reference = solve(stock, catalog, config, base=base)
    assert reference.stats.complete
    assert optimized.solutions == reference.solutions
    a, b = asdict(optimized.stats), asdict(reference.stats)
    a.pop("duration_s")
    b.pop("duration_s")
    assert a == b
