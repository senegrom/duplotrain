"""Bound malformed catalogue input before float conversion or grid work."""
from fractions import Fraction

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.collision import CollisionField
from duplotrain.exact import Alg
from duplotrain.pieces import parse_length, parse_piece


def piece(**updates):
    return {"id": "custom", "paths": [{"segments": [{"type": "straight", "run": 128}]}],
            **updates}


@pytest.mark.parametrize("number", [10**400, -(10**400), Fraction(10**400, 3),
                                    Fraction(1, 10**400), Alg(10**400)])
def test_exact_catalogue_numbers_reject_excessive_representation(number):
    with pytest.raises(ValueError, match="catalogue number"):
        parse_length(number)


@pytest.mark.parametrize("where", ["run", "start", "alg", "chord"])
def test_huge_json_integer_fails_cleanly_before_geometry(where):
    number = 10**400
    path = {"segments": [{"type": "straight", "run": number if where == "run" else 128}]}
    if where == "start":
        path["start"] = {"x": number}
    if where == "alg":
        path["segments"][0]["run"] = {"alg": [0, number, 0, 0]}
    if where == "chord":
        path["segments"][0]["run"] = {"chord": {"radius": number, "degrees": 30}}
    with pytest.raises(ValueError, match="catalogue number"):
        parse_piece(piece(paths=[path]))


@pytest.mark.parametrize("value", [128, 152.5, "305/2", Fraction(305, 2), "1e-64"])
def test_normal_exact_numbers_remain_exact(value):
    expected = Fraction(str(value)) if isinstance(value, float) else Fraction(value)
    assert parse_length(value) == Alg(expected)


def test_old_maximal_decimal_representation_remains_accepted():
    text = "9" * 60 + "e64"
    assert parse_length(text) == Alg(Fraction(text))


@pytest.mark.parametrize("field", ["width", "end_overhang"])
@pytest.mark.parametrize("value", [10**400, 1e12, float("inf"), float("nan"), True])
def test_catalogue_dimensions_have_clean_errors(field, value):
    with pytest.raises(ValueError):
        parse_piece(piece(**{field: value}))


def test_dimension_limits_and_catalogue_are_usable():
    assert parse_piece(piece(width=10000, end_overhang=10000)).width == 10000
    assert all(p.width <= 10000 and p.end_overhang <= 10000 for p in default_catalog().values())


class GuardGrid(dict):
    """Turn an unbounded empty-neighbourhood scan into a prompt test failure."""
    lookups = 0

    def get(self, key, default=None):
        self.lookups += 1
        assert self.lookups <= 10000, "unbounded empty-cell enumeration"
        return super().get(key, default)


@pytest.mark.parametrize("width", [1e12, 1e308])
def test_sparse_collision_grid_bounds_work_for_extreme_programmatic_widths(width):
    field = CollisionField()
    field.add(0, [(0.0, 0.0, 0.0)], width)
    field._grid = GuardGrid(field._grid)
    assert not field.clashes([(0.0, 0.0, 200.0)], width, set())
    assert field.clashes([(0.0, 0.0, 0.0)], width, set())
    assert not field.clashes([(0.0, 0.0, 0.0)], width, {0})
    assert field._grid.lookups == 0


@pytest.mark.parametrize("height", [0, 41, 42, 43, 119, 120, 121])
@pytest.mark.parametrize("underpass", [False, True])
def test_sparse_bucket_fallback_preserves_clearance_and_underpass(height, underpass):
    import duplotrain.collision as collision

    field = CollisionField()
    field.add(0, [(0.0, 0.0, 0.0), (96.0, 0.0, 0.0)], 32)
    query = [(0.0, 0.0, float(height)), (-96.0, 0.0, float(height))]
    ordinary = field.clashes(query, 32, set(), underpass=underpass)
    old = collision._NARROW_MAX_RADIUS
    try:
        collision._NARROW_MAX_RADIUS = 0
        assert field.clashes(query, 32, set(), underpass=underpass) == ordinary
        assert not field.clashes(query, 32, {0}, underpass=underpass)
    finally:
        collision._NARROW_MAX_RADIUS = old


def test_sparse_fallback_matches_normal_path_after_backtracking(monkeypatch):
    import random

    import duplotrain.collision as collision

    rng = random.Random(143)
    field = CollisionField()
    for i in range(30):
        field.add(i, [(rng.uniform(-1000, 1000), rng.uniform(-1000, 1000), 0.0)],
                  rng.choice([16, 32, 80]))
    for pop in range(4):
        for _ in range(80):
            query = [(rng.uniform(-1200, 1200), rng.uniform(-1200, 1200),
                      rng.choice([0, 42, 57.6, 120]))]
            width = rng.choice([16, 32, 80, 1800])
            ignore = {rng.randrange(30)}
            monkeypatch.setattr(collision, "_NARROW_MAX_RADIUS", 1000)
            expected = field.clashes(query, width, ignore)
            monkeypatch.setattr(collision, "_NARROW_MAX_RADIUS", 0)
            assert field.clashes(query, width, ignore) == expected
        field.pop()
