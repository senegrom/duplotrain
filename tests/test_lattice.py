"""The integer lattice engine: ring arithmetic, conversion, and conformance.

The conformance tests are the load-bearing ones: identical solutions from the field
and lattice engines on every solver mode, so the fast path can never silently change
an answer.
"""

import math

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.exact import Alg
from duplotrain.geometry import ORIGIN, Pose, degrees_to_steps
from duplotrain.lattice import (
    SCALE,
    LatticePoint,
    LatticePose,
    ROT_COS_SIN,
    from_alg_xy,
    z_from_alg,
)
from duplotrain.layout import build_chain
from duplotrain.solver import SolverConfig, _pose_to_lattice, solve


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


# -- ring arithmetic ---------------------------------------------------------------


def test_rotation_matches_floats():
    p = LatticePoint(7 * SCALE, 3, -5, 2)
    x0, y0 = p.xy()
    for steps in range(12):
        c, s = ROT_COS_SIN[steps]
        rx, ry = p.rotated(steps).xy()
        assert rx == pytest.approx(c * x0 - s * y0, abs=1e-9)
        assert ry == pytest.approx(s * x0 + c * y0, abs=1e-9)


def test_twelve_rotations_are_identity():
    p = LatticePoint(123, -45, 6, 789)
    assert p.rotated(12).key() == p.key()
    assert p.rotated(5).rotated(7).key() == p.key()


def test_conversion_round_trips_catalogue_geometry(catalog):
    """Every port of every built-in piece fits the lattice and converts faithfully."""
    for piece in catalog.values():
        for port in piece.ports:
            pose = port.pose
            lat = _pose_to_lattice(pose)
            assert lat is not None, f"{piece.id} port off-lattice"
            x, y = lat.p.xy()
            px, py = pose.xy()
            assert x == pytest.approx(px, abs=1e-9)
            assert y == pytest.approx(py, abs=1e-9)
            assert lat.z / SCALE == pytest.approx(float(pose.z), abs=1e-9)
            assert lat.heading * 2 == pose.heading


def test_off_lattice_values_are_rejected():
    assert from_alg_xy(Alg(0, 1, 0, 0), Alg(0)) is None  # sqrt2: 45-degree land
    assert from_alg_xy(Alg(1) / 3, Alg(0)) is None  # not a twentieth
    assert z_from_alg(Alg(0, 0, 1, 0)) is None  # irrational elevation
    assert _pose_to_lattice(Pose.make(0, 0, 0, degrees_to_steps(15))) is None


def test_lattice_pose_composition_matches_field(catalog):
    """Random-ish walks agree between Pose.then and LatticePose.then exactly."""
    curve = catalog["curve"]
    straight = catalog["straight"]
    field_pose = ORIGIN
    lat_pose = _pose_to_lattice(ORIGIN)
    walk = [curve.exit_delta(0, 1), straight.exit_delta(0, 1), curve.exit_delta(1, 0)] * 4
    for dx, dy, dz, dh in walk:
        field_pose = field_pose.then(dx, dy, dz, dh)
        delta = from_alg_xy(dx, dy)
        lat_pose = lat_pose.then(delta, z_from_alg(dz), dh // 2)
        assert _pose_to_lattice(field_pose).key() == lat_pose.key()
    fx, fy = field_pose.xy()
    lx, ly = lat_pose.p.xy()
    assert (lx, ly) == (pytest.approx(fx, abs=1e-9), pytest.approx(fy, abs=1e-9))


# -- engine conformance ------------------------------------------------------------


def _run_both(catalog, inventory, config_kwargs, **solve_kwargs):
    results = {}
    for engine in ("field", "lattice"):
        cfg = SolverConfig(engine=engine, **config_kwargs)
        results[engine] = solve(inventory, catalog, cfg, **solve_kwargs)
    field, lattice = results["field"], results["lattice"]
    assert field.stats.engine == "field"
    assert lattice.stats.engine == "lattice"
    assert len(field.solutions) == len(lattice.solutions)
    assert sorted(s.signature for s in field.solutions) == sorted(
        s.signature for s in lattice.solutions
    )
    for f, l in zip(
        sorted(field.solutions, key=lambda s: s.signature),
        sorted(lattice.solutions, key=lambda s: s.signature),
    ):
        assert f.exact == l.exact
        assert f.gap == pytest.approx(l.gap, abs=1e-9)
        assert f.kind == l.kind
        assert f.layout.piece_counts == l.layout.piece_counts
    return results


def test_conformance_loops(catalog):
    _run_both(
        catalog,
        {"curve": 12, "straight": 4},
        {"use_all_pieces": True, "max_results": 100},
    )


def test_conformance_switch_stub(catalog):
    _run_both(
        catalog,
        {"curve": 11, "switch": 1},
        {"use_all_pieces": True, "max_results": 20},
    )


def test_conformance_reversing_teardrop(catalog):
    _run_both(
        catalog,
        {"switch": 1, "curve": 12},
        {
            "use_all_pieces": True,
            "reversing_loops": True,
            "max_results": 100,
            "max_nodes": 600_000,
        },
    )


def test_conformance_completion(catalog):
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    _run_both(
        catalog,
        {"curve": 6, "straight": 4},
        {"min_pieces": 1, "max_results": 100},
        base=base,
    )


def test_conformance_forced_fits(catalog):
    from duplotrain.catalog import DEFAULT_CATALOG_SPECS
    from duplotrain.pieces import parse_pieces

    specs = list(DEFAULT_CATALOG_SPECS) + [
        {
            "id": "stretched",
            "name": "Stretched straight (test)",
            "category": "track",
            "width": 64,
            "paths": [{"segments": [{"type": "straight", "run": 130}]}],
        }
    ]
    pieces = parse_pieces(specs)
    _run_both(
        pieces,
        {"curve": 12, "straight": 1, "stretched": 1},
        {"use_all_pieces": True, "slop": 3.0, "max_results": 20},
    )


def test_auto_engine_picks_lattice_for_builtins(catalog):
    result = solve({"curve": 12}, catalog, SolverConfig(max_results=5))
    assert result.stats.engine == "lattice"


def test_auto_engine_falls_back_for_off_lattice_pieces(catalog):
    from duplotrain.catalog import DEFAULT_CATALOG_SPECS
    from duplotrain.pieces import parse_pieces

    specs = list(DEFAULT_CATALOG_SPECS) + [
        {
            "id": "odd45",
            "name": "45-degree curve (off-lattice)",
            "category": "track",
            "width": 64,
            "paths": [{"segments": [{"type": "arc", "radius": 256, "degrees": 45}]}],
        }
    ]
    pieces = parse_pieces(specs)
    result = solve({"curve": 12, "odd45": 1}, pieces, SolverConfig(max_results=5))
    assert result.stats.engine == "field"
    assert result.solutions  # the plain circle is still found

    with pytest.raises(ValueError, match="lattice"):
        solve({"odd45": 1, "curve": 12}, pieces, SolverConfig(engine="lattice"))