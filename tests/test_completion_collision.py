"""Completions must respect the base layout: no candidate may overlap existing
tiles, and a gap whose only closure is physically blocked must report NO way."""

import math

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.geometry import ORIGIN, Pose
from duplotrain.gui import Session
from duplotrain.layout import Layout
from duplotrain.solver import SolverConfig, solve


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def strict_overlap_pairs(layout, spacing=8.0):
    """Independent all-pairs audit: linked neighbours exempt, everything else must
    keep centreline clearance (same rule the engine's CollisionField enforces)."""
    clouds = []
    for placement in layout:
        pts = [p for line in placement.centrelines(spacing) for p in line]
        clouds.append((pts, placement.piece.width / 2.0))
    linked = {tuple(sorted((a[0], b[0]))) for a, b in layout.links.items()}
    bad = []
    for i in range(len(clouds)):
        pa, ha = clouds[i]
        for j in range(i + 1, len(clouds)):
            if (i, j) in linked:
                continue
            pb, hb = clouds[j]
            limit = ha + hb - 2.0
            for x, y, z in pa:
                hit = False
                for px, py, pz in pb:
                    if (
                        abs(z - pz) < 120.0
                        and (x - px) ** 2 + (y - py) ** 2 < limit * limit
                    ):
                        bad.append((i, j, math.hypot(x - px, y - py)))
                        hit = True
                        break
                if hit:
                    break
    return bad


def blocked_circle(catalog):
    """11 curves of a circle, with a floating straight laid across the corridor
    where the 12th curve would go."""
    curve, straight = catalog["curve"], catalog["straight"]
    layout = Layout()
    layout, first = layout.with_piece(curve, curve.frame_for(0, ORIGIN))
    cursor = (first, 1)
    for _ in range(10):
        layout, idx = layout.attach(curve, 0, cursor)
        cursor = (idx, 1)
    blocker = Pose.make(-64, -64, 0, 6)  # heading 90 deg, crossing the gap arc
    layout, b = layout.with_piece(straight, straight.frame_for(0, blocker))
    assert strict_overlap_pairs(layout) == []  # the base itself is clean
    opens = [end for end in layout.connectable_ends() if end[0] != b]
    return layout, opens


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_blocked_gap_is_not_closed_through_existing_track(catalog, engine):
    layout, opens = blocked_circle(catalog)
    result = solve(
        {"curve": 12, "straight": 8},
        catalog,
        SolverConfig(min_pieces=1, max_pieces=26, max_nodes=30_000, engine=engine),
        base=layout,
        grow_from=opens[1],
        close_onto=opens[0],
    )
    assert result.solutions == []


def test_gui_completions_never_overlap_the_base():
    """A ring containing a switch with a dangling spur, closed via solve_gap:
    every candidate must pass an independent overlap audit against the base."""
    session = Session()
    session.attach("switch", 1, None)
    session.attach("straight", 0, (0, 2))  # spur on the spare branch
    cursor = (0, 0)
    for _ in range(8):
        session.attach("curve", 0, cursor)
        cursor = (len(session.layout) - 1, 1)
    base = session.layout
    pre = {(i, j) for i, j, _d in strict_overlap_pairs(base)}
    opens = base.connectable_ends()
    grow = next(end for end in opens if end[0] == len(base) - 1)
    close = next(end for end in opens if end[0] == 0)

    outcome = session.solve_gap(grow, close, slop=0.0, max_results=6)
    assert outcome["found"] > 0
    for solution in session.candidates:
        fresh = [
            hit
            for hit in strict_overlap_pairs(solution.layout)
            if (hit[0], hit[1]) not in pre
        ]
        assert fresh == [], f"candidate overlaps the base: {fresh}"
