"""Completions must respect the base layout: no candidate may overlap existing
tiles, and a gap whose only closure is physically blocked must report NO way."""

import math
from dataclasses import replace

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.collision import UNDERPASS_MIN
from duplotrain.geometry import ORIGIN, Pose
from duplotrain.gui import Session
from duplotrain.layout import Layout
from duplotrain.solver import SolverConfig, _solution_overlaps, solve
from tests.test_completion import crossing_completion


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def strict_overlap_pairs(layout, spacing=8.0):
    """Independent all-pairs audit: linked neighbours exempt, everything else must
    keep centreline clearance (same rules the engine's CollisionField enforces,
    including the arch-underpass exemption)."""
    clouds = []
    for placement in layout:
        pts = [p for line in placement.centrelines(spacing) for p in line]
        clouds.append((pts, placement.piece.width / 2.0, placement.piece.underpass))
    linked = {tuple(sorted((a[0], b[0]))) for a, b in layout.links.items()}
    bad = []
    for i in range(len(clouds)):
        pa, ha, ua = clouds[i]
        for j in range(i + 1, len(clouds)):
            if (i, j) in linked:
                continue
            pb, hb, ub = clouds[j]
            limit = ha + hb - 2.0
            for x, y, z in pa:
                hit = False
                for px, py, pz in pb:
                    if abs(z - pz) >= 120.0:
                        continue
                    if ua and z - pz >= UNDERPASS_MIN:
                        continue
                    if ub and pz - z >= UNDERPASS_MIN:
                        continue
                    if (x - px) ** 2 + (y - py) ** 2 < limit * limit:
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
    assert result.solutions == [] and result.stats.complete
    # Refused by the search as pieces reach the blocker, not by the audit of
    # closures already found through it.
    assert result.stats.pruned_collision and not result.stats.dropped_overlap


@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_future_joint_exemption_does_not_ignore_unrelated_obstacle(engine):
    catalog, base, grow, close, witness = crossing_completion()
    base, _ = base.with_piece(catalog["straight"], ORIGIN)
    blocked, _ = witness.with_piece(catalog["straight"], ORIGIN)
    assert _solution_overlaps(blocked, 0, 120, 8)
    result = solve(
        {"crossing": 1, "lower": 1}, catalog,
        SolverConfig(min_pieces=1, engine=engine, max_nodes=100_000),
        base=base, grow_from=grow, close_onto=close,
    )
    assert not result.solutions
    assert result.stats.complete and result.stats.pruned_collision


@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_sealed_crossing_branch_is_not_a_future_joint(engine, monkeypatch):
    # Placed at the gap, the crossing touches the closing end's piece where one
    # of its second route's ports would mate it. Open, that port is a future
    # joint and the search exempts the closing piece from collision with the
    # crossing; with both of those ports sealed nothing can ever mate there, so
    # nothing is exempt and the touching crossing is refused.
    from duplotrain.collision import CollisionField

    exempted = []
    near = CollisionField.near

    def recorded(field, bounds, half_width, ignore):
        exempted.append(set(ignore))
        return near(field, bounds, half_width, ignore)

    monkeypatch.setattr(CollisionField, "near", recorded)
    results = {}
    for sealed in (False, True):
        catalog, base, grow, close, _ = crossing_completion()
        if sealed:
            catalog["crossing"] = replace(catalog["crossing"], sealed=frozenset({2, 3}))
        exempted.clear()
        # Without the reachability lookahead the search reaches the crossing:
        # with it, a sealed crossing is pruned before any collision rule applies.
        result = solve(
            {"crossing": 1, "lower": 1}, catalog,
            SolverConfig(min_pieces=1, engine=engine, max_nodes=100_000,
                         completion_lookahead=0),
            base=base, grow_from=grow, close_onto=close,
        )
        results[sealed] = result, any(close[0] in ignore for ignore in exempted)
    (open_result, open_exempt), (sealed_result, sealed_exempt) = results[False], results[True]
    assert open_result.solutions and open_exempt
    assert not sealed_result.solutions and sealed_result.stats.complete
    assert not sealed_exempt and sealed_result.stats.pruned_collision


def test_gui_completions_never_overlap_the_base(monkeypatch):
    """A ring containing a switch with a dangling spur, closed via solve_gap:
    every candidate must pass an independent overlap audit against the base."""
    import duplotrain.editor as editor

    searches, search = [], editor.solve

    def recorded(*args, **kwargs):
        result = search(*args, **kwargs)
        searches.append(result.stats)
        return result

    monkeypatch.setattr(editor, "solve", recorded)
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
    # The solver found them, refusing overlapping pieces as it placed them: its
    # final audit of each closure had nothing left to drop.
    assert searches and all(s.pruned_collision and not s.dropped_overlap for s in searches)


def bridge_with_ground_track(catalog, cross_x):
    """The 4-piece bridge along +x from the origin, plus a floating ground-level
    straight crossing beneath it at ``cross_x``, heading 90 degrees."""
    layout = Layout()
    ramp, span, straight = catalog["ramp"], catalog["span"], catalog["straight"]
    layout, idx = layout.with_piece(ramp, ramp.frame_for(0, ORIGIN))
    cursor = (idx, 1)
    for piece, entry in ((span, 0), (span, 1), (ramp, 1)):
        layout, idx = layout.attach(piece, entry, cursor)
        cursor = (idx, 1 - entry)
    under = Pose.make(cross_x, -64, 0, 6)
    layout, _b = layout.with_piece(straight, straight.frame_for(0, under))
    return layout


def test_ground_track_passes_under_the_high_bridge(catalog):
    """The user's observations: a train fits beneath the mid-arch, beneath the
    spans generally, and grazing under the ramp's highest portion is fine."""
    from duplotrain.solver import _solution_overlaps

    for cross_x in (512.0, 384.0, 304.0):  # crest, span low half, ramp top
        layout = bridge_with_ground_track(catalog, cross_x=cross_x)
        assert strict_overlap_pairs(layout) == [], cross_x
        assert not _solution_overlaps(layout, 0, 120.0, 8.0), cross_x


def test_ground_track_never_passes_under_the_lower_ramp(catalog):
    from duplotrain.solver import _solution_overlaps

    for cross_x in (60.0, 160.0):  # ramp foot and mid-ramp stay solid
        layout = bridge_with_ground_track(catalog, cross_x=cross_x)
        assert strict_overlap_pairs(layout) != [], cross_x
        assert _solution_overlaps(layout, 0, 120.0, 8.0), cross_x


def test_shared_overlap_audit_matches_the_standalone_audit_and_restores_its_field():
    from duplotrain import Layout, build_chain, default_catalog, solve
    from duplotrain.solver import SolverConfig, _OverlapAudit, _solution_overlaps

    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["ramp"], 0, 1)])
    audit = _OverlapAudit(base, 120.0, 8.0)
    assert len(audit.field) == len(base)
    result = solve({"curve": 6, "straight": 4, "ramp": 1, "span": 2}, catalog,
                   SolverConfig(min_pieces=0, max_results=8), base=base)
    candidates = [s.layout for s in result.solutions]
    # Layouts that overlap: fold the closing track back through the base and
    # through a fresh piece laid on top of an earlier one.
    clash = build_chain([(catalog["curve"], 0, 1)] * 6)
    clash, index = clash.attach(catalog["straight"], 0, (5, 1))
    clash, _ = clash.attach(catalog["straight"], 1, (index, 1))
    onto_base = Layout(base.placements + (base.placements[2],), dict(base.links))
    candidates += [clash, onto_base, base, Layout()]
    verdicts = set()
    for layout in candidates:
        n_base = len(base) if layout.placements[:len(base)] == base.placements else 0
        expected = _solution_overlaps(layout, n_base, 120.0, 8.0)
        assert audit.overlaps(layout) is expected
        assert len(audit.field) == len(base) + len(audit.pushed)  # the field is the kept prefix
        verdicts.add(expected)
    assert verdicts == {True, False}
    # A layout over another base is audited standalone, and the loop-mode
    # auditor without a base behaves like the plain function.
    empty = _OverlapAudit(None, 120.0, 8.0)
    for layout in candidates:
        assert empty.overlaps(layout) is _solution_overlaps(layout, 0, 120.0, 8.0)
        assert len(empty.field) == len(empty.pushed)


def test_shared_overlap_audit_accepts_equal_copies_of_the_base_and_shorter_layouts():
    from duplotrain import Layout, build_chain, default_catalog
    from duplotrain.geometry import Pose
    from duplotrain.layout import Placement
    from duplotrain.solver import _OverlapAudit, _solution_overlaps

    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["ramp"], 0, 1)])
    audit = _OverlapAudit(base, 120.0, 8.0)
    # Equal frames in fresh objects: not the base's placements, but the same base.
    copies = tuple(Placement(p.piece, Pose.make(p.frame.x, p.frame.y, p.frame.z, p.frame.heading))
                   for p in base.placements)
    assert all(c is not p and c == p for c, p in zip(copies, base.placements, strict=True))
    extra = Placement(catalog["straight"], base.pose_of(base.connectable_ends()[-1]))
    onto_base = Layout(base.placements + (base.placements[2],), dict(base.links))
    # Whatever the prefix, the verdict is the standalone audit's over this base:
    # equal copies take the shared path, anything else falls back to it.
    for layout in (Layout(copies + (extra,), dict(base.links)), onto_base,
                   Layout(copies[:3], {}), Layout(), base):
        assert audit.overlaps(layout) is _solution_overlaps(layout, len(base), 120.0, 8.0)
        assert len(audit.field) == len(base) + len(audit.pushed)


def test_shared_overlap_audit_keeps_a_prefix_only_with_the_same_links():
    """Consecutive loop solutions share placements; transits and closings change
    which earlier placements a kept piece is linked to, so a kept prefix must
    carry the same link sets, and every verdict must equal the standalone audit's."""
    import random

    from duplotrain import Layout, SolverConfig, default_catalog, solve
    from duplotrain.layout import Placement
    from duplotrain.solver import _OverlapAudit, _solution_overlaps

    catalog = default_catalog()
    result = solve({"curve": 12, "straight": 4, "switch": 2}, catalog,
                   SolverConfig(max_results=60, reversing_loops=True, max_nodes=60_000))
    layouts = [s.layout for s in result.solutions]
    assert len(layouts) == 60
    # Overlapping variants: a piece laid twice, and the same track without its
    # links, whose neighbours then count as overlaps.
    for layout in layouts[:20]:
        doubled = layout.placements + (Placement(layout.placements[3].piece,
                                                 layout.placements[3].frame),)
        layouts.append(Layout(doubled, dict(layout.links), layout.accessories))
        layouts.append(Layout(layout.placements, {}, layout.accessories))
    rng = random.Random(11)
    orders = [layouts, layouts[::-1], rng.sample(layouts, len(layouts))]
    for order in orders:
        audit = _OverlapAudit(None, 120.0, 8.0)
        kept = 0
        for layout in order:
            before = list(audit.pushed)
            expected = _solution_overlaps(layout, 0, 120.0, 8.0)
            assert audit.overlaps(layout) is expected
            assert len(audit.field) == len(audit.pushed)
            # Every kept entry is the same object, checked under the same links.
            shared = sum(1 for a, b in zip(before, audit.pushed, strict=False) if a is b)
            kept += shared
            for index, (placement, links) in enumerate(audit.pushed):
                current = layout.placements[index]  # a kept entry is an earlier object
                assert placement is current or (placement.piece is current.piece
                                                and placement.frame is current.frame)
                assert links == {b[0] for a, b in layout.links.items() if a[0] == index}
        assert kept > 0
