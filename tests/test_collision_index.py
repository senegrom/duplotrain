"""The spatial broad phase must preserve every decision of a full bounds scan."""

import gc
import json
import math
import random
import weakref
from dataclasses import asdict, replace
from pathlib import Path

import pytest

from duplotrain import Pose, SolverConfig, build_chain, default_catalog, solve
from duplotrain.collision import CollisionField, _bound_cells, bounds_of
from duplotrain.layout import layout_from_dict


class LinearField(CollisionField):
    def _near_clouds(self, bounds, half_width):
        return self._clouds


def fill(field, n=160):
    for i in range(n):
        field.add(i, [(float(i * 512), 0.0, 0.0)], 32)
    return field


def compare(indexed, linear, points, half=32, ignore=None, underpass=False):
    ignore = set() if ignore is None else ignore
    bounds = bounds_of(points)
    left = indexed.near(bounds, half, ignore)
    right = linear.near(bounds, half, ignore)
    assert left == right
    assert indexed.clashes(points, half, ignore, underpass) == linear.clashes(
        points, half, ignore, underpass
    )
    # near() must bin EVERY eligible deferred cloud, not just the first match.
    assert [c.deferred is None for c in indexed._clouds] == [
        c.deferred is None for c in linear._clouds
    ]


def test_index_is_lazy_for_audits_and_small_fields():
    small = fill(CollisionField(), 8)
    assert small.near((0, 0, 0, 0, 0, 0), 32, set())
    assert small._bounds_grid is None
    large = fill(CollisionField())
    assert large.clashes([(0, 0, 0)], 32, set())
    assert large._bounds_grid is None
    assert large.near((0, 0, 0, 0, 0, 0), 32, set())
    assert large._bounds_grid


def test_local_query_ignores_hundreds_of_distant_bounds():
    field = fill(CollisionField(), 512)
    nearby = field._near_clouds((0, 10, 0, 0, 0, 0), 32)
    assert len(nearby) == 1
    assert nearby[0].placement == 0
    assert field.near((0, 10, 0, 0, 0, 0), 32, set())


@pytest.mark.parametrize("x", [-512.0, -256.0, -0.01, 0.0, 255.99, 256.0, 512.0])
@pytest.mark.parametrize("gap", [61.999, 62.0, 62.001])
def test_cell_boundaries_and_exact_touch_margin(x, gap):
    a, b = fill(CollisionField()), fill(LinearField())
    for field in (a, b):
        field.add(99, [(x, -512.0, 0.0)], 32)
    points = [(x + gap, -512.0, 0.0)]
    compare(a, b, points)
    assert a.clashes(points, 32, set()) == (gap < 62)


@pytest.mark.parametrize("height", [-120, -42, 0, 41.999, 42, 119.999, 120, 250])
@pytest.mark.parametrize("underpass", [False, True])
def test_index_preserves_height_clearance_and_underpasses(height, underpass):
    a, b = fill(CollisionField()), fill(LinearField())
    for field in (a, b):
        field.add(100, [(0.0, -512.0, height)], 80, underpass=underpass)
    for query_height in (0, 42, 120):
        compare(a, b, [(0.0, -512.0, query_height)], half=32)
        compare(a, b, [(0.0, -512.0, query_height)], half=32, underpass=True)
    # Clearance is configurable; the index cannot cache a previous height decision.
    a.clearance = b.clearance = 40
    compare(a, b, [(0.0, -512.0, 0.0)], half=32)


def test_same_placement_id_does_not_hide_a_second_cloud():
    a, b = fill(CollisionField()), fill(LinearField())
    for field in (a, b):
        field.add(99, [(10.0, -512.0, 0.0)], 32)
        field.add(99, [(220.0, -512.0, 0.0)], 32)
    compare(a, b, [(10.0, -512.0, 0.0)])
    assert a.clashes([(10.0, -512.0, 0.0)], 32, set())
    compare(a, b, [(10.0, -512.0, 0.0)], ignore={99})


def test_deferred_clouds_are_indexed_deduplicated_and_removed_on_pop():
    a, b = fill(CollisionField()), fill(LinearField())
    # Activate before appending; all samples are initially deferred.
    compare(a, b, [(0.0, 0.0, 0.0)])
    points = [(0.0, 0.0, 0.0), (600.0, 600.0, 0.0)]
    for field in (a, b):
        for i in range(3):
            offset = (-512.0, -512.0, float(i))
            field.add_deferred(100 + i, points, offset, 32, bounds_of(points, offset))
    nearby = a._near_clouds((-512, -512, -512, -512, 0, 0), 32)
    assert len([c for c in nearby if c.placement == 100]) == 1
    compare(a, b, [(-512.0, -512.0, 0.0)], ignore={101})
    assert a._clouds[-2].deferred is not None
    for field in (a, b):
        field.pop()  # binned
        field.pop()  # still deferred
    compare(a, b, [(-512.0, -512.0, 0.0)])
    for field in (a, b):
        field.pop()
    compare(a, b, [(-512.0, -512.0, 0.0)])
    assert not a.near((-512, -512, -512, -512, 0, 0), 32, set())


def test_oversized_boxes_and_queries_fall_back_without_unbounded_indexing():
    a, b = fill(CollisionField()), fill(LinearField())
    compare(a, b, [(0.0, 0.0, 0.0)])
    for field in (a, b):
        points = [(-1e9, -1e9, 0.0), (1e9, 1e9, 0.0)]
        field.add_deferred(100, points, (0, 0, 0), 32, bounds_of(points))
    assert len(a._wide_clouds) == 1
    compare(a, b, [(-1e9, -1e9, 0.0)])
    assert len(a._bounds_grid) == 160
    assert _bound_cells((-1e9, 1e9, -1e9, 1e9)) is None
    assert _bound_cells((-1e308, 1e308, -1e308, 1e308), 1e308) is None
    assert a._near_clouds((-1e9, 1e9, -1e9, 1e9, 0, 0), 32) is a._clouds
    for field in (a, b):
        field.pop()
    assert not a._wide_clouds
    # Insertion before lazy activation takes the same wide-cloud fallback.
    cold = fill(CollisionField())
    cold.add_deferred(100, points, (0, 0, 0), 32, bounds_of(points))
    cold.near((0, 0, 0, 0, 0, 0), 32, set())
    assert len(cold._wide_clouds) == 1


def test_wide_piece_radius_is_honoured_and_restored_after_pop():
    a, b = fill(CollisionField()), fill(LinearField())
    compare(a, b, [(0.0, 0.0, 0.0)])
    for field in (a, b):
        field.add(99, [(0.0, -512.0, 0.0)], 600)
    compare(a, b, [(500.0, -512.0, 0.0)])
    assert a.clashes([(500.0, -512.0, 0.0)], 32, set())
    for field in (a, b):
        field.pop()
    assert a._max_half_width == b._max_half_width == 32
    compare(a, b, [(500.0, -512.0, 0.0)])


@pytest.mark.parametrize("seed", range(5))
def test_randomized_push_pop_ignore_and_query_matches_linear_scan(seed):
    rng = random.Random(seed)
    a, b = fill(CollisionField()), fill(LinearField())
    for step in range(250):
        if len(a) > 160 and rng.random() < 0.3:
            a.pop()
            b.pop()
        else:
            points = [(0.0, 0.0, 0.0), (rng.uniform(-700, 700), rng.uniform(-700, 700),
                                       rng.choice([0.0, 57.6, 76.8, 120.0]))]
            offset = (rng.uniform(-1200, 1200), rng.uniform(-1200, 1200),
                      rng.choice([-10.0, 0.0, 42.0, 120.0]))
            half = rng.choice([16.0, 32.0, 80.0, 200.0])
            arch = rng.choice([False, True])
            for field in (a, b):
                field.add_deferred(1000 + step, points, offset, half,
                                   bounds_of(points, offset), underpass=arch)
        ignore = {cloud.placement for cloud in a._clouds if rng.random() < 0.08}
        query = [(rng.uniform(-1500, 1500), rng.uniform(-1500, 1500),
                  rng.choice([0.0, 42.0, 120.0, 200.0]))]
        compare(a, b, query, half=rng.choice([16, 32, 80]), ignore=ignore,
                underpass=rng.choice([False, True]))
    while len(a):
        a.pop()
    assert not a._grid and not a._bounds_grid and not a._wide_clouds


@pytest.mark.parametrize("engine", ["field", "lattice"])
@pytest.mark.parametrize("slop", [0.0, 3.0])
@pytest.mark.parametrize("reversing", [False, True])
def test_complete_search_results_and_counters_match_without_index(
    engine, slop, reversing, monkeypatch
):
    catalog = default_catalog()
    base = build_chain([(catalog["switch" if reversing else "curve"], 0, 1)]
                       * (1 if reversing else 8), start=Pose.make(317, -190, 43,
                                                                 4 if engine == "lattice" else 5))
    ends = (base.connectable_ends()[1], base.connectable_ends()[0])
    stock = {"curve": 12} if reversing else {"curve": 4, "straight": 2}
    # Extra scene geometry triggers the broad phase without altering the gap.
    for i in range(140):
        base, _ = base.with_piece(catalog["straight"], Pose.make(4000 + 256 * i))
    config = SolverConfig(min_pieces=0, max_results=10000, max_nodes=200000,
                          engine=engine, slop=slop, reversing_loops=reversing)
    opts = dict(base=base, grow_from=ends[0], close_onto=ends[1])
    indexed = solve(stock, catalog, config, **opts)
    monkeypatch.setattr(CollisionField, "_near_clouds", LinearField._near_clouds)
    linear = solve(stock, catalog, config, **opts)
    assert indexed.stats.complete and linear.stats.complete
    assert indexed.solutions and indexed.solutions == linear.solutions
    assert asdict(replace(indexed.stats, duration_s=0)) == asdict(
        replace(linear.stats, duration_s=0)
    )


def test_reported_bridge_search_is_unchanged(monkeypatch):
    from duplotrain.gui import Session

    catalog = default_catalog()
    base = layout_from_dict(json.loads((Path(__file__).parent
                                       / "fixtures/bridge-gap.json").read_text()), catalog)
    sessions = []
    outcomes = []
    for indexed in (True, False):
        if not indexed:
            monkeypatch.setattr(CollisionField, "_near_clouds", LinearField._near_clouds)
        session = Session(history=[base], unlimited=True)
        outcomes.append(session.solve_gap(None, None, 0, 8))
        sessions.append(session)
    assert outcomes[0] == outcomes[1]
    assert sessions[0].candidates == sessions[1].candidates
    assert len(sessions[0].candidates) == 8


def test_index_is_local_and_does_not_keep_fields_alive():
    a, b = fill(CollisionField()), fill(CollisionField())
    a.near((0, 0, 0, 0, 0, 0), 32, set())
    assert a._bounds_grid and b._bounds_grid is None
    reference = weakref.ref(a)
    del a
    gc.collect()
    assert reference() is None


def test_nonfinite_box_uses_safe_fallback():
    assert _bound_cells((-math.inf, math.inf, 0, 0)) is None
    assert _bound_cells((math.nan, 0, 0, 0)) is None


def test_query_padding_rounds_outwards_at_cell_boundaries():
    cells = _bound_cells((62.0, 194.0, 62.0, 194.0), padding=62.0)
    assert (-1, -1) in cells and (1, 1) in cells
