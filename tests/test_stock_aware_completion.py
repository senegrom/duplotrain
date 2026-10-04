"""Scarce stock and unavailable base routes must not enlarge the tail search."""

import itertools
import math

import pytest

import duplotrain.solver as solver
from duplotrain import Layout, Pose, SolverConfig, build_chain, default_catalog


def unfiltered_moves(pieces, stock, base, grow_from, close_onto):
    """The previous relaxation: every base type was reusable, even when occupied."""
    return {pid: solver._moves_for(piece) for pid, piece in pieces.items()}


@pytest.mark.parametrize("slots", range(7))
@pytest.mark.parametrize("consumed", [None, "long", "short"])
def test_stock_span_bound_matches_exhaustive_selection(slots, consumed):
    counts = {"long": 1, "short": 3, "empty": 0}
    spans = [(1024.0, "long"), (128.0, "short"), (64.0, "empty")]
    lengths = [span for span, pid in spans
               for _ in range(counts[pid] - (pid == consumed))]
    expected = max(sum(combo) for n in range(min(slots, len(lengths)) + 1)
                   for combo in itertools.combinations(lengths, n))
    assert solver._stock_span_budget(counts, spans, slots, consumed) == expected
    assert counts == {"long": 1, "short": 3, "empty": 0}


def test_scarce_bridge_is_not_reusable_after_it_is_spent():
    spans = [(1024.0, "bridge"), (128.0, "straight")]
    counts = {"bridge": 1, "straight": 999}
    assert solver._stock_span_budget(counts, spans, 3) == 1280
    assert solver._stock_span_budget(counts, spans, 3, "bridge") == 384
    counts["bridge"] = 0
    assert solver._stock_span_budget(counts, spans, 3) == 384


def test_the_stock_filter_offers_only_ends_the_completion_can_meet():
    # A completion meets the base only at its own two ends and at the open ports of
    # junctions it may pass through. A span, which rests only on a ramp's top, finds
    # no partner in the top of a remote bridge ramp.
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 8)
    base, ramp = base.with_piece(catalog["ramp"], Pose.make(x=10000))
    base, switch = base.with_piece(catalog["switch"], Pose.make(x=-10000))
    grow, close = (7, 1), (0, 0)
    ends = solver._walk_ends(base, grow, close)
    assert (ramp, 1) in base.connectable_ends()
    assert sorted(ends) == [close, grow, (switch, 0), (switch, 1), (switch, 2)]
    stock = {"curve": 4, "span": 2}
    assert solver._placeable_stock(stock, catalog, base) == stock  # every open end
    assert solver._placeable_stock(stock, catalog, base, ends) == {"curve": 4}
    # Left out, the spans neither widen the search nor keep it from using every piece.
    options = dict(base=base, grow_from=grow, close_onto=close)
    config = SolverConfig(min_pieces=0, max_results=100)
    plain = solver.solve({"curve": 4}, catalog, config, **options)
    extra = solver.solve(stock, catalog, config, **options)
    assert extra.solutions == plain.solutions and extra.stats.nodes == plain.stats.nodes
    everything = solver.solve(stock, catalog, SolverConfig(min_pieces=0, use_all_pieces=True),
                              **options)
    assert [s.piece_count for s in everything.solutions] == [len(base) + 4]


def test_base_only_nonjunctions_are_not_fictitious_spare_moves():
    catalog = default_catalog()
    base = build_chain([(catalog["ramp"], 0, 1), (catalog["span"], 0, 1)])
    moves = solver._completion_moves(catalog, {"curve": 4}, base, (0, 0), (1, 1))
    assert moves["curve"] == solver._moves_for(catalog["curve"])
    assert not any(routes for pid, routes in moves.items() if pid != "curve")


def test_base_crossing_keeps_canonical_free_route_but_not_reserved_endpoints():
    catalog = default_catalog()
    base, crossing = Layout().with_piece(catalog["crossing"], Pose.make())
    base, left = base.attach(catalog["straight"], 0, (crossing, 0))
    base, right = base.attach(catalog["straight"], 0, (crossing, 1))
    moves = solver._completion_moves(catalog, {}, base, (left, 1), (right, 1))
    canon = solver._canonical_traversals(catalog["crossing"])
    expected = {canon[2, 3], canon[3, 2]}
    assert {(m.entry, m.exit) for m in moves["crossing"]} == expected
    # Selected ends are final targets, never available for an intermediate transit.
    moves = solver._completion_moves(catalog, {}, base, (crossing, 2), (crossing, 3))
    assert not moves["crossing"]


def test_free_ports_on_different_switches_cannot_form_a_transit():
    catalog = default_catalog()
    base = Layout()
    outer = []
    for index, branch in enumerate((1, 2)):
        base, switch = base.with_piece(catalog["switch"], Pose.make(x=index * 2000))
        for port in (0, branch):
            base, end = base.attach(catalog["straight"], 0, (switch, port))
            outer.append((end, 1))
    moves = solver._completion_moves(catalog, {}, base, outer[0], outer[-1])
    assert not moves["switch"]
    # A spare switch, unlike occupied ones, really can be used in any orientation.
    moves = solver._completion_moves(catalog, {"switch": 1}, base, outer[0], outer[-1])
    assert moves["switch"] == solver._moves_for(catalog["switch"])


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("slop", [0.0, 5.0])
@pytest.mark.parametrize("shape", ["circle", "bridge", "switch"])
def test_stronger_prunes_preserve_complete_results(engine, slop, shape, monkeypatch):
    catalog = default_catalog()
    if shape == "switch":
        base = build_chain([(catalog["switch"], 0, 1)])
        grow, close = (0, 1), (0, 0)
        stock = {"curve": 12}
    else:
        base = build_chain([(catalog["curve"], 0, 1)] * 8,
                           start=Pose.make(x=317, y=-123, z=41,
                                           heading=4 if engine == "lattice" else 5))
        grow, close = (7, 1), (0, 0)
        stock = {"curve": 4, "straight": 2}
        if shape == "bridge":
            # A preplaced, remote bridge is an obstacle, not climbable spare stock.
            base, _ = base.with_piece(catalog["ramp"], Pose.make(x=10000))
            stock["ramp"] = 2
    config = SolverConfig(min_pieces=0, max_results=10000, max_nodes=200000,
                          engine=engine, slop=slop, reversing_loops=shape == "switch")
    options = dict(base=base, grow_from=grow, close_onto=close)
    improved = solver.solve(stock, catalog, config, **options)
    monkeypatch.setattr(solver, "_stock_span_budget", lambda *a, **kw: math.inf)
    monkeypatch.setattr(solver, "_completion_moves", unfiltered_moves)
    reference = solver.solve(stock, catalog, config, **options)
    assert improved.stats.complete and reference.stats.complete
    assert improved.solutions and improved.solutions == reference.solutions
    for candidate in improved.solutions:
        assert candidate.layout.placements[:len(base)] == base.placements
        assert not solver._solution_overlaps(candidate.layout, len(base), 120, 8)
