"""Search regressions: eligibility before dedup, exact symmetries and honest limits."""

from dataclasses import replace

import pytest

from duplotrain import IncompleteSearchError, PerfectResult
from duplotrain.catalog import default_catalog
from duplotrain.explore import congruence_key, find_perfect_loops, find_perfect_networks
from duplotrain.geometry import ORIGIN
from duplotrain.layout import Placement, build_chain
from duplotrain.networks import NetworkConfig, _attach_orientations, enumerate_networks
from duplotrain.pieces import Straight, parse_piece
from duplotrain.solver import (
    SolverConfig,
    _mirror_traversals,
    _moves_for,
    _solution_overlaps,
    solve,
)


def test_adding_a_level_crossing_does_not_hide_a_perfect_shuttle():
    catalog = default_catalog()
    cfg = NetworkConfig(min_pieces=4, max_pieces=4, max_results=100, max_nodes=100_000)
    stones = {"stone_direction": 2}
    baseline = find_perfect_networks({"buffer": 2, "straight": 2}, catalog, stones, cfg)
    expanded = find_perfect_networks(
        {"buffer": 2, "straight": 2, "level_crossing": 1}, catalog, stones, cfg
    )
    assert len(baseline) == len(expanded) == 1
    assert baseline.stats.complete
    assert not expanded.stats.complete  # four-piece bound, five pieces available
    assert expanded.stats.stop_reason == "piece_limit"
    assert expanded[0][0].piece_counts == {"buffer": 2, "straight": 2}
    assert congruence_key(baseline[0][0]) == congruence_key(expanded[0][0])
    assert expanded[0][1].perfectly_looping


def test_acceptance_precedes_dedup_and_only_accepted_results_consume_cap():
    attempts = []

    def accept(layout):
        attempts.append(layout.piece_counts)
        return layout.piece_counts.get("straight") == 2

    result = enumerate_networks(
        {"buffer": 2, "straight": 2, "level_crossing": 1}, default_catalog(),
        NetworkConfig(min_pieces=4, max_pieces=4, max_results=1), accept=accept,
    )
    assert attempts[0].get("level_crossing") == 1
    assert len(result.layouts) == 1
    assert result.layouts[0].piece_counts.get("straight") == 2
    assert result.stats.stop_reason == "result_limit"


def hump_piece():
    return parse_piece({
        "id": "hump", "width": 64,
        "paths": [{"segments": [
            {"type": "arc", "radius": 128, "degrees": 90},
            {"type": "arc", "radius": 128, "degrees": -180},
            {"type": "arc", "radius": 128, "degrees": 90},
        ]}],
    })


@pytest.mark.parametrize("enumerator", [_moves_for, _attach_orientations])
def test_equal_ports_do_not_imply_equal_footprints(enumerator):
    piece = hump_piece()
    placements = [Placement(piece, piece.frame_for(e, ORIGIN)) for e in (0, 1)]
    assert (frozenset(placements[0].port_pose(p) for p in (0, 1))
            == frozenset(placements[1].port_pose(p) for p in (0, 1)))
    ys = [[y for line in p.centrelines() for _x, y, _z in line] for p in placements]
    assert max(ys[0]) > 200 and min(ys[1]) < -200
    assert len(enumerator(piece)) == 2


def test_hump_reflection_swaps_the_two_distinct_traversals():
    assert _mirror_traversals(hump_piece()) == {(0, 1): (1, 0), (1, 0): (0, 1)}


def test_known_straight_symmetry_still_collapses():
    piece = default_catalog()["straight"]
    assert len(_moves_for(piece)) == len(_attach_orientations(piece)) == 1
    assert _mirror_traversals(piece) == {(0, 1): (0, 1), (1, 0): (0, 1)}


def test_unknown_segment_geometry_is_not_assumed_symmetric():
    class CustomSegment(Straight):
        pass

    piece = default_catalog()["straight"]
    path = replace(piece.paths[0], segments=(CustomSegment(piece.paths[0].segments[0].run),))
    piece = replace(piece, paths=(path,))
    assert len(_moves_for(piece)) == len(_attach_orientations(piece)) == 2
    assert all(partner is None for partner in _mirror_traversals(piece).values())


@pytest.mark.parametrize("search", [solve, enumerate_networks])
@pytest.mark.parametrize("count", [0.5, -1, True, "2", float("nan"), None])
def test_both_searches_reject_invalid_counts(search, count):
    with pytest.raises(ValueError, match="non-negative integer"):
        search({"straight": count}, default_catalog())


@pytest.mark.parametrize("search", [solve, enumerate_networks])
def test_both_searches_reject_unknown_ids_even_with_zero_count(search):
    with pytest.raises(ValueError, match="unknown piece"):
        search({"not-a-piece": 0}, default_catalog())


@pytest.mark.parametrize("kwargs", [
    {"min_pieces": -1}, {"min_pieces": True}, {"max_pieces": 0},
    {"max_pieces": None}, {"max_pieces": 1.5}, {"max_pieces": True},
    {"max_results": 0}, {"max_results": True}, {"max_nodes": 0},
    {"max_nodes": 1.5}, {"clearance": -1}, {"clearance": float("inf")},
    {"collision_spacing": 0}, {"collision_spacing": -1},
    {"collision_spacing": float("nan")},
])
def test_network_configuration_validates_resource_and_sampling_bounds(kwargs):
    with pytest.raises(ValueError):
        NetworkConfig(**kwargs)


@pytest.mark.parametrize("inventory", [{}, {"straight": 0}, {"straight": 1}])
def test_network_exhaustion_is_reported_even_without_results(inventory):
    result = enumerate_networks(inventory, default_catalog())
    assert result.layouts == []
    assert result.stats.complete
    assert result.stats.stop_reason == "exhausted"


@pytest.mark.parametrize("limit,reason", [
    ({"max_nodes": 1}, "node_limit"),
    ({"max_results": 1}, "result_limit"),
    ({"max_pieces": 2}, "piece_limit"),
])
def test_network_limits_are_not_exhaustion(limit, reason):
    result = enumerate_networks(
        {"buffer": 2, "straight": 2}, default_catalog(), NetworkConfig(**limit)
    )
    assert not result.stats.complete
    assert result.stats.stop_reason == reason
    assert result.stats.aborted == (reason == "node_limit")
    assert result.stats.max_pieces_searched == min(4, limit.get("max_pieces", 18))


@pytest.mark.parametrize("family", ["loops", "networks"])
@pytest.mark.parametrize("limit,reason", [
    ({"max_nodes": 1}, "node_limit"),
    ({"max_results": 1}, "result_limit"),
    ({"max_pieces": 1}, "piece_limit"),
    ({}, "exhausted"),
])
def test_perfection_wrappers_retain_stats_and_can_require_exhaustion(family, limit, reason):
    catalog = default_catalog()
    if family == "loops":
        def search(**kwargs):
            return find_perfect_loops(
                {"curve": 12, "straight": 2}, catalog, SolverConfig(**limit), **kwargs
            )
    else:
        def search(**kwargs):
            return find_perfect_networks(
                {"buffer": 2, "straight": 2}, catalog, {"stone_direction": 2},
                NetworkConfig(**limit), **kwargs,
            )
    result = search()
    assert isinstance(result, PerfectResult)
    assert result.layouts is result
    assert list(result) == result  # existing list-style clients still work
    assert result.stats.stop_reason == reason
    if reason == "exhausted":
        assert result.stats.complete
        assert result.require_complete() is result
        assert search(require_complete=True).stats.complete
    else:
        assert not result.stats.complete
        with pytest.raises(IncompleteSearchError) as error:
            result.require_complete()
        assert error.value.result is result
        with pytest.raises(IncompleteSearchError, match=reason):
            search(require_complete=True)


def flyover_catalog(underpass):
    """Four custom tiles form a closed eight; only non-neighbours cross.

    The bridge deck is 60 mm high, below blanket clearance but above the
    underpass threshold. The two long connectors go around opposite corners.
    """
    def line(run):
        return {"type": "straight", "run": run}

    def arc(turn):
        return {"type": "arc", "radius": 64, "degrees": turn}

    def connector(rise, turn):
        return [
            {"type": "ramp", "run": 128, "rise": rise}, arc(turn),
            line(128), arc(turn), line(192), arc(turn), line(64),
        ]

    return {
        pid: parse_piece({"id": pid, "width": 8, "underpass": arch,
                          "paths": [{"segments": segments}]})
        for pid, segments, arch in [
            ("ground", [line(256)], False),
            ("climb", connector(60, -90), False),
            ("deck", [line(256)], underpass),
            ("descent", connector(-60, 90), False),
        ]
    }


@pytest.mark.parametrize("underpass", [False, True])
def test_network_and_solver_agree_on_bridge_crossing(underpass):
    catalog = flyover_catalog(underpass)
    layout = build_chain([(catalog[pid], 0, 1)
                          for pid in ("ground", "climb", "deck", "descent")])
    layout = layout.join((3, 1), (0, 0))
    assert layout.is_closed
    assert _solution_overlaps(layout, 0, 120.0, 8.0) is not underpass
    result = enumerate_networks(
        dict.fromkeys(catalog, 1), catalog,
        NetworkConfig(min_pieces=4, max_pieces=4, use_all_pieces=True, max_results=100),
    )
    assert result.stats.complete
    assert (congruence_key(layout) in {congruence_key(lay) for lay in result.layouts}) is underpass
