"""Network enumeration and the exhaustive hunt for perfectly looping networks."""

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.drive import classify
from duplotrain.explore import congruence_key, find_perfect_networks
from duplotrain.networks import NetworkConfig, enumerate_networks


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def test_circle_is_the_only_12_curve_network(catalog):
    result = enumerate_networks(
        {"curve": 12}, catalog, NetworkConfig(use_all_pieces=True, max_pieces=12)
    )
    assert len(result.layouts) == 1
    assert result.layouts[0].is_closed


def test_shuttle_is_the_only_buffered_bar(catalog):
    result = enumerate_networks(
        {"straight": 3, "buffer": 2},
        catalog,
        NetworkConfig(use_all_pieces=True, max_pieces=5),
    )
    assert len(result.layouts) == 1
    layout = result.layouts[0]
    assert layout.is_closed  # buffer faces are sealed, not loose
    assert layout.piece_counts == {"straight": 3, "buffer": 2}


def test_perfect_networks_shuttle(catalog):
    perfect = find_perfect_networks(
        {"straight": 3, "buffer": 2},
        catalog,
        {"stone_direction": 2},
        NetworkConfig(use_all_pieces=True, max_pieces=5),
    )
    assert len(perfect) == 1
    layout, verdict = perfect[0]
    assert verdict.perfectly_looping
    # Both buffer faces got their mandatory guard stones.
    assert len(layout.accessories) == 2


def test_star_of_three_arms_is_never_perfect(catalog):
    """The sticky-tongue theorem: dead-end caps REFLECT, so a train ping-pongs
    between two arms of a 3-armed star forever and the third arm is never visited.
    A reflecting cap preserves the tongue; only a lobe (branch-to-branch loop)
    alternates it."""
    result = enumerate_networks(
        {"switch": 1, "straight": 3, "buffer": 3},
        catalog,
        NetworkConfig(use_all_pieces=True, max_pieces=7),
    )
    stars = [
        layout
        for layout in result.layouts
        if layout.piece_counts.get("switch") == 1
        and layout.piece_counts.get("buffer") == 3
    ]
    assert stars, "the Y-star network must be buildable"

    perfect = find_perfect_networks(
        {"switch": 1, "straight": 3, "buffer": 3},
        catalog,
        {"stone_direction": 3},
        NetworkConfig(use_all_pieces=True, max_pieces=7),
    )
    assert perfect == []  # looping at best, never perfect

    # Pick the symmetric star (one straight per arm) so every guard stone has a
    # straight to clip onto, and check the ladder verdict directly.
    def symmetric(layout):
        return all(
            layout.placements[layout.links[(i, 0)][0]].piece.id == "straight"
            for i, p in enumerate(layout.placements)
            if p.piece.id == "buffer"
        )

    star = next(s for s in stars if symmetric(s))
    guarded = star
    for index, placement in enumerate(star.placements):
        if placement.piece.id != "buffer":
            continue
        neighbour, port = star.links[(index, 0)]
        guarded = guarded.with_accessory(neighbour, "stone_direction", at_port=port)
    verdict = classify(guarded)
    assert verdict.looping  # nobody derails or stalls...
    assert not verdict.completely_looping  # ...but the third arm is never visited


@pytest.mark.slow
def test_perfect_networks_finds_the_stoned_loop(catalog):
    """{12 curves + 2 straights}: network enumeration + stone placement rediscovers
    the perfect loop family (a closed ring with one direction stone on a straight)."""
    perfect = find_perfect_networks(
        {"curve": 12, "straight": 2},
        catalog,
        {"stone_direction": 1},
        NetworkConfig(use_all_pieces=True, max_pieces=14, max_nodes=1_500_000),
    )
    assert perfect
    keys = {congruence_key(layout) for layout, _v in perfect}
    assert len(keys) == len(perfect)
    for layout, verdict in perfect:
        assert verdict.perfectly_looping
        # Exactly the one direction stone, clipped mid-piece on a straight.
        assert [entry[1] for entry in layout.accessories] == ["stone_direction"]