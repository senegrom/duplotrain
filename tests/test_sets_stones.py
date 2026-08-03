"""Set inventories, buffer stops, action stones, and reversing loops."""

import pytest

from duplotrain.catalog import ACCESSORIES, default_catalog
from duplotrain.layout import build_chain, layout_from_dict, layout_to_dict
from duplotrain.sets import SETS, inventory_for_sets
from duplotrain.solver import SolverConfig, solve


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


# -- sets ------------------------------------------------------------------------


def test_sets_combine():
    pieces, stones = inventory_for_sets(["10872", "10882"])
    assert pieces == {
        "straight": 9,
        "ramp": 2,
        "span": 2,
        "curve": 10,
        "switch": 2,
        "level_crossing": 1,
        "buffer": 2,
    }
    assert stones == {"stone_stop": 1}


def test_owning_a_set_twice(catalog):
    pieces, _ = inventory_for_sets(["10874", "10874"])
    assert pieces == {"curve": 24, "straight": 8}


def test_unknown_set_rejected():
    with pytest.raises(ValueError, match="unknown set"):
        inventory_for_sets(["9999"])


def test_all_set_pieces_exist_in_catalog(catalog):
    for train_set in SETS.values():
        for pid in train_set.pieces:
            assert pid in catalog, f"{train_set.code} references unknown piece {pid}"
        for sid in train_set.stones:
            assert sid in ACCESSORIES


# -- buffers ---------------------------------------------------------------------


def test_buffer_seals_its_far_end(catalog):
    buffer = catalog["buffer"]
    layout = build_chain([(catalog["straight"], 0, 1)])
    layout, idx = layout.attach(buffer, 0, layout.open_ends()[-1])
    sealed_end = (idx, 1)
    assert layout.is_sealed(sealed_end)
    assert sealed_end not in layout.connectable_ends()
    with pytest.raises(ValueError, match="sealed"):
        layout.attach(catalog["straight"], 0, sealed_end)
    # A straight capped by a buffer has one connectable end left.
    assert len(layout.connectable_ends()) == 1


def test_buffers_never_join_a_loop(catalog):
    result = solve(
        {"curve": 12, "buffer": 2},
        catalog,
        SolverConfig(use_all_pieces=True),
    )
    assert result.solutions == []  # a loop cannot pass through a dead face
    result = solve({"curve": 12, "buffer": 2}, catalog)
    assert result.solutions  # without use-all the circle simply leaves them in the box
    assert all("buffer" not in s.layout.piece_counts for s in result.solutions)


# -- action stones ---------------------------------------------------------------


def test_stones_serialise_with_the_layout(catalog):
    layout = build_chain([(catalog["straight"], 0, 1), (catalog["straight"], 0, 1)])
    layout = layout.with_accessory(0, "stone_direction").with_accessory(1, "stone_stop")
    assert layout.stones_on(0) == ["stone_direction"]
    rebuilt = layout_from_dict(layout_to_dict(layout), catalog)
    assert rebuilt == layout
    assert rebuilt.stones_on(1) == ["stone_stop"]
    removed = rebuilt.without_accessory(0, "stone_direction")
    assert removed.stones_on(0) == []
    with pytest.raises(ValueError, match="no 'stone_direction'"):
        removed.without_accessory(0, "stone_direction")


# -- reversing loops ---------------------------------------------------------------


def test_teardrop_needs_reversing_mode(catalog):
    inventory = {"switch": 1, "curve": 12}
    plain = solve(inventory, catalog, SolverConfig(use_all_pieces=True))
    assert plain.solutions == []


def test_teardrop_found_with_reversing(catalog):
    """switch + 12 curves closes branch-onto-branch: the endless one-stone layout."""
    result = solve(
        {"switch": 1, "curve": 12},
        catalog,
        SolverConfig(use_all_pieces=True, reversing_loops=True, max_results=100),
    )
    assert len(result.solutions) == 3  # three distinct teardrop shapes, mirrors folded
    for sol in result.solutions:
        assert sol.kind == "reversing"
        assert sol.exact
        assert sol.piece_count == 13
        # The tail connector (the switch's stem side) stays open for the stone.
        assert sol.open_stubs == 1
        # Every recorded link truly mates.
        for a, b in sol.layout.links.items():
            if a < b:
                assert sol.layout.pose_of(a).connects_to(sol.layout.pose_of(b))


def test_reversing_never_replaces_plain_loops(catalog):
    """When an ordinary loop exists it is still found and ranked first."""
    result = solve(
        {"curve": 12},
        catalog,
        SolverConfig(reversing_loops=True, max_results=10),
    )
    assert result.solutions
    assert result.solutions[0].kind == "loop"
    assert result.solutions[0].exact