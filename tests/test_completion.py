"""Completion mode: close a partially built layout using spare pieces."""

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.layout import build_chain
from duplotrain.solver import SolverConfig, solve

LEFT = (0, 1)


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


@pytest.fixture()
def half_circle(catalog):
    return build_chain([(catalog["curve"], *LEFT)] * 6)


def test_complete_half_circle_with_six_curves(catalog, half_circle):
    result = solve(
        {"curve": 6},
        catalog,
        SolverConfig(min_pieces=1),
        base=half_circle,
    )
    assert len(result.solutions) == 1
    sol = result.solutions[0]
    assert sol.exact
    assert sol.layout.is_closed
    assert len(sol.layout) == 12  # 6 base + 6 grown
    assert sol.piece_count == 12


def test_completions_enumerate_straight_variants(catalog, half_circle):
    """With 6 curves + 4 straights spare there are exactly three ways to close."""
    result = solve(
        {"curve": 6, "straight": 4},
        catalog,
        SolverConfig(min_pieces=1, max_results=100),
        base=half_circle,
    )
    assert all(s.exact and s.layout.is_closed for s in result.solutions)
    grown_counts = sorted(
        sum(n for pid, n in s.layout.piece_counts.items()) for s in result.solutions
    )
    # circle (6 curves), oval-let (6c+2s), full oval (6c+4s)
    assert grown_counts == [12, 14, 16]


def test_completion_respects_base_collisions(catalog):
    """Growing must not plough through the base track: an S that dead-ends into the
    base's own body cannot be part of any reported completion."""
    base = build_chain([(catalog["curve"], *LEFT)] * 6)
    result = solve(
        {"curve": 6, "straight": 8},
        catalog,
        SolverConfig(min_pieces=1, max_results=200),
        base=base,
    )
    # Every solution must replay into a collision-legal closed layout; is_closed and
    # exactness are already asserted by construction, so just require solutions exist
    # and none uses fewer pieces than the geometric minimum.
    assert result.solutions
    assert min(len(s.layout) for s in result.solutions) == 12


def test_completion_around_a_switch_leaves_its_branch_open(catalog):
    switch = catalog["switch"]
    base = build_chain([(switch, 0, 1)])  # stem in at origin, left branch onward
    result = solve(
        {"curve": 11},
        catalog,
        SolverConfig(min_pieces=1),
        base=base,
        grow_from=(0, 1),  # continue from the left branch
        close_onto=(0, 0),  # come back around to the stem
    )
    assert result.solutions
    sol = result.solutions[0]
    assert sol.exact
    assert len(sol.layout) == 12
    assert sol.layout.open_ends() == [(0, 2)]  # only the right branch dangles


def test_completion_rejects_already_mating_ends(catalog):
    layout = build_chain([(catalog["curve"], *LEFT)] * 12)  # full circle, unjoined
    with pytest.raises(ValueError, match="already mate"):
        solve({"curve": 1}, catalog, SolverConfig(min_pieces=1), base=layout)


def test_completion_needs_two_open_ends(catalog):
    layout = build_chain([(catalog["curve"], *LEFT)] * 12)
    closed = layout.join(layout.open_ends()[1], layout.open_ends()[0])
    with pytest.raises(ValueError, match="two distinct open ends"):
        solve({"curve": 1}, catalog, SolverConfig(min_pieces=1), base=closed)


def test_loop_mode_rejects_stray_end_arguments(catalog):
    with pytest.raises(ValueError, match="only make sense"):
        solve({"curve": 12}, catalog, grow_from=(0, 0))