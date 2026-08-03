"""The loop finder: correctness, completeness on small inventories, and dedup."""

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.geometry import ORIGIN
from duplotrain.scoring import score_solution
from duplotrain.solver import SolverConfig, solve


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def assert_loop_is_sound(solution, catalog):
    """Every reported loop must replay into a layout whose links all truly mate."""
    layout = solution.layout
    for a, b in layout.links.items():
        if a < b:
            pa, pb = layout.pose_of(a), layout.pose_of(b)
            if solution.exact:
                assert pa.connects_to(pb)
            else:
                assert (pa.heading - pb.heading) % 24 == 12
                assert pa.distance_to(pb) <= solution.gap + 1e-9


def test_twelve_curves_make_exactly_one_circle(catalog):
    result = solve({"curve": 12}, catalog)
    assert len(result.solutions) == 1
    sol = result.solutions[0]
    assert sol.exact
    assert sol.piece_count == 12
    assert sol.open_stubs == 0
    assert_loop_is_sound(sol, catalog)


def test_eleven_curves_make_nothing(catalog):
    result = solve({"curve": 11}, catalog)
    assert result.solutions == []
    # The turn and reach prunes should keep this cheap.
    assert result.stats.nodes < 100_000


def test_starter_oval_found_and_exact(catalog):
    result = solve(
        {"curve": 12, "straight": 4},
        catalog,
        SolverConfig(use_all_pieces=True, max_results=200),
    )
    assert result.solutions, "the starter-set oval must be found"
    for sol in result.solutions:
        assert sol.exact
        assert sol.piece_count == 16
        assert_loop_is_sound(sol, catalog)
    # The classic oval is among them: bounding envelope 832 x 576 mm.
    sizes = {
        tuple(sorted((round(w), round(h))))
        for w, h in (s.layout.size() for s in result.solutions)
    }
    assert (576, 832) in sizes


def test_no_false_closures_with_odd_straight(catalog):
    # One straight can never balance: its 128 mm must be cancelled by something.
    result = solve(
        {"curve": 12, "straight": 1},
        catalog,
        SolverConfig(use_all_pieces=True),
    )
    assert result.solutions == []


def test_switch_joins_the_circle_with_a_dangling_branch(catalog):
    result = solve({"curve": 11, "switch": 1}, catalog)
    assert result.solutions
    best = result.solutions[0]
    assert best.exact
    assert best.piece_count == 12
    assert best.open_stubs == 1  # the unused branch of the switch
    assert_loop_is_sound(best, catalog)


def test_slop_never_relabels_forced_fits_as_exact(catalog):
    # A simple closed loop must turn a net 360 degrees; ten curves cannot, so with or
    # without slop this inventory yields nothing -- and never a fake "exact" closure.
    for slop in (0.0, 6.0):
        result = solve(
            {"curve": 10, "straight": 2},
            catalog,
            SolverConfig(slop=slop, use_all_pieces=True),
        )
        assert result.solutions == []


def test_dedup_no_mirror_twins(catalog):
    # The all-left circle and the all-right circle are the same physical layout.
    result = solve({"curve": 12}, catalog, SolverConfig(max_results=10))
    assert len(result.solutions) == 1


def test_chiral_loops_dedup_mirror_twins(catalog):
    """A circle with a switch is chiral; its mirror image must not double-count.

    Regression for the reflection bug: reversal alone only collapses mirror twins of
    layouts that are themselves mirror-symmetric, so this returned 2 before the
    signature gained an explicit mirror normalisation.
    """
    result = solve({"curve": 11, "switch": 1}, catalog, SolverConfig(use_all_pieces=True))
    assert len(result.solutions) == 1


@pytest.mark.slow
def test_chiral_enumeration_counts(catalog):
    """12 curves + 6 straights: 18 distinct loops, 9 of them using every piece."""
    result = solve({"curve": 12, "straight": 6}, catalog, SolverConfig(max_results=100))
    assert len(result.solutions) == 18
    result = solve(
        {"curve": 12, "straight": 6},
        catalog,
        SolverConfig(use_all_pieces=True, max_results=100),
    )
    assert len(result.solutions) == 9


def test_level_crossings_never_link_in_series(catalog):
    """The 160 mm road plates overhang a 128 mm joint; two of them cannot mate."""
    result = solve(
        {"curve": 12, "level_crossing": 4},
        catalog,
        SolverConfig(use_all_pieces=True, max_results=50),
    )
    assert result.solutions
    for sol in result.solutions:
        for a, b in sol.layout.links.items():
            pa = sol.layout.placements[a[0]].piece.id
            pb = sol.layout.placements[b[0]].piece.id
            assert not (pa == pb == "level_crossing")


def test_slop_reports_engineered_gap(catalog):
    """A 130 mm 'stretched straight' opposite a 128 mm one leaves exactly 2 mm.

    No arrangement of those two plus 12 curves closes exactly (the straights' vector
    sum has magnitude >= 2 mm), so with slop every solution must be a forced fit
    reporting exactly that 2 mm gap -- never relabelled exact.
    """
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
    inventory = {"curve": 12, "straight": 1, "stretched": 1}

    exact_only = solve(inventory, pieces, SolverConfig(use_all_pieces=True))
    assert exact_only.solutions == []

    forced = solve(
        inventory, pieces, SolverConfig(use_all_pieces=True, slop=3.0, max_results=20)
    )
    assert forced.solutions
    for sol in forced.solutions:
        assert not sol.exact
        assert sol.gap == pytest.approx(2.0, abs=1e-9)
        assert sol.layout.is_closed


def test_starter_box_has_exactly_four_shapes(catalog):
    """Using all of 12 curves + 4 straights, exactly four layouts exist.

    The four straights must pair off into opposite headings; up to symmetry that is
    the oval (0+180 twice), two parallelograms (30 and 60 degrees between the pairs)
    and the rounded square (90 degrees).  Mirror twins must NOT be double-counted.
    """
    result = solve(
        {"curve": 12, "straight": 4},
        catalog,
        SolverConfig(use_all_pieces=True, max_results=1000),
    )
    assert len(result.solutions) == 4
    sizes = sorted(
        tuple(sorted((round(w), round(h))))
        for w, h in (s.layout.size() for s in result.solutions)
    )
    assert sizes == [(576, 832), (640, 815), (687, 768), (704, 704)]


def test_results_are_replayable_layouts(catalog):
    result = solve({"curve": 12, "straight": 4}, catalog, SolverConfig(max_results=5))
    for sol in result.solutions:
        assert sol.layout.is_closed or sol.open_stubs > 0
        # Walking the loop from the first piece returns in piece_count steps.
        steps = list(sol.layout.walk(start=(0, 0)))
        assert len(steps) == sol.piece_count


def test_inventory_validation(catalog):
    with pytest.raises(ValueError, match="unknown piece"):
        solve({"warp_gate": 1}, catalog)


def test_scoring_prefers_exact_and_fuller_layouts(catalog):
    inventory = {"curve": 12, "straight": 4}
    result = solve(inventory, catalog, SolverConfig(max_results=50))
    scored = [(score_solution(s, inventory).total, s) for s in result.solutions]
    assert all(t >= 0 for t, _ in scored)
    top_total, top = max(scored, key=lambda p: p[0])
    # The best layout should use most of the box.
    assert top.piece_count >= 12


def test_anchor_pose_is_origin(catalog):
    result = solve({"curve": 12}, catalog)
    layout = result.solutions[0].layout
    entry = layout.pose_of((0, layout.placements[0].piece.routes[0].port_a))
    assert entry.same_point(ORIGIN)
