"""Ranking loops for a box of pieces: exactness, usage, variety and open stubs."""

from dataclasses import fields, replace

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.scoring import score_solution
from duplotrain.solver import SolverConfig, solve
from tests.test_solver import stretched_catalog


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def test_scoring_prefers_exact_and_fuller_layouts(catalog):
    inventory = {"curve": 12, "straight": 4}
    result = solve(inventory, catalog, SolverConfig(max_results=50))
    scored = [(score_solution(s, inventory).total, s) for s in result.solutions]
    assert all(t >= 0 for t, _ in scored)
    top_total, top = max(scored, key=lambda p: p[0])
    # The best layout uses the most of the box any loop uses.
    assert top.exact and top.piece_count == max(s.piece_count for s in result.solutions)


def test_scoring_ranks_a_forced_fit_below_the_same_loop_closed_exactly(catalog):
    # The same oval, once with a stretched straight forcing a 2 mm gap and once
    # exact: equal usage and variety, so the gap decides.
    forced_box = {"curve": 12, "straight": 1, "stretched": 1}
    exact_box = {"curve": 12, "straight": 2}
    forced = solve(forced_box, stretched_catalog(),
                   SolverConfig(use_all_pieces=True, slop=3.0)).solutions[0]
    exact = solve(exact_box, catalog, SolverConfig(use_all_pieces=True)).solutions[0]
    assert not forced.exact and forced.gap == pytest.approx(2.0) and exact.exact
    f, e = score_solution(forced, forced_box), score_solution(exact, exact_box)
    assert e.exactness == 40.0
    assert f.exactness == pytest.approx(40.0 - 8.0 * 2.0)  # 8 points per mm of gap
    assert (f.usage, f.variety) == (e.usage, e.variety)
    assert e.total - f.total == pytest.approx(16.0, abs=0.5)


def test_scoring_subtracts_a_penalty_for_each_open_stub(catalog):
    # Eleven curves and a switch close with the switch's other branch dangling.
    inventory = {"curve": 11, "switch": 1}
    stubbed = solve(inventory, catalog, SolverConfig(use_all_pieces=True)).solutions[0]
    assert stubbed.open_stubs == 1
    with_stub = score_solution(stubbed, inventory)
    tidy = score_solution(replace(stubbed, open_stubs=0), inventory)
    assert with_stub.stub_penalty == 3.0 and tidy.stub_penalty == 0.0
    assert with_stub.total == pytest.approx(tidy.total - 3.0)
    parts = {f.name: getattr(with_stub, f.name) for f in fields(with_stub)}
    assert with_stub.total == pytest.approx(
        sum(parts.values()) - 2 * (parts["stub_penalty"] + parts["stack_penalty"]))


def test_each_piece_raised_on_bricks_costs_a_stack(catalog):
    from duplotrain.layout import build_chain
    from duplotrain.scoring import ScoreWeights
    from duplotrain.solver import Solution

    ramp, span, straight = catalog["ramp"], catalog["span"], catalog["straight"]

    def penalty(chain):
        layout = build_chain(chain)
        solution = Solution(layout, (), 0.0, True, len(layout.connectable_ends()), ())
        return score_solution(solution, {"ramp": 1, "span": 1, "straight": 1}).stack_penalty

    # Bridge parts carry themselves; a straight at the crest stands on bricks.
    assert penalty([(ramp, 0, 1), (span, 0, 1)]) == 0
    assert penalty([(ramp, 0, 1), (span, 0, 1), (straight, 0, 1)]) == ScoreWeights().stack_penalty
    assert penalty([(straight, 0, 1), (ramp, 0, 1), (span, 0, 1)]) == 0
