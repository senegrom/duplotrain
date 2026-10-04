"""Ranking loops for a box of pieces: exactness, usage, variety, open stubs and bricks."""

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
    assert (with_stub.stubs, tidy.stubs) == (1, 0)
    assert with_stub.total == pytest.approx(tidy.total - 3.0)
    parts = {f.name: getattr(with_stub, f.name) for f in fields(with_stub)
             if f.name not in ("raised", "stubs")}
    assert with_stub.total == pytest.approx(sum(parts.values()) - 2 * parts["stub_penalty"])


def test_a_teardrop_tail_is_no_stub(catalog):
    # A teardrop's tail ends open by design, where its stone clips on.
    inventory = {"switch": 1, "curve": 12}
    result = solve(inventory, catalog,
                   SolverConfig(use_all_pieces=True, reversing_loops=True, max_results=100))
    assert result.solutions and all(s.kind == "reversing" and s.open_stubs == 1
                                    for s in result.solutions)
    for teardrop in result.solutions:
        score = score_solution(teardrop, inventory)
        assert score.stubs == 0 and score.stub_penalty == 0.0


def test_pieces_on_bricks_are_counted_apart_from_the_score(catalog):
    from duplotrain.layout import build_chain
    from duplotrain.solver import Solution

    ramp, span, straight, slope = (catalog[pid] for pid in ("ramp", "span", "straight", "slope"))

    def score(chain):
        layout = build_chain(chain)
        solution = Solution(layout, (), 0.0, True, len(layout.connectable_ends()), ())
        return score_solution(solution, {"ramp": 2, "span": 2, "straight": 1, "slope": 4})

    def raised(chain):
        return score(chain).raised

    # A bridge standing on the floor carries itself; a straight at the crest
    # stands on bricks, whichever way the chain was walked.
    assert raised([(ramp, 0, 1), (span, 0, 1)]) == 0
    assert raised([(ramp, 0, 1), (span, 0, 1), (straight, 0, 1)]) == 1
    assert raised([(straight, 0, 1), (ramp, 0, 1), (span, 0, 1)]) == 0
    assert raised([(span, 1, 0), (ramp, 1, 0), (straight, 0, 1)]) == 0
    # A ramp climbing on from a crest stands on bricks, and so does its arch.
    assert raised([(ramp, 0, 1), (span, 0, 1), (ramp, 0, 1), (span, 0, 1), (straight, 0, 1)]) == 3
    # Less than a brick up, track rests on its joints: four slight slopes lift
    # the straight after them past one brick.
    assert raised([(slope, 0, 1), (straight, 0, 1)]) == 0
    assert raised([(slope, 0, 1)] * 4 + [(straight, 0, 1)]) == 1
    # A bridge whose ramp rests on slight slopes carries itself too; past a brick,
    # the ramp stands on bricks and so does its arch.
    assert raised([(slope, 0, 1), (ramp, 0, 1), (span, 0, 1)]) == 0
    assert raised([(span, 1, 0), (ramp, 1, 0), (slope, 1, 0)]) == 0
    assert raised([(slope, 0, 1)] * 4 + [(ramp, 0, 1), (span, 0, 1)]) == 2
    # Stacks rank a loop lower whatever its score, and never enter the score.
    up = score([(ramp, 0, 1), (span, 0, 1), (straight, 0, 1)])
    flat = score([(ramp, 0, 1), (span, 0, 1)])
    assert up.rank > flat.rank and up.rank == (1, -up.total)
