"""The loop finder: correctness, completeness on small inventories, and dedup."""

import pytest

import duplotrain.solver as solver_module
from duplotrain.catalog import default_catalog
from duplotrain.geometry import ORIGIN
from duplotrain.layout import build_chain
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
    # The all-left and all-right circles are one physical layout.
    result = solve({"curve": 12}, catalog, SolverConfig(max_results=10))
    assert result.stats.complete and result.stats.stop_reason == "exhausted"
    assert len(result.solutions) == 1
    sol = result.solutions[0]
    assert sol.exact
    assert sol.piece_count == 12
    assert sol.open_stubs == 0
    assert_loop_is_sound(sol, catalog)


def test_eleven_curves_make_nothing(catalog):
    result = solve({"curve": 11}, catalog)
    assert result.solutions == [] and result.stats.complete
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
    assert result.solutions == [] and result.stats.complete


def test_switch_joins_the_circle_with_a_dangling_branch(catalog):
    result = solve({"curve": 11, "switch": 1}, catalog)
    assert result.solutions
    best = result.solutions[0]
    assert best.exact
    assert best.piece_count == 12
    assert best.open_stubs == 1  # the unused branch of the switch
    assert_loop_is_sound(best, catalog)


def test_slop_never_closes_a_loop_that_cannot_turn_full_circle(catalog):
    # A simple closed loop must turn a net 360 degrees; ten curves cannot, so with or
    # without slop this inventory yields nothing. (test_slop_reports_engineered_gap
    # checks that genuine forced fits are never labelled exact.)
    for slop in (0.0, 6.0):
        result = solve(
            {"curve": 10, "straight": 2},
            catalog,
            SolverConfig(slop=slop, use_all_pieces=True),
        )
        assert result.solutions == [] and result.stats.complete


def test_chiral_loops_dedup_mirror_twins(catalog):
    """A circle with a switch is chiral; its mirror image must not double-count.

    Regression for the reflection bug: reversal alone only collapses mirror twins of
    layouts that are themselves mirror-symmetric, so this returned 2 before the
    signature gained an explicit mirror normalisation.
    """
    result = solve({"curve": 11, "switch": 1}, catalog, SolverConfig(use_all_pieces=True))
    assert result.stats.complete and result.stats.stop_reason == "exhausted"
    assert len(result.solutions) == 1


def test_chiral_enumeration_counts(catalog):
    """12 curves + 6 straights: 18 distinct loops, 9 of them using every piece."""
    result = solve({"curve": 12, "straight": 6}, catalog, SolverConfig(max_results=100))
    assert result.stats.complete and len(result.solutions) == 18
    result = solve(
        {"curve": 12, "straight": 6},
        catalog,
        SolverConfig(use_all_pieces=True, max_results=100),
    )
    assert result.stats.complete and len(result.solutions) == 9


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
    # Exactly four: the enumeration ran to exhaustion, not into a limit.
    assert result.stats.complete and result.stats.stop_reason == "exhausted"
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


@pytest.mark.parametrize("ends", [((5, 1), (-6, 0)), ((-1, 1), (0, 0)), ((5, -1), (0, 0)),
                                  ((9, 0), (0, 0)), ((5, 7), (0, 0)), ([5, 1], (0, 0)),
                                  ((5, True), (0, 0))])
def test_completion_ends_must_name_real_ports(catalog, ends):
    # A negative alias of a real port passed every lookup, then matched nothing.
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    with pytest.raises(ValueError, match="not a port"):
        solve({"curve": 6}, catalog, SolverConfig(min_pieces=1), base=base,
              grow_from=ends[0], close_onto=ends[1])


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_rejected_candidates_do_not_exhaust_the_result_limit(catalog, engine):
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    seen = []

    def accept(candidate):
        seen.append(candidate.piece_count)
        return candidate.piece_count == 16  # six base curves + six curves/four straights

    result = solve({"curve": 6, "straight": 4}, catalog, SolverConfig(
        min_pieces=0, max_results=1, engine=engine, solution_filter=accept), base=base)
    assert result.solutions and len(result.solutions[0].layout) == 16
    assert result.stats.dropped_filter > 0
    assert 12 in seen and 16 in seen
    assert result.solutions[0].layout.is_closed
    assert not solver_module._solution_overlaps(result.solutions[0].layout, 0, 120, 8)


def test_filter_validation_and_exceptions_are_not_silenced(catalog):
    with pytest.raises(ValueError, match="solution_filter"):
        SolverConfig(solution_filter=42)
    base = build_chain([(catalog["curve"], 0, 1)] * 6)

    def fail(candidate):
        raise RuntimeError("audit failed")

    with pytest.raises(RuntimeError, match="audit failed"):
        solve({"curve": 6, "straight": 4}, catalog, SolverConfig(solution_filter=fail),
              base=base)


def test_base_junction_types_need_not_be_in_the_catalogue(catalog):
    base = build_chain([(catalog["switch"], 0, 1)])
    subset = {pid: catalog[pid] for pid in ("curve", "straight")}
    cfg = SolverConfig(min_pieces=1, max_results=1000, reversing_loops=True)
    options = dict(base=base, grow_from=(0, 1), close_onto=(0, 0))
    full = solve({"curve": 12, "straight": 4}, catalog, cfg, **options)
    assert full.solutions and full.stats.complete
    assert solve({"curve": 12, "straight": 4}, subset, cfg, **options).solutions == full.solutions


def test_the_search_depth_cap_is_reported_not_a_crash(catalog, monkeypatch):
    # Thousands of straights once recursed past Python's limit.
    result = solve({"curve": 12, "straight": 2000}, catalog, SolverConfig(max_nodes=20_000))
    assert result.solutions and result.stats.stop_reason == "node_limit"
    monkeypatch.setattr(solver_module, "_MAX_SEARCH_DEPTH", 12)
    capped = solve({"curve": 12, "straight": 2}, catalog)
    assert [s.piece_count for s in capped.solutions] == [12]
    assert capped.stats.stop_reason == "piece_limit" and not capped.stats.complete


def test_node_and_result_caps_report_incomplete():
    catalog = default_catalog()
    stopped = solve({"curve": 12}, catalog, SolverConfig(max_nodes=1))
    assert stopped.stats.aborted
    assert not stopped.stats.complete
    assert stopped.stats.stop_reason == "node_limit"
    capped = solve({"curve": 12}, catalog, SolverConfig(max_results=1))
    assert capped.solutions
    assert not capped.stats.complete
    assert capped.stats.stop_reason == "result_limit"
    exhausted = solve({"straight": 1}, catalog)
    assert exhausted.stats.complete
    assert exhausted.stats.stop_reason == "exhausted"


@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_contour_zero_does_not_emit_an_empty_fresh_loop(engine):
    result = solve({}, default_catalog(), SolverConfig(min_pieces=0, engine=engine))
    assert not result.solutions and result.stats.complete


def test_scoring_prefers_exact_and_fuller_layouts(catalog):
    inventory = {"curve": 12, "straight": 4}
    result = solve(inventory, catalog, SolverConfig(max_results=50))
    scored = [(score_solution(s, inventory).total, s) for s in result.solutions]
    assert all(t >= 0 for t, _ in scored)
    top_total, top = max(scored, key=lambda p: p[0])
    # The best layout uses the most of the box any loop uses.
    assert top.exact and top.piece_count == max(s.piece_count for s in result.solutions)


def stretched_catalog():
    """The default pieces plus a 130 mm straight that closes 2 mm short."""
    from duplotrain.catalog import DEFAULT_CATALOG_SPECS
    from duplotrain.pieces import parse_pieces

    return parse_pieces(list(DEFAULT_CATALOG_SPECS) + [{
        "id": "stretched", "name": "Stretched straight (test)", "category": "track",
        "width": 64, "paths": [{"segments": [{"type": "straight", "run": 130}]}],
    }])


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
    from dataclasses import fields, replace

    inventory = {"curve": 11, "switch": 1}
    stubbed = solve(inventory, catalog, SolverConfig(use_all_pieces=True)).solutions[0]
    assert stubbed.open_stubs == 1
    with_stub = score_solution(stubbed, inventory)
    tidy = score_solution(replace(stubbed, open_stubs=0), inventory)
    assert with_stub.stub_penalty == 3.0 and tidy.stub_penalty == 0.0
    assert with_stub.total == pytest.approx(tidy.total - 3.0)
    parts = {f.name: getattr(with_stub, f.name) for f in fields(with_stub)}
    assert with_stub.total == pytest.approx(
        sum(parts.values()) - 2 * parts["stub_penalty"])


def test_anchor_pose_is_origin(catalog):
    result = solve({"curve": 12}, catalog)
    layout = result.solutions[0].layout
    entry = layout.pose_of((0, layout.placements[0].piece.routes[0].port_a))
    assert entry.same_point(ORIGIN)


def test_canonical_signature_equals_the_exhaustive_rotation_minimum(catalog):
    import random

    from duplotrain.solver import (
        _canonical_signature,
        _canonical_traversals,
        _mirror_traversals,
        _Place,
        _Transit,
    )

    pieces = {pid: catalog[pid] for pid in ("straight", "curve", "switch", "crossing")}
    canon_for = {pid: _canonical_traversals(p) for pid, p in pieces.items()}
    mirror_for = {pid: _mirror_traversals(p) for pid, p in pieces.items()}

    def exhaustive(steps):
        # The definition: normalise every rotation of the walk, its reversal,
        # its mirror and the reversed mirror, and take the smallest.
        place_pids = [s.piece_id for s in steps if isinstance(s, _Place)]
        visits, ordinal = [], 0
        for s in steps:
            if isinstance(s, _Place):
                visits.append((ordinal, s.piece_id, s.entry, s.exit))
                ordinal += 1
            else:
                visits.append((s.placement, place_pids[s.placement], s.entry, s.exit))

        def normalise(seq):
            fresh, out = {}, []
            for inst, pid, entry, exit_ in seq:
                fresh.setdefault(inst, len(fresh))
                entry, exit_ = canon_for[pid].get((entry, exit_), (entry, exit_))
                out.append((fresh[inst], pid, entry, exit_))
            return tuple(out)

        def reverse(seq):
            return [(inst, pid, x, e) for (inst, pid, e, x) in reversed(seq)]

        sequences = [visits, reverse(visits)]
        mirrored = []
        for inst, pid, entry, exit_ in visits:
            partner = mirror_for[pid].get((entry, exit_))
            if partner is None:
                mirrored = None
                break
            mirrored.append((inst, pid, *partner))
        if mirrored is not None:
            sequences += [mirrored, reverse(mirrored)]
        n = len(visits)
        return min(normalise(seq[start:] + seq[:start]) for seq in sequences for start in range(n))

    rng = random.Random(2024)
    for _ in range(300):
        steps, junctions = [], []
        for index in range(rng.randint(1, 9)):
            pid = rng.choice(list(pieces))
            piece = pieces[pid]
            entry = rng.choice([p for p in range(len(piece.ports)) if piece.transit(p)])
            exit_port = rng.choice([e for e, _route in piece.transit(entry)])
            steps.append(_Place(pid, entry, exit_port))
            if piece.is_junction:
                junctions.append((index, piece, entry, exit_port))
            if junctions and rng.random() < 0.3:
                j, jpiece, jentry, jexit = rng.choice(junctions)
                spare = [p for p in range(len(jpiece.ports)) if p not in (jentry, jexit)]
                port = rng.choice(spare)
                exits = [e for e, _route in jpiece.transit(port) if e not in (jentry, jexit)]
                if exits:
                    steps.append(_Transit(j, port, rng.choice(exits)))
        assert _canonical_signature(steps, canon_for, mirror_for=mirror_for) == exhaustive(steps)


def test_solution_layouts_equal_their_replayed_constructions(catalog):
    from duplotrain import ORIGIN, Layout, build_chain
    from duplotrain.solver import _Place, _replay, _Transit

    # Two crossings in a row: a completion that transits both without a piece,
    # and ones that add pieces around them.
    crossings, a = Layout().with_piece(catalog["crossing"], ORIGIN)
    crossings, b = crossings.attach(catalog["crossing"], 0, (a, 1))
    crossings, left = crossings.attach(catalog["straight"], 1, (a, 0))
    crossings, right = crossings.attach(catalog["straight"], 0, (b, 1))
    crossings = Layout(crossings.placements, {})
    searches = [
        ({"curve": 12, "straight": 4}, SolverConfig(max_results=20), {}),
        ({"curve": 12, "switch": 1}, SolverConfig(max_results=20, reversing_loops=True), {}),
        ({}, SolverConfig(min_pieces=0),
         dict(base=crossings, grow_from=(left, 1), close_onto=(right, 0))),
        ({"curve": 12, "straight": 6}, SolverConfig(min_pieces=0, max_results=20),
         dict(base=crossings, grow_from=(left, 1), close_onto=(right, 0))),
        ({"curve": 12, "straight": 2}, SolverConfig(max_results=20, slop=3.0), {}),
        ({"curve": 6, "straight": 4},
         SolverConfig(min_pieces=0, max_results=20),
         dict(base=build_chain([(catalog["curve"], 0, 1)] * 6))),
        ({"curve": 12, "straight": 4, "switch": 1},
         SolverConfig(min_pieces=0, max_results=20, reversing_loops=True),
         dict(base=build_chain([(catalog["switch"], 0, 1)]), grow_from=(0, 1), close_onto=(0, 0))),
    ]
    checked = transits = 0
    for inventory, config, options in searches:
        result = solve(inventory, catalog, config, **options)
        assert result.solutions
        for solution in result.solutions:
            base = options.get("base")
            grow_from, close_onto = options.get("grow_from"), options.get("close_onto")
            if base is not None and grow_from is None:
                opens = base.connectable_ends()
                grow_from, close_onto = opens[-1], opens[0]
            final_target = None
            if solution.kind == "reversing":
                # The walk's last end mates the stub it closed into.
                n_base = len(base) if base is not None else 0
                cursor, index = None, n_base
                for step in solution.steps:
                    if isinstance(step, _Place):
                        cursor, index = (index, step.exit), index + 1
                    else:
                        cursor = (step.placement, step.exit)
                final_target = solution.layout.links[cursor]
            replayed = _replay(solution.steps, catalog, force_final_join=solution.gap > 0,
                               base=base, grow_from=grow_from, close_onto=close_onto,
                               final_target=final_target)
            assert isinstance(solution.layout, Layout) and replayed == solution.layout
            checked += 1
            transits += any(isinstance(step, _Transit) for step in solution.steps)
    assert checked >= 30 and transits >= 1


def test_a_reversing_lobe_driven_either_way_round_is_one_result():
    # The same teardrop, entered at the stem, can go round its lobe either way.
    from duplotrain.explore import congruence_key

    catalog = default_catalog()
    result = solve({"curve": 12, "switch": 1, "straight": 2}, catalog,
                   SolverConfig(reversing_loops=True, max_results=100))
    keys = [congruence_key(s.layout) for s in result.solutions if s.kind == "reversing"]
    assert len(keys) == len(set(keys)) == 40
    base = build_chain([(catalog["straight"], 0, 1)])
    completed = solve({"curve": 12, "switch": 1, "straight": 1}, catalog,
                      SolverConfig(reversing_loops=True, max_results=100),
                      base=base, grow_from=(0, 1), close_onto=(0, 0))
    placed = [frozenset((p.piece.id, frozenset(map(p.port_pose, range(len(p.piece.ports)))))
                        for p in s.layout.placements[1:]) for s in completed.solutions]
    assert len(placed) == len(set(placed)) == 68


def test_mirror_twins_closing_into_a_crossing_are_one_result():
    # The mirror twin of a loop closing into a crossing's diagonal port enters by
    # the crossing's other route, where that port lands on a straight one. An unused
    # single-handed piece turns the one-handed search off, so both twins are built.
    from duplotrain.catalog import DEFAULT_CATALOG_SPECS
    from duplotrain.explore import congruence_key
    from duplotrain.pieces import parse_pieces

    catalog = parse_pieces(list(DEFAULT_CATALOG_SPECS) + [
        {"id": "arc300", "width": 64, "paths": [{"segments": [
            {"type": "arc", "radius": {"alg": [0, 0, 64, 0]}, "degrees": -300}]}]},
        {"id": "hook", "width": 64, "paths": [{"segments": [
            {"type": "arc", "radius": 256, "degrees": 30}, {"type": "straight", "run": 64}]}]},
    ])
    for stock in ({"straight": 1, "crossing": 1, "arc300": 1},
                  {"straight": 1, "crossing": 1, "arc300": 1, "hook": 1}):
        result = solve(stock, catalog, SolverConfig(reversing_loops=True, min_pieces=2))
        assert result.stats.complete
        keys = [congruence_key(s.layout) for s in result.solutions
                if s.kind == "reversing" and "hook" not in s.layout.piece_counts]
        assert len(keys) == len(set(keys)) == 2


def test_a_slop_search_far_from_the_origin_runs_on_the_field_engine():
    from duplotrain.geometry import Pose

    catalog = default_catalog()
    half = [(catalog["straight"], 0, 1)] * 2 + [(catalog["curve"], 0, 1)] * 6
    oval = half + half
    rest = [oval[(6 + i) % len(oval)] for i in range(len(oval) - 3)]  # three curves short
    base = build_chain(rest, start=Pose.make(y=150_000_000))  # 150 km: past the packed keys
    ends = base.connectable_ends()
    for slop in (0.0, 5.0):
        result = solve({"curve": 4, "straight": 2}, catalog,
                       SolverConfig(slop=slop, min_pieces=1, max_pieces=5),
                       base=base, grow_from=ends[-1], close_onto=ends[0])
        assert result.stats.engine == "field" and len(result.solutions) == 1
    with pytest.raises(ValueError, match="does not fit the integer lattice"):
        solve({"curve": 4, "straight": 2}, catalog, SolverConfig(engine="lattice", max_pieces=5),
              base=base, grow_from=ends[-1], close_onto=ends[0])


@pytest.mark.parametrize("spec", [
    {"id": "x", "paths": "abc"},
    {"id": "x", "paths": [{"segments": [5]}]},
    {"id": "x", "paths": [{"start": "s", "segments": [{"type": "straight", "run": 1}]}]},
    {"id": "x", "paths": [{"segments": "abc"}]},
    "not a piece",
])
def test_malformed_catalogue_entries_are_bad_input(spec):
    from duplotrain.pieces import parse_piece

    with pytest.raises(ValueError):
        parse_piece(spec)


def test_a_catalogue_keyed_apart_from_its_piece_ids_is_refused():
    catalog = default_catalog()
    with pytest.raises(ValueError, match="must agree"):
        solve({"my_curve": 12}, {"my_curve": catalog["curve"]})
