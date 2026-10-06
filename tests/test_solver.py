"""The loop finder: correctness, completeness on small inventories, and dedup."""

import pytest

import duplotrain.solver as solver_module
from duplotrain.catalog import default_catalog
from duplotrain.geometry import ORIGIN
from duplotrain.layout import build_chain
from duplotrain.solver import SolverConfig, solve


def assert_loop_is_sound(solution):
    """Every recorded link of a reported loop truly mates (exactly, or within its gap)."""
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
    assert_loop_is_sound(sol)


def test_eleven_curves_make_nothing(catalog):
    # An exact closed track turns a full circle at least in all (Fenchel's theorem).
    # Eleven curves turn 330 degrees: no straights or crossings make them a loop,
    # and the search knows so before it places a piece.
    for box in ({"curve": 11}, {"curve": 11, "straight": 30, "crossing": 2}):
        result = solve(box, catalog)
        assert result.solutions == [] and result.stats.complete
        assert result.stats.stop_reason == "exhausted"
        assert result.stats.nodes == result.stats.max_pieces_searched == 0
    # No loop of any length exists, so a piece limit cuts none off: that answer is
    # complete too.
    capped = solve({"curve": 11}, catalog, SolverConfig(max_pieces=6))
    assert capped.solutions == [] and capped.stats.complete
    assert capped.stats.stop_reason == "exhausted"


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
        assert_loop_is_sound(sol)
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
    assert_loop_is_sound(best)


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


def test_only_an_exact_fresh_loop_must_turn_a_full_circle(catalog):
    from duplotrain.catalog import DEFAULT_CATALOG_SPECS
    from duplotrain.pieces import parse_pieces

    # A teardrop's lobe meets its junction at an angle, which turns the rest: an arc
    # of 300 degrees, a crossing and a straight make two, though no loop.
    hooked = parse_pieces(list(DEFAULT_CATALOG_SPECS) + [
        {"id": "arc300", "width": 64, "paths": [{"segments": [
            {"type": "arc", "radius": {"alg": [0, 0, 64, 0]}, "degrees": -300}]}]}])
    stock = {"straight": 1, "crossing": 1, "arc300": 1}
    teardrops = solve(stock, hooked, SolverConfig(reversing_loops=True, min_pieces=2))
    assert teardrops.stats.complete
    assert [s.kind for s in teardrops.solutions] == ["reversing", "reversing"]
    loops = solve(stock, hooked, SolverConfig(min_pieces=2))
    assert not loops.solutions and loops.stats.complete and loops.stats.nodes == 0
    # A forced fit's gap may stand in for any turn: four straights in a row close
    # 512 mm apart inside a 600 mm slop.
    forced = solve({"straight": 4}, catalog, SolverConfig(slop=600.0))
    assert [(s.piece_count, s.gap) for s in forced.solutions] == [(4, 512.0)]
    # A completion's base turns the rest: six curves close six more into a circle,
    # so a limit of five pieces cuts that circle off.
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    cut = solve({"curve": 6}, catalog, SolverConfig(min_pieces=1, max_pieces=5), base=base)
    assert not cut.solutions and not cut.stats.complete
    assert cut.stats.stop_reason == "piece_limit"


def test_a_closed_walk_turns_in_a_piece_by_its_arcs_once_a_pass(catalog):
    from duplotrain.pieces import parse_piece

    # Each pass takes one route through two ports: once through a switch, twice
    # through a piece with two separate routes, such as a double-track curve.
    turns = {pid: solver_module._circle_turn(piece) for pid, piece in catalog.items()}
    assert None not in turns.values()  # no catalogue piece has a shape of unknown turn
    assert (turns["curve"], turns["switch"], turns["crossing"], turns["slope"]) == (30, 30, 0, 0)
    double = parse_piece({"id": "double_curve", "width": 64, "paths": [
        {"segments": [{"type": "arc", "radius": 256, "degrees": 30}]},
        {"start": {"x": 0, "y": 64, "heading_deg": 0},
         "segments": [{"type": "arc", "radius": 192, "degrees": 30}]}]})
    assert len(double.ports) == 4 and solver_module._circle_turn(double) == 60
    # An arc turns by its size whichever way it bends: an S-bend by both its arcs,
    # and twelve curves drawn turning right close a circle as the left-hand ones do.
    s_bend = parse_piece({"id": "s_bend", "width": 64, "paths": [{"segments": [
        {"type": "arc", "radius": 256, "degrees": 30},
        {"type": "arc", "radius": 256, "degrees": -30}]}]})
    assert solver_module._circle_turn(s_bend) == 60
    right = parse_piece({"id": "right_curve", "width": 64, "paths": [
        {"segments": [{"type": "arc", "radius": 256, "degrees": -30}]}]})
    circle = solve({"right_curve": 12}, {"right_curve": right})
    assert circle.stats.complete and [s.piece_count for s in circle.solutions] == [12]


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


def test_slop_reports_engineered_gap():
    """A 130 mm 'stretched straight' opposite a 128 mm one leaves exactly 2 mm.

    No arrangement of those two plus 12 curves closes exactly (the straights' vector
    sum has magnitude >= 2 mm), so with slop every solution must be a forced fit
    reporting exactly that 2 mm gap -- never relabelled exact.
    """
    pieces = stretched_catalog()
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


def test_results_walk_round_in_piece_count_steps(catalog):
    result = solve({"curve": 12, "straight": 4}, catalog, SolverConfig(max_results=5))
    assert result.solutions
    for sol in result.solutions:
        assert sol.layout.is_closed or sol.open_stubs > 0
        # Walking the loop from the first piece returns in piece_count steps.
        steps = list(sol.layout.walk(start=(0, 0)))
        assert len(steps) == sol.piece_count


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
    # Each piece a walk places is a nested frame, and Python allows about a
    # thousand: a search places _MAX_SEARCH_DEPTH pieces at most. A loop that
    # long is found, in one pass at the cap.
    box = {"curve": 12, "straight": 2000}
    cap = solver_module._MAX_SEARCH_DEPTH
    deepest = solve(box, catalog, SolverConfig(min_pieces=cap, max_results=1))
    assert [s.piece_count for s in deepest.solutions] == [cap]
    assert deepest.stats.max_pieces_searched == cap
    # A longer loop, or one of all 2,012 pieces, is cut by the cap unsearched.
    for config in (SolverConfig(min_pieces=1500, max_nodes=20_000),
                   SolverConfig(use_all_pieces=True, max_nodes=20_000)):
        cut = solve(box, catalog, config)
        assert not cut.solutions and not cut.stats.complete
        assert cut.stats.stop_reason == "piece_limit"
        assert cut.stats.nodes == cut.stats.max_pieces_searched == 0
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


def test_piece_limits_no_loop_can_meet_run_no_pass(catalog):
    # Fourteen pieces: a loop of thirteen or more under a bound of twelve, or one of
    # every piece under a bound of thirteen, is cut by the piece limit unsearched.
    box = {"curve": 12, "straight": 2}
    for config in (SolverConfig(min_pieces=13, max_pieces=12),
                   SolverConfig(use_all_pieces=True, max_pieces=13)):
        cut = solve(box, catalog, config)
        assert not cut.solutions and not cut.stats.complete
        assert cut.stats.stop_reason == "piece_limit"
        assert cut.stats.nodes == cut.stats.max_pieces_searched == 0
    # No loop of more pieces than the box holds exists: that answer is complete.
    longer = solve(box, catalog, SolverConfig(min_pieces=15))
    assert not longer.solutions and longer.stats.complete
    assert longer.stats.stop_reason == "exhausted"
    assert longer.stats.nodes == longer.stats.max_pieces_searched == 0


@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_contour_zero_does_not_emit_an_empty_fresh_loop(engine):
    result = solve({}, default_catalog(), SolverConfig(min_pieces=0, engine=engine))
    assert not result.solutions and result.stats.complete


def stretched_catalog():
    """The default pieces plus a 130 mm straight that closes 2 mm short."""
    from duplotrain.catalog import DEFAULT_CATALOG_SPECS
    from duplotrain.pieces import parse_pieces

    return parse_pieces(list(DEFAULT_CATALOG_SPECS) + [{
        "id": "stretched", "name": "Stretched straight (test)", "category": "track",
        "width": 64, "paths": [{"segments": [{"type": "straight", "run": 130}]}],
    }])


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


def replay(steps, pieces, force_final_join, base=None, grow_from=None, close_onto=None,
           final_target=None):
    """Rebuild a solution from its step trace with Layout.attach and Layout.join.

    Loop mode (no *base*): the first placed piece plugs onto a virtual face at the
    origin and the trace must return there.  Completion mode: the trace grows from the
    open end *grow_from* of *base* and finally joins onto *close_onto*.  A reversing
    loop overrides either with *final_target*: the walk's end joins that junction stub
    instead, leaving the anchor face open as the tail.
    """
    from duplotrain import Layout
    from duplotrain.solver import _Place, _Transit

    layout = base if base is not None else Layout()
    cursor, target = grow_from, close_onto
    for step in steps:
        if isinstance(step, _Place):
            piece = pieces[step.piece_id]
            if cursor is None:
                layout, index = layout.with_piece(piece, piece.frame_for(step.entry, ORIGIN))
                target = (index, step.entry)
            else:
                layout, index = layout.attach(piece, step.entry, cursor)
            cursor = (index, step.exit)
        else:
            assert isinstance(step, _Transit) and cursor is not None
            layout = layout.join(cursor, (step.placement, step.entry), force=force_final_join)
            cursor = (step.placement, step.exit)
    if final_target is not None:
        target = final_target
    assert cursor is not None and target is not None
    return layout.join(cursor, target, force=force_final_join)


def test_solution_layouts_equal_their_replayed_constructions(catalog):
    from duplotrain import Layout
    from duplotrain.solver import _Place, _Transit

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
            replayed = replay(solution.steps, catalog, force_final_join=solution.gap > 0,
                              base=base, grow_from=grow_from, close_onto=close_onto,
                              final_target=final_target)
            assert isinstance(solution.layout, Layout) and replayed == solution.layout
            checked += 1
            transits += any(isinstance(step, _Transit) for step in solution.steps)
    assert checked >= 30 and transits >= 1


@pytest.mark.parametrize("inventory, loops, teardrops", [
    ({"curve": 12, "switch": 1}, 2, 3),
    # A second switch at the tail's end: the walk may start by either free branch.
    ({"curve": 12, "switch": 2}, 19, 178),
])
def test_reversing_loop_mode_offers_each_layout_once(inventory, loops, teardrops):
    # A ring through a switch is a loop with a stub, not a teardrop without a tail.
    from duplotrain.explore import congruence_key

    result = solve(inventory, default_catalog(),
                   SolverConfig(reversing_loops=True, max_results=1000))
    keys = [congruence_key(s.layout) for s in result.solutions]
    assert result.stats.complete and len(keys) == len(set(keys))
    kinds = [s.kind for s in result.solutions]
    assert (kinds.count("loop"), kinds.count("reversing")) == (loops, teardrops)


def test_a_reversing_lobe_driven_either_way_round_is_one_result():
    # The same teardrop, entered at the stem, can go round its lobe either way.
    from duplotrain.explore import congruence_key

    catalog = default_catalog()
    result = solve({"curve": 12, "switch": 1, "straight": 2}, catalog,
                   SolverConfig(reversing_loops=True, max_results=100))
    keys = [congruence_key(s.layout) for s in result.solutions if s.kind == "reversing"]
    assert len(keys) == len(set(keys)) == 33
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


def test_a_sideways_step_below_float_resolution_keeps_its_hand():
    # The one-handed loop search sorts U-turns by the sign of their sideways step,
    # decided exactly: in floats both of this hairpin's turns looked alike, and
    # the search skipped the one loop two of them make.
    from duplotrain.pieces import parse_piece

    radius = {"alg": ["-1.41421356237309504", 1, 0, 0]}  # 8.8e-18 mm, 0.0 as a float
    hairpin = parse_piece({"id": "hairpin", "width": 8, "paths": [
        {"segments": [{"type": "arc", "radius": radius, "degrees": 180}]}]})
    result = solve({"hairpin": 2}, {"hairpin": hairpin}, SolverConfig(min_pieces=2))
    assert result.stats.complete and len(result.solutions) == 1


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


def test_a_catalogue_keyed_apart_from_its_piece_ids_is_refused():
    catalog = default_catalog()
    with pytest.raises(ValueError, match="must agree"):
        solve({"my_curve": 12}, {"my_curve": catalog["curve"]})


def test_lattice_ends_apart_by_less_than_float_resolution_make_a_forced_fit():
    import math
    from itertools import islice

    from duplotrain.solver import _compile_lattice, _flat_xy

    def convergents():  # of sqrt3 = [1; 1, 2, 1, 2, ...]
        p0, q0, p1, q1 = 1, 0, 1, 1
        for a in [1, 2] * 40:
            p0, q0, p1, q1 = p1, q1, a * p1 + p0, a * q1 + q0
            yield p1, q1

    # Exact lattice poses p - q*sqrt3 mm apart, which floats cannot tell apart.
    p, q = next((p, q) for p, q in islice(convergents(), 80)
                if math.dist(_flat_xy((20 * p, -40 * q, 0, 20 * q, 0, 0)),
                             _flat_xy((0, 0, 0, 0, 0, 0))) == 0.0)
    engine = _compile_lattice(ORIGIN, ORIGIN, {}, {})
    cursor = (20 * p, -40 * q, 0, 20 * q, 0, engine.anchor[5])
    assert engine.near_anchor(cursor, 1.0) == math.ulp(0.0)
    mate = (*cursor[:5], (cursor[5] + 6) % 12)
    assert engine.near_pose(cursor, (0, 0, 0, 0, 0, mate[5]), 1.0) == math.ulp(0.0)
    assert engine.near_pose(cursor, mate, 1.0) == 0.0  # the same point, facing it


def test_moves_too_long_for_the_packed_table_keys_run_on_the_field_engine(monkeypatch, catalog):
    base = build_chain([(catalog["curve"], 0, 1)] * 9)
    ends = base.connectable_ends()
    config = SolverConfig(min_pieces=1, max_pieces=5, max_results=10)
    lattice = solve({"curve": 4, "straight": 2}, catalog, config,
                    base=base, grow_from=ends[-1], close_onto=ends[0])
    monkeypatch.setattr(solver_module, "_MOVE_LIMIT", 1)  # every move is too long
    field = solve({"curve": 4, "straight": 2}, catalog, config,
                  base=base, grow_from=ends[-1], close_onto=ends[0])
    assert (lattice.stats.engine, field.stats.engine) == ("lattice", "field")
    assert [s.signature for s in field.solutions] == [s.signature for s in lattice.solutions]


def crossings_in_a_row(catalog, n, end_heading=0):
    """Unlinked crossings end to end, then a straight: a walk of n free transits."""
    from duplotrain.geometry import Pose
    from duplotrain.layout import Layout, Placement, layout_from_dict, layout_to_dict

    placements = [Placement(catalog["crossing"], Pose.make(128 * k, 0, 0, 0)) for k in range(n)]
    placements.append(Placement(catalog["straight"], Pose.make(128 * n, 0, 0, end_heading)))
    # Unlinked, as a layout file may be: the editor's import accepts it.
    return layout_from_dict(layout_to_dict(Layout(tuple(placements), {})), catalog)


def test_a_walk_stops_at_its_step_cap_and_says_so(monkeypatch, catalog):
    base = crossings_in_a_row(catalog, 30)
    config = SolverConfig(min_pieces=0, max_results=1)
    walked = solve({}, catalog, config, base=base, grow_from=(0, 1), close_onto=(30, 0))
    assert len(walked.solutions) == 1 and walked.stats.stop_reason == "result_limit"
    # Fewer nested frames than the walk needs: no RecursionError, no false exhaustion.
    monkeypatch.setattr(solver_module, "_MAX_WALK_STEPS", 20)
    cut = solve({}, catalog, config, base=base, grow_from=(0, 1), close_onto=(30, 0))
    assert not cut.solutions and not cut.stats.complete
    assert cut.stats.stop_reason == "piece_limit"
    # A stepwise search keeps reporting the cut instead of finishing as exhausted.
    steps = solver_module.solve_steps({}, catalog, config, base=base, grow_from=(0, 1),
                                      close_onto=(30, 0), limits=solver_module.SearchLimits())
    events = [next(steps)["kind"] for _ in range(3)]
    steps.close()
    assert events[-2:] == ["walk_limit", "walk_limit"]


@pytest.mark.parametrize("unplaceable", [{"buffer": 2}, {"ramp": 2}, {"span": 2}])
def test_a_piece_no_walk_can_place_leaves_the_search_alone(catalog, unplaceable):
    # A buffer's one open face joins no walk, and a ramp with no arch to take its
    # top joins none either, nor an arch with no ramp to rest on. Counted in the
    # stock, they widened every piece budget, so the same search ran eight to
    # twenty-seven times as long, and no layout could ever use every piece.
    box = {"curve": 12, "straight": 5, "switch": 2}
    plain = solve(box, catalog, SolverConfig(max_results=25))
    extra = solve({**box, **unplaceable}, catalog, SolverConfig(max_results=25))
    assert [s.signature for s in extra.solutions] == [s.signature for s in plain.solutions]
    assert extra.stats.nodes == plain.stats.nodes
    everything = SolverConfig(use_all_pieces=True, max_results=5)
    assert solve({"curve": 12, "straight": 4, **unplaceable}, catalog, everything).solutions


def test_loops_use_bridge_parts_only_as_they_join(catalog):
    # The steam train and bridge sets: a ramp's top carries an arch's foot, and
    # arches meet at a crest, climb on with a further ramp or take raised track.
    # Loops come shortest first. One carrying the whole bridge, as long as eight
    # straights, needs eight straights back and the twelve curves: 24 pieces at least.
    result = solve({"curve": 12, "straight": 12, "ramp": 2, "span": 2}, catalog,
                   SolverConfig(min_pieces=24, max_results=25))
    assert result.solutions
    assert not any(solution.layout.joint_issues() for solution in result.solutions)

    def on_the_floor(layout):
        return len({min(placement.port_pose(port).z for port in range(len(placement.piece.ports)))
                    for placement in layout if placement.piece.category != "bridge"}) == 1

    # Some carry the whole bridge, both arches, over track that all lies on the floor.
    assert any(on_the_floor(solution.layout) and solution.layout.piece_counts.get("span") == 2
               for solution in result.solutions)


def test_a_loop_closes_only_where_the_parts_join(catalog):
    # Two arches and one ramp: no bridge fits in a loop, which could only close by
    # setting one arch's foot on the other's.
    result = solve({"curve": 12, "straight": 3, "span": 2, "ramp": 1}, catalog,
                   SolverConfig(max_results=100))
    assert result.stats.complete and result.solutions
    assert not any({"span", "ramp"} & set(s.layout.piece_counts) for s in result.solutions)


def test_a_teardrop_tail_never_ends_at_an_arch_foot(catalog):
    # A tail's open end is where the walk began: an arch's foot there would stand
    # on nothing, for it rests only on a ramp's top.
    result = solve({"curve": 11, "switch": 1, "span": 1, "ramp": 1}, catalog,
                   SolverConfig(reversing_loops=True))
    assert result.stats.complete and len(result.solutions) == 4
    assert not any(s.layout.placements[index].piece.ports[port].kind == "arch_foot"
                   for s in result.solutions for index, port in s.layout.connectable_ends())
    # So an arch with no ramp joins no teardrop at all: it is left out of the search.
    teardrops = SolverConfig(reversing_loops=True)
    assert (solve({"curve": 11, "switch": 1, "span": 1}, catalog, teardrops).stats.nodes
            == solve({"curve": 11, "switch": 1}, catalog, teardrops).stats.nodes)


def test_a_teardrop_tail_may_end_at_a_ramp_top(catalog):
    # A tail's open end is where the walk began: a ramp may stand there with its
    # top open, though no arch in the box could rest on it.
    box = {"curve": 11, "switch": 1, "ramp": 1}
    result = solve(box, catalog, SolverConfig(reversing_loops=True))
    ramped = [s for s in result.solutions if "ramp" in s.layout.piece_counts]
    assert result.stats.complete and ramped
    for teardrop in ramped:
        assert teardrop.kind == "reversing" and not teardrop.layout.joint_issues()
        [(index, port)] = teardrop.layout.connectable_ends()
        assert teardrop.layout.placements[index].piece.ports[port].kind == "ramp_top"
    # So a teardrop can use every piece, the ramp at its tail.
    everything = solve(box, catalog, SolverConfig(reversing_loops=True, use_all_pieces=True))
    assert everything.solutions
    assert all("ramp" in s.layout.piece_counts for s in everything.solutions)
    # A completion has no open tail, even one that may end in a teardrop: its walk
    # begins at the base. Left out, the ramp keeps no completion from using every piece.
    base = build_chain([(catalog["curve"], 0, 1)] * 8)
    closing = SolverConfig(min_pieces=1, reversing_loops=True, use_all_pieces=True)
    completed = solve({"curve": 4, "ramp": 1}, catalog, closing, base=base)
    assert [s.piece_count for s in completed.solutions] == [12]


def test_loops_come_shortest_first(catalog):
    # A broad box, a bridge set, a switch and a track pack: one pass at full length
    # found no loop in two million nodes. Shortest first, loops come at once.
    from duplotrain.sets import inventory_for_sets

    box, _stones = inventory_for_sets(["10874", "10872", "10882"])
    broad = solve(box, catalog, SolverConfig(max_results=25))
    assert len(broad.solutions) == 25 and broad.stats.nodes < 10_000
    assert max(s.piece_count for s in broad.solutions) <= 14
    # A result limit keeps every shorter loop: 12 curves and 6 straights make seven
    # loops of up to 16 pieces, and those are the first seven.
    every = solve({"curve": 12, "straight": 6}, catalog, SolverConfig(max_results=1000))
    first = solve({"curve": 12, "straight": 6}, catalog, SolverConfig(max_results=7))
    assert {s.signature for s in first.solutions} == {
        s.signature for s in every.solutions if s.piece_count <= 16}
    # The pass that fills the result limit is the last: the circle is the one loop
    # of twelve pieces, and no pass of more pieces follows it.
    circle = solve({"curve": 12, "straight": 6}, catalog, SolverConfig(max_results=1))
    assert [s.piece_count for s in circle.solutions] == [12]
    assert circle.stats.max_pieces_searched == 12


def test_a_stepwise_loop_search_answers_to_its_own_result_limit(catalog):
    from itertools import islice

    # Its limits replace the config's: a configured limit of one result does not
    # stop it lengthening past the circle to the oval.
    steps = solver_module.solve_steps({"curve": 12, "straight": 2}, catalog,
                                      SolverConfig(max_results=1),
                                      limits=solver_module.SearchLimits(max_results=50))
    events = list(islice(steps, 1000))
    assert [e["solution"].piece_count for e in events if e["kind"] == "solution"] == [12, 14]


@pytest.mark.parametrize("box, reversing, half_circle", [
    ({"curve": 12, "straight": 4}, False, False),
    ({"curve": 12, "switch": 1}, True, False),
    ({"curve": 6, "straight": 4}, False, True),
])
def test_each_closure_counts_once_in_the_pass_of_its_length(catalog, box, reversing,
                                                            half_circle):
    # Every pass finds the shorter loops again, but counts only those of its own
    # length: one search over every length counts what one pass per length does.
    # A completion's pass is as long as the pieces it adds: six curves close half
    # a circle, and two or four straights more make ovals.
    options = {}
    if half_circle:
        options = dict(base=build_chain([(catalog["curve"], 0, 1)] * 6),
                       grow_from=(5, 1), close_onto=(0, 0))
    every = solve(box, catalog, SolverConfig(min_pieces=1, max_results=1000,
                                              reversing_loops=reversing), **options)
    passes = [solve(box, catalog, SolverConfig(min_pieces=n, max_pieces=n, max_results=1000,
                                               reversing_loops=reversing), **options)
              for n in range(1, sum(box.values()) + 1)]
    assert every.stats.complete and every.solutions
    assert every.stats.closures_found == sum(p.stats.closures_found for p in passes)
    assert every.stats.closures_found >= len(every.solutions)
