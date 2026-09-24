"""Stateful driving, the looping taxonomy, and isomorphism of perfect tracks."""

import importlib
import os
import subprocess
import sys
from itertools import islice
from pathlib import Path

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.drive import (
    ClassificationLimitError,
    DriveLimitError,
    _tongue_assignments,
    classify,
    drive,
)
from duplotrain.explore import congruence_key, find_perfect_loops, make_dogbone
from duplotrain.geometry import ORIGIN
from duplotrain.gui import Session, dispatch_session
from duplotrain.layout import Layout, build_chain, layout_to_dict
from duplotrain.solver import SolverConfig, _solution_overlaps, solve

LEFT = (0, 1)


@pytest.fixture(scope="module")
def catalog():
    return default_catalog()


def closed_circle(catalog):
    layout = build_chain([(catalog["curve"], *LEFT)] * 12)
    return layout.join(layout.open_ends()[1], layout.open_ends()[0])


def closed_oval(catalog):
    pieces = (
        [(catalog["straight"], 0, 1)] * 2
        + [(catalog["curve"], *LEFT)] * 6
        + [(catalog["straight"], 0, 1)] * 2
        + [(catalog["curve"], *LEFT)] * 6
    )
    layout = build_chain(pieces)
    return layout.join(layout.open_ends()[1], layout.open_ends()[0])


@pytest.fixture(scope="module")
def teardrops(catalog):
    result = solve(
        {"switch": 1, "curve": 12},
        catalog,
        SolverConfig(
            use_all_pieces=True, reversing_loops=True, max_results=100, max_nodes=600_000
        ),
    )
    assert result.solutions
    return result.solutions


@pytest.fixture(scope="module")
def teardrop(catalog, teardrops):
    from duplotrain.explore import pick_stem_tailed

    sol = pick_stem_tailed(teardrops, catalog)
    assert sol is not None, "a stem-tailed teardrop must exist among the three"
    return sol


# -- drive semantics ---------------------------------------------------------------


def test_circle_drives_forever_one_way(catalog):
    report = drive(closed_circle(catalog))
    assert report.outcome == "endless"
    assert report.period == 12
    assert report.covers(closed_circle(catalog))
    assert report.reversals == 0


def test_switch_state_forced_by_trailing_move(catalog, teardrop):
    """Facing moves follow the tongue; trailing moves overwrite it."""
    # Grow the tail: one straight with the direction stone on it.
    tail = teardrop.layout.connectable_ends()[0]
    layout, idx = teardrop.layout.attach(catalog["straight"], 0, tail)
    layout = layout.with_accessory(idx, "stone_direction")

    # Placed on the tail straight heading outward: the stone bounces it back in.
    # (Entering via the open tip instead is the doomed start: bounce, then off the
    # end -- which is exactly why the teardrop is only locally looping.)
    report = drive(layout, start=(idx, 0))
    assert report.outcome == "endless"
    assert report.reversals >= 2
    # Within one period the switch is trailed from BOTH branches: the tongue
    # alternates, so the train alternates lobes -- and covers every piece both ways.
    switch_index = next(
        i for i, p in enumerate(layout.placements) if p.piece.id == "switch"
    )
    cycle = report.steps[report.cycle_start :]
    entries = {e for p, e, _x in cycle if p == switch_index}
    assert {1, 2} <= entries  # entered via left AND right branches (trailing moves)
    assert 0 in entries  # and via the stem (facing moves)


def test_wrong_tongue_derails_at_a_dangling_stub(catalog):
    """A circle with a switch is safe trailing, fatal facing the open branch."""
    layout = build_chain([(catalog["switch"], 0, 1)] + [(catalog["curve"], *LEFT)] * 11)
    layout = layout.join(layout.open_ends()[-1], (0, 0))
    switch = 0
    # Trailing around (entering the switch via its left branch): always endless.
    assert drive(layout, start=(0, 1)).outcome == "endless"
    # Facing the switch with the tongue set to the dangling right branch: off we go.
    report = drive(layout, start=(0, 0), switch_states={switch: 2})
    assert report.outcome == "derailed"
    # Tongue correctly set: endless.
    assert drive(layout, start=(0, 0), switch_states={switch: 1}).outcome == "endless"


def test_stop_stone_parks_every_run(catalog):
    layout = closed_oval(catalog).with_accessory(0, "stone_stop")
    verdict = classify(layout)
    assert not verdict.locally_looping
    assert drive(layout).outcome == "stopped"


# -- the looping ladder --------------------------------------------------------------


def test_plain_circle_is_completely_but_not_perfectly_looping(catalog):
    verdict = classify(closed_circle(catalog))
    assert verdict.locally_looping
    assert verdict.looping
    assert verdict.completely_looping
    assert not verdict.perfectly_looping  # every run is one-directional


def test_oval_with_direction_stone_is_perfectly_looping(catalog):
    layout = closed_oval(catalog).with_accessory(0, "stone_direction")
    verdict = classify(layout)
    assert verdict.perfectly_looping


def test_circle_with_stub_is_only_locally_looping(catalog):
    layout = build_chain([(catalog["switch"], 0, 1)] + [(catalog["curve"], *LEFT)] * 11)
    layout = layout.join(layout.open_ends()[-1], (0, 0))
    verdict = classify(layout)
    assert verdict.locally_looping
    assert not verdict.looping  # facing the stub with the wrong tongue derails


def test_teardrop_with_stone_is_only_locally_looping(catalog, teardrop):
    """The open tail tip is a doomed start, however clever the stone placement."""
    tail = teardrop.layout.connectable_ends()[0]
    layout, idx = teardrop.layout.attach(catalog["straight"], 0, tail)
    layout = layout.with_accessory(idx, "stone_direction")
    verdict = classify(layout)
    assert verdict.locally_looping
    assert not verdict.looping


def test_dogbone_is_perfectly_looping_with_no_stone(catalog, teardrop):
    dogbone = make_dogbone(teardrop, catalog, bar_straights=2)
    assert dogbone.is_closed
    assert not dogbone.accessories
    verdict = classify(dogbone)
    assert verdict.perfectly_looping


def test_branch_tailed_teardrop_is_a_one_way_trap(catalog, teardrops):
    """The other teardrop flavour absorbs the train into a one-way circuit; it can
    never make a dogbone, and make_dogbone says so instead of building a dud."""
    from duplotrain.explore import is_stem_tailed, make_dogbone

    branch_tailed = next(
        (s for s in teardrops if not is_stem_tailed(s, catalog)), None
    )
    assert branch_tailed is not None
    with pytest.raises(ValueError, match="branch-tailed"):
        make_dogbone(branch_tailed, catalog)


def test_direction_stone_at_buffer_face_makes_a_safe_terminator(catalog, teardrop):
    """The user's construction: teardrop + tail + [stone at the buffer face][buffer].

    Every approach to the buffer reverses at the wall, the doomed tip start no longer
    exists, and the buffer itself (never drivable through) is excluded from coverage
    -- so the whole build becomes PERFECTLY looping.
    """
    tail = teardrop.layout.connectable_ends()[0]
    layout, s1 = teardrop.layout.attach(catalog["straight"], 0, tail)
    layout, b = layout.attach(catalog["buffer"], 0, (s1, 1))
    layout = layout.with_accessory(s1, "stone_direction", at_port=1)  # at the buffer face
    assert layout.is_closed  # buffer face sealed, everything else mated

    verdict = classify(layout)
    assert verdict.looping, verdict.counterexample
    assert verdict.completely_looping
    assert verdict.perfectly_looping

    # A mid-piece stone in the same spot is NOT safe: a train setting off from the
    # buffer side triggers it and shunts itself into the bumper.
    unsafe = teardrop.layout
    unsafe, s2 = unsafe.attach(catalog["straight"], 0, tail)
    unsafe, _b2 = unsafe.attach(catalog["buffer"], 0, (s2, 1))
    unsafe = unsafe.with_accessory(s2, "stone_direction")
    bad = classify(unsafe)
    assert bad.locally_looping
    assert not bad.looping


def test_shuttle_with_face_stones_is_perfectly_looping(catalog):
    """[buffer][stone@face ... straights ... stone@face][buffer]: pure ping-pong."""
    chain = build_chain([(catalog["straight"], 0, 1)] * 3)
    layout, b1 = chain.attach(catalog["buffer"], 0, chain.open_ends()[0])
    layout, b2 = layout.attach(catalog["buffer"], 0, (2, 1))
    layout = layout.with_accessory(0, "stone_direction", at_port=0)  # at buffer 1's face
    layout = layout.with_accessory(2, "stone_direction", at_port=1)  # at buffer 2's face
    assert layout.is_closed

    verdict = classify(layout)
    assert verdict.perfectly_looping
    report = drive(layout, start=(1, 0))
    assert report.outcome == "endless"
    assert report.reversals >= 2


def test_positioned_stones_serialise(catalog):
    from duplotrain.layout import layout_from_dict, layout_to_dict

    layout = build_chain([(catalog["straight"], 0, 1)])
    layout = layout.with_accessory(0, "stone_direction", at_port=1)
    rebuilt = layout_from_dict(layout_to_dict(layout), catalog)
    assert rebuilt == layout
    assert rebuilt.stone_entries_on(0) == [("stone_direction", 1)]


# -- isomorphism ---------------------------------------------------------------------


def test_congruence_ignores_placement_pose(catalog):
    a = closed_circle(catalog)
    # The same circle built starting from a rotated, translated pose.
    from duplotrain.geometry import Pose

    b = build_chain(
        [(catalog["curve"], *LEFT)] * 12, start=Pose.make(500, -321, 0, 5)
    )
    b = b.join(b.open_ends()[1], b.open_ends()[0])
    assert congruence_key(a) == congruence_key(b)
    assert congruence_key(a) != congruence_key(closed_oval(catalog))


def test_congruence_identifies_same_curve_different_pieces(catalog):
    """A level crossing draws the same line as a straight: isomorphic layouts."""
    with_straight = closed_oval(catalog)
    pieces = (
        [(catalog["level_crossing"], 0, 1), (catalog["straight"], 0, 1)]
        + [(catalog["curve"], *LEFT)] * 6
        + [(catalog["straight"], 0, 1)] * 2
        + [(catalog["curve"], *LEFT)] * 6
    )
    with_crossing = build_chain(pieces)
    with_crossing = with_crossing.join(
        with_crossing.open_ends()[1], with_crossing.open_ends()[0]
    )
    assert congruence_key(with_straight) == congruence_key(with_crossing)


def test_find_perfect_loops_dedupes_isomorphs(catalog):
    """12 curves + 4 straights: four non-isomorphic perfectly looping tracks."""
    cfg = SolverConfig(use_all_pieces=True, max_results=100)
    found = find_perfect_loops({"curve": 12, "straight": 4}, catalog, cfg)
    assert found.stats.complete
    assert len(found) == 4  # oval, two parallelograms, rounded square -- stone added
    for layout, verdict in found:
        assert verdict.perfectly_looping
        assert any(sid == "stone_direction" for _i, sid in layout.accessories)
    keys = {congruence_key(layout) for layout, _v in found}
    assert len(keys) == 4
    # Level crossings draw the same line as straights: the solver's nine piece
    # arrangements trace those same four curves, and each counts once.
    box = {"curve": 12, "straight": 2, "level_crossing": 2}
    assert len(solve(box, catalog, cfg).solutions) == 9
    crossed = find_perfect_loops(box, catalog, cfg)
    assert crossed.stats.complete and len(crossed) == 4
    assert {congruence_key(layout) for layout, _v in crossed} == keys
    assert all(verdict.perfectly_looping for _layout, verdict in crossed)


def test_a_crossing_on_the_tail_is_not_taken_for_the_switch(catalog):
    from duplotrain.explore import is_stem_tailed

    result = solve({"switch": 1, "curve": 12, "crossing": 1}, catalog,
                   SolverConfig(reversing_loops=True, max_results=2000))
    tailed = []
    for solution in result.solutions:
        ids = [getattr(step, "piece_id", None) for step in solution.steps]
        if (solution.kind == "reversing" and "crossing" in ids
                and ids.index("crossing") < ids.index("switch")):
            tailed.append((solution.steps[ids.index("switch")].entry == 0, solution))
    assert tailed
    for via_stem, solution in tailed:
        assert is_stem_tailed(solution, catalog) is via_stem


@pytest.mark.parametrize("start", [(-1, 0), (0, 5), (16, 0), [0, 0], (0, True)])
def test_a_start_must_be_a_port_of_the_layout(catalog, start):
    oval = build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["straight"], 0, 1)] * 2
                       + [(catalog["curve"], 0, 1)] * 6 + [(catalog["straight"], 0, 1)] * 2)
    with pytest.raises(ValueError, match="not a port"):
        drive(oval.join((15, 1), (0, 0)), start=start)


def test_a_train_never_starts_through_a_sealed_face_or_on_no_track(catalog):
    bar = build_chain([(catalog["straight"], 0, 1), (catalog["buffer"], 0, 1)])
    with pytest.raises(ValueError, match="sealed buffer face"):
        drive(bar, start=(1, 1))
    assert drive(bar, start=(0, 0)).outcome == "buffered"
    with pytest.raises(ValueError, match="nothing to drive on"):
        drive(Layout())


def test_the_counterexample_breaks_the_first_failed_property(catalog):
    # One direction round the oval stops at the stone, the other runs forever but
    # never covers the stone's face both ways: the report must show the stop.
    oval = solve({"curve": 12, "straight": 4}, catalog,
                 SolverConfig(use_all_pieces=True, max_results=5)).solutions[0].layout
    straight = next(i for i, p in enumerate(oval.placements) if p.piece.id == "straight")
    entered = next(e for p, e, _x in drive(oval, start=(0, 0)).steps if p == straight)
    verdict = classify(oval.with_accessory(straight, "stone_stop", at_port=entered))
    assert verdict.locally_looping and not verdict.looping
    assert verdict.counterexample[2] == "stopped"


def _switch_ring(n):
    """Exact ring of 4n + 12 switches, each with one dangling branch, and a stone."""
    sw, st = default_catalog()["switch"], default_catalog()["straight"]
    side = [(sw, 0, 1), (sw, 1, 0)] * n + [(st, 0, 1)]
    chain = build_chain(([(sw, 0, 1)] * 6 + side) * 2)
    ring = chain.join((len(chain.placements) - 1, 1), (0, 0))
    straight = next(i for i, p in enumerate(ring.placements) if p.piece.id == "straight")
    return ring.with_accessory(straight, "stone_direction")


def test_a_half_never_driven_is_not_swept_both_ways(catalog):
    # A mid-piece stone on M and a stone on B's face toward M: every cycle bounces
    # between M's midpoint and that face, so M's other half is never driven.
    oval = build_chain(([(catalog["straight"], 0, 1)] * 2 + [(catalog["curve"], 0, 1)] * 6) * 2)
    oval = oval.join((15, 1), (0, 0))
    layout = oval.with_accessory(0, "stone_direction")
    layout = layout.with_accessory(1, "stone_direction", at_port=0)
    verdict = classify(layout)
    assert verdict.completely_looping and not verdict.perfectly_looping
    # One stone mid-piece sweeps both halves of its straight both ways: perfect.
    assert classify(oval.with_accessory(0, "stone_direction")).perfectly_looping


def test_an_endless_run_found_exactly_at_the_step_budget_is_a_verdict(catalog):
    circle = build_chain([(catalog["curve"], 0, 1)] * 12).join((0, 0), (11, 1))
    report = drive(circle, max_steps=12)
    assert report.outcome == "endless" and len(report.steps) == 12
    with pytest.raises(DriveLimitError, match="11-step budget"):
        drive(circle, max_steps=11)


def test_drive_memory_does_not_grow_with_steps_times_switches():
    import tracemalloc

    ring = _switch_ring(100)
    assert sum(p.piece.id == "switch" for p in ring.placements) == 412
    tracemalloc.start()
    try:
        report = drive(ring, start=(0, 0), max_steps=10_000)
        _current, peak = tracemalloc.get_traced_memory()
    finally:
        tracemalloc.stop()
    assert report.outcome == "endless" and len(report.steps) > 400
    # One tongue tuple per change, not one per step (a copy per step took 6 MiB).
    assert peak < 2 * 2**20


# -- stones on the return pass -------------------------------------------------------


def exact_oval():
    catalog = default_catalog()
    half = [(catalog["straight"], 0, 1)] + [(catalog["curve"], 0, 1)] * 6
    layout = build_chain(half * 2)
    return layout.join(*layout.connectable_ends())


def oval_with_return_stop(face):
    """Both stone placements are accepted by the shared editor API."""
    session = Session()
    dispatch_session(session, "/api/import", {
        "revision": session.revision, "data": layout_to_dict(exact_oval()),
    })
    for sid, position in (("stone_direction", None), ("stone_stop", face)):
        dispatch_session(session, "/api/stone", {
            "revision": session.revision,
            "placement": 0, "id": sid, "at_port": position,
        })
    layout = session.layout
    assert layout.is_closed and not layout.joint_issues()
    assert not _solution_overlaps(layout, 0, 120.0, 8.0)
    return layout


@pytest.mark.parametrize("face", [0, 1])
def test_returning_from_mid_piece_reversal_hits_the_face_stop(face):
    layout = oval_with_return_stop(face)
    # Starting away from the face is silent; returning toward it after the green
    # stone must fire the red stone before the train leaves that same connector.
    assert drive(layout, start=(0, face)).outcome == "stopped"


@pytest.mark.parametrize("face", [0, 1])
def test_reachable_return_stop_prevents_a_perfect_verdict(face):
    layout = oval_with_return_stop(face)
    verdict = classify(layout)
    assert not verdict.perfectly_looping
    assert not verdict.looping


# -- the classification budget -------------------------------------------------------


def switches(count):
    layout = Layout()
    switch = default_catalog()["switch"]
    for _ in range(count):
        layout, _ = layout.with_piece(switch, ORIGIN)
    return layout


def test_tongue_assignments_can_yield_a_small_prefix_of_a_large_product():
    assignments = list(islice(_tongue_assignments(switches(24)), 3))
    assert len(assignments) == 3
    assert all(len(a) == 24 for a in assignments)
    assert len({tuple(a.items()) for a in assignments}) == 3
    assignments[0].clear()
    assert len(assignments[1]) == 24


def test_large_classification_fails_before_any_simulation(monkeypatch):
    def unexpected_drive(*args, **kwargs):
        pytest.fail("classification must check its budget before simulation")

    monkeypatch.setattr(importlib.import_module("duplotrain.drive"), "drive", unexpected_drive)
    with pytest.raises(ClassificationLimitError, match="1,207,959,552 runs"):
        classify(switches(24))


def test_classification_budget_is_explicit_and_never_returns_a_partial_verdict():
    layout = switches(1)
    with pytest.raises(ClassificationLimitError, match="6 runs"):
        classify(layout, max_runs=5)
    bounded = classify(layout, max_runs=6)
    assert bounded == classify(layout, max_runs=None)
    assert bounded.runs == 6 and not bounded.locally_looping


@pytest.mark.parametrize("budget", [0, -1, 1.5, True])
def test_classification_rejects_invalid_budget(budget):
    with pytest.raises(ValueError, match="max_runs"):
        classify(switches(1), max_runs=budget)


@pytest.mark.skipif(sys.platform != "linux", reason="isolated Linux memory-budget probe")
def test_unbounded_classifier_reaches_first_simulation_with_bounded_memory():
    # Stop on the first call to drive: exercise lazy allocation without running an
    # exponential search. (test_large_classification_fails_before_any_simulation
    # checks the default budget fails before any simulation.)
    source = '''
import importlib
import resource
from duplotrain import build_chain, default_catalog
module = importlib.import_module("duplotrain.drive")
switch = default_catalog()["switch"]
layout = build_chain([(switch, 0, 1 if i % 2 == 0 else 2) for i in range(25)])
class FirstSimulation(Exception):
    pass
def stop(*args, **kwargs):
    raise FirstSimulation
module.drive = stop
with open("/proc/self/status") as status:
    size = next(int(line.split()[1]) * 1024 for line in status if line.startswith("VmSize:"))
limit = size + 64 * 1024 * 1024
resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
try:
    module.classify(layout, max_runs=None)
except FirstSimulation:
    print("first simulation started")
else:
    raise AssertionError("no simulation")
'''
    env = dict(os.environ, PYTHONPATH=str(Path(__file__).resolve().parents[1] / "src"))
    process = subprocess.run([sys.executable, "-c", source], env=env, text=True,
                             capture_output=True, timeout=15, check=False)
    assert process.returncode == 0, process.stderr
    assert process.stdout.strip() == "first simulation started"
