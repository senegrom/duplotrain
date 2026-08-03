"""Stateful driving, the looping taxonomy, and isomorphism of perfect tracks."""

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.drive import classify, drive
from duplotrain.explore import congruence_key, find_perfect_loops, make_dogbone
from duplotrain.layout import build_chain
from duplotrain.solver import SolverConfig, solve

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
    found = find_perfect_loops(
        {"curve": 12, "straight": 4},
        catalog,
        SolverConfig(use_all_pieces=True, max_results=100),
    )
    assert len(found) == 4  # oval, two parallelograms, rounded square -- stone added
    for layout, verdict in found:
        assert verdict.perfectly_looping
        assert any(sid == "stone_direction" for _i, sid in layout.accessories)
    keys = {congruence_key(layout) for layout, _v in found}
    assert len(keys) == 4