"""Stones are encountered along each outward and return pass, not just by type."""

import pytest

from duplotrain import build_chain, classify, default_catalog, drive


def straight_with(stones):
    layout = build_chain([(default_catalog()["straight"], 0, 1)])
    for sid, position in stones:
        layout = layout.with_accessory(0, f"stone_{sid}", at_port=position)
    return layout


@pytest.mark.parametrize("entry", [0, 1])
@pytest.mark.parametrize("order", [False, True])
@pytest.mark.parametrize("reversal", ["mid", "face"])
def test_stop_on_departure_face_is_encountered_on_return(entry, order, reversal):
    stones = [("direction", None if reversal == "mid" else 1 - entry), ("stop", entry)]
    report = drive(straight_with(stones[::-1] if order else stones), start=(0, entry))
    assert report.outcome == "stopped"
    assert report.reversals == 1
    assert report.visited == {0}


@pytest.mark.parametrize("entry", [0, 1])
def test_mid_reversal_does_not_encounter_far_face_stop(entry):
    layout = straight_with([("direction", None), ("stop", 1 - entry)])
    assert drive(layout, start=(0, entry)).outcome == "derailed"
    assert drive(layout, start=(0, 1 - entry)).outcome == "stopped"


@pytest.mark.parametrize("entry", [0, 1])
@pytest.mark.parametrize("order", [False, True])
@pytest.mark.parametrize("position", [None, 0, 1])
def test_stop_has_priority_over_coincident_direction_stone(entry, order, position):
    stones = [("stop", position), ("direction", position)]
    report = drive(straight_with(stones[::-1] if order else stones), start=(0, entry))
    assert report.outcome == ("derailed" if position == entry else "stopped")
    assert report.reversals == 0


@pytest.mark.parametrize("entry", [0, 1])
def test_face_to_face_cycle_never_follows_buffer_links(entry):
    layout = straight_with([("direction", 0), ("direction", 1)])
    for port in (0, 1):
        layout, _ = layout.attach(default_catalog()["buffer"], 0, (0, port))
    report = drive(layout, start=(0, entry))
    assert report.outcome == "endless"
    assert report.period == 2
    assert report.reversals == 2
    assert report.visited == {0}  # The train never enters either bumper.
    assert set(report.steps[report.cycle_start:]) == {(0, 0, 1), (0, 1, 0)}
    assert classify(layout).perfectly_looping


@pytest.mark.parametrize("entry", [0, 1])
def test_mid_and_face_reversals_detect_internal_cycle_without_skipping_stop(entry):
    layout = straight_with([("direction", None), ("direction", entry), ("stop", 1 - entry)])
    trapped = drive(layout, start=(0, entry))
    assert trapped.outcome == "endless" and trapped.period == 1
    assert trapped.reversals == 2
    assert drive(layout, start=(0, 1 - entry)).outcome == "stopped"
    verdict = classify(layout)
    assert verdict.locally_looping and not verdict.looping
    assert not verdict.perfectly_looping


def test_internal_cycle_does_not_claim_to_cover_other_pieces():
    layout = straight_with([("direction", 0), ("direction", 1)])
    layout, _ = layout.attach(default_catalog()["straight"], 0, (0, 1))
    report = drive(layout, start=(0, 0))
    assert report.outcome == "endless" and not report.covers(layout)
    assert not classify(layout).completely_looping


@pytest.mark.parametrize("stone", ["horn", "lights", "refuel"])
def test_passive_stones_do_not_change_return_stops(stone):
    layout = straight_with([("direction", 1), ("stop", 0), (stone, None)])
    assert drive(layout, start=(0, 0)).outcome == "stopped"


PASSIVE = ("stone_horn", "stone_lights", "stone_refuel")


def with_every_passive_stone(layout):
    """Each passive stone mid-piece and on both faces of every straight."""
    for index, placement in enumerate(layout.placements):
        if placement.piece.id == "straight":
            for sid in PASSIVE:
                for position in (None, 0, 1):
                    layout = layout.with_accessory(index, sid, at_port=position)
    return layout


def test_passive_stones_never_stop_reverse_or_park_a_train():
    # With no stop or direction stone on the track, horn, lights and refuel
    # stones must leave every run exactly as it is without them.
    c = default_catalog()
    half = [(c["straight"], 0, 1)] + [(c["curve"], 0, 1)] * 6
    oval = build_chain(half * 2)
    oval = oval.join(*oval.connectable_ends())
    bar = build_chain([(c["buffer"], 1, 0)] + [(c["straight"], 0, 1)] * 2 + [(c["buffer"], 0, 1)])
    for plain in (oval, bar):
        stoned = with_every_passive_stone(plain)
        assert len(stoned.accessories) == 9 * sum(p.piece.id == "straight" for p in plain)
        starts = [(i, port) for i, p in enumerate(plain.placements) if p.piece.id != "buffer"
                  for port in range(len(p.piece.ports))]
        for start in starts:
            expected, report = drive(plain, start=start), drive(stoned, start=start)
            assert report.outcome == expected.outcome, start
            assert report.outcome == ("endless" if plain is oval else "buffered")
            assert report.reversals == 0
            assert report.steps == expected.steps and report.terminal == expected.terminal
        assert classify(stoned) == classify(plain)
