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
