"""Stone actions and retained pages against the real editor and HTTP engine."""

import re
from fractions import Fraction
from pathlib import Path

import pytest

from duplotrain.exact import Alg
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, Placement
from tests.browser import test_editor as editor_tests

editor = editor_tests.editor
load = editor_tests.load
pytestmark = pytest.mark.browser


def crossing(session, reverse, stones=False):
    straight = session.catalog["straight"]
    pieces = [Placement(straight, Pose(Alg(-64), Alg(0), Alg(0), 0)),
              Placement(straight, Pose(Alg(0), Alg(-64), Alg(Fraction(768, 5)), 6))]
    if reverse:
        pieces.reverse()
    lower, upper = (1, 0) if reverse else (0, 1)
    layout = Layout(pieces)
    if stones:
        layout = layout.with_accessory(lower, "stone_stop")
        layout = layout.with_accessory(upper, "stone_direction")
    session.history = [layout]
    session.unlimited = True
    return lower, upper


def tap_world(page, x=0, y=0):
    point = page.evaluate("([x,y]) => worldToScreen(x,y)", [x, y])
    page.locator("#canvas").scroll_into_view_if_needed()
    bounds = page.locator("#canvas").bounding_box()
    page.touchscreen.tap(bounds["x"] + point[0], bounds["y"] + point[1])


@pytest.mark.parametrize("reverse", [False, True])
def test_stone_mount_chooser_highest_first_and_undo(editor, reverse):
    from playwright.sync_api import expect

    page, session, url, errors = editor
    _lower, upper = crossing(session, reverse)
    load(page, url)
    initial = session.snapshot()
    page.locator("#stones button").filter(has_text=re.compile("^Stop")).tap()
    tap_world(page)
    picker = page.locator("#overlap-picker")
    expect(picker).to_be_visible()
    expect(picker.locator("select option")).to_have_count(2)
    assert page.evaluate("selectedPiece") == upper
    assert not session.layout.accessories
    picker.get_by_role("button", name="Place selected stone", exact=True).tap()
    page.wait_for_function("S.snapshot.layout.accessories.length === 1 && !apiBusy")
    assert session.layout.accessories[0][:2] == (upper, "stone_stop")
    page.locator("#undo").tap()
    page.wait_for_function("S.snapshot.layout.accessories.length === 0 && !apiBusy")
    assert session.snapshot() == initial
    assert not errors


@pytest.mark.parametrize("reverse", [False, True])
def test_stone_removal_can_explicitly_choose_lower_without_removing_upper(editor, reverse):
    from playwright.sync_api import expect

    page, session, url, errors = editor
    lower, upper = crossing(session, reverse, stones=True)
    load(page, url)
    initial = session.snapshot()
    page.locator("#delete-tool").tap()
    tap_world(page)
    picker = page.locator("#overlap-picker")
    expect(picker).to_be_visible()
    assert page.evaluate("selectedPiece") == upper
    picker.locator("select").select_option(index=1)
    assert page.evaluate("selectedPiece") == lower
    picker.get_by_role("button", name="Remove selected stone", exact=True).tap()
    page.wait_for_function("S.snapshot.layout.accessories.length === 1 && !apiBusy")
    assert session.layout.accessories[0][:2] == (upper, "stone_direction")
    page.locator("#undo").tap()
    page.wait_for_function("S.snapshot.layout.accessories.length === 2 && !apiBusy")
    assert session.snapshot() == initial
    assert not errors


def test_later_published_page_survives_route_analysis_then_applies_and_undoes(editor):
    from playwright.sync_api import expect

    page, session, url, errors = editor
    load(page, url)
    page.locator("#unlimited").check()
    page.wait_for_function("S.inventory.unlimited && !apiBusy")
    page.locator("#reversing").uncheck()
    fixture = Path(__file__).parents[1] / "fixtures/bridge-gap.json"
    page.locator("#importfile").set_input_files(str(fixture))
    expect(page.locator("#status")).to_contain_text("imported 59 pieces.")
    original = page.evaluate("S.snapshot")
    page.locator("#solve").tap()
    expect(page.locator("#status")).to_contain_text("8 alternative(s) found", timeout=90000)
    page.locator("#find-more").tap()
    expect(page.locator("#status")).to_contain_text("16 alternative(s) found", timeout=90000)
    page.locator("#candidate-next").tap()
    expect(page.locator("#candidate-page")).to_have_text("Page 2 / 2")
    assert page.evaluate("S.candidates === interactiveJob.candidates")
    for label in ("Test train", "Find and analyse train routes"):
        summary = page.locator("summary", has_text=re.compile("^" + re.escape(label) + "$"))
        if summary.locator("..").get_attribute("open") is None:
            summary.tap()
    page.locator("#train-start").select_option("[0,0]")
    page.locator("#route-best").tap()
    expect(page.locator("#route-report")).to_contain_text("64 / 64 runs", timeout=90000)
    page.evaluate("renderCandidates()")
    expect(page.locator(".cand")).to_have_count(8)
    first = page.locator(".cand").first
    assert first.get_attribute("data-candidate-index") == "8"
    first.get_by_role("button", name="Preview", exact=True).tap()
    expect(first.get_by_role("button", name="Apply")).to_be_enabled()
    first.get_by_role("button", name="Apply").tap()
    editor_tests.wait_count(page, 83)
    assert session.layout.is_closed and not session.layout.joint_issues()
    page.locator("#undo").tap()
    editor_tests.wait_count(page, 59)
    assert session.snapshot() == original
    assert not errors
