"""The arc shortcut matches exact suffixes without multiplying transform work."""

import json
from collections import Counter
from pathlib import Path

import pytest

from duplotrain import Layout, Pose, build_chain, default_catalog
from duplotrain.gui import Session
from duplotrain.layout import layout_from_dict
from duplotrain.solver import _solution_overlaps


@pytest.mark.parametrize("heading", [0, 1, 5, 23])
@pytest.mark.parametrize("climbing", [False, True])
def test_suffix_lookup_keeps_exact_rotated_and_elevated_closures(heading, climbing):
    catalog = default_catalog()
    chain = ["curve"] * 6 + (["ramp"] if climbing else [])
    base = build_chain([(catalog[pid], 0, 1) for pid in chain],
                       start=Pose.make(x=317, y=-123, heading=heading))
    stock = {"curve": 6, "straight": 4, "ramp": int(climbing), "span": 2 * int(climbing)}
    owned = dict(Counter(base.piece_counts) + Counter(stock))
    session = Session(history=[base], inventory=owned)
    grow, close = base.connectable_ends()[-1], base.connectable_ends()[0]
    found = session._arc_closures(grow, close, 8, 26)
    assert found
    for candidate in found:
        assert candidate.layout.is_closed and not candidate.layout.joint_issues()
        assert candidate.layout.placements[:len(base)] == base.placements
        assert not _solution_overlaps(candidate.layout, 0, 120, 8)
        assert all(n <= owned.get(pid, 0) for pid, n in candidate.layout.piece_counts.items())


def test_duplicate_straight_bridge_templates_do_not_fill_result_cards():
    catalog = default_catalog()
    layout, a = Layout().with_piece(catalog["straight"], Pose.make())
    layout, b = layout.with_piece(catalog["straight"], Pose.make(x=1152))
    session = Session(history=[layout], inventory={"straight": 2, "ramp": 2, "span": 2})
    found = session._arc_closures((a, 1), (b, 0), 50, 4)
    assert found
    keys = [candidate.layout.placements[len(layout):] for candidate in found]
    assert len(keys) == len(set(keys))


def test_reported_gap_does_not_rebuild_every_suffix_for_every_prefix(monkeypatch):
    data = json.loads((Path(__file__).parent / "fixtures/bridge-gap.json").read_text())
    layout = layout_from_dict(data, default_catalog())
    session = Session(history=[layout], unlimited=True)
    calls = 0
    original = Pose.then

    def counted(self, *args):
        nonlocal calls
        calls += 1
        return original(self, *args)

    monkeypatch.setattr(Pose, "then", counted)
    assert not session._arc_closures((25, 0), (23, 1), 8, 26)
    # The earlier suffix lookup still made over 4,000 transforms. Composed runs
    # reduce this to about 1,440; use an operation ceiling, not wall-clock timing.
    assert calls < 2_000


@pytest.mark.parametrize("straights", [0, 1, 2, 4])
def test_composed_arc_runs_preserve_finite_stock_order(straights):
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6)
    session = Session(history=[base], inventory={"curve": 12, "straight": straights})
    found = session._arc_closures((5, 1), (0, 0), 50, 26)
    assert [len(s.layout) for s in found] == [12 + 2 * i for i in range(straights // 2 + 1)]
    for candidate in found:
        assert not candidate.layout.joint_issues()
        assert not _solution_overlaps(candidate.layout, 0, 120, 8)
