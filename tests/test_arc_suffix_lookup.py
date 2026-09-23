"""The arc shortcut matches exact suffixes without multiplying transform work."""

import json
from collections import Counter
from pathlib import Path

import pytest

import duplotrain.editor as editor
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
    # The lattice path uses integer tuples; count the exact path's transforms.
    monkeypatch.setattr(editor._LatticeArcGeometry, "compile", staticmethod(lambda *args: None))
    calls = 0
    original = Pose.then

    def counted(self, *args):
        nonlocal calls
        calls += 1
        return original(self, *args)

    monkeypatch.setattr(Pose, "then", counted)
    assert not session._arc_closures((25, 0), (23, 1), 8, 26)
    # One walk back per suffix and composed runs take about 1,440 transforms;
    # rebuilding suffixes per prefix takes several times that. Count, never time.
    assert 0 < calls < 2_000


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


def test_lattice_oracle_geometry_matches_the_exact_geometry():
    from fractions import Fraction

    import duplotrain.editor as editor
    from duplotrain import Layout, Pose, build_chain
    from duplotrain.editor import Session, _ExactArcGeometry, _LatticeArcGeometry

    catalog = default_catalog()
    bases = [
        build_chain([(catalog["curve"], 0, 1)] * 6),
        build_chain([(catalog["curve"], 0, 1)] * 2),
        build_chain([(catalog["straight"], 0, 1)] * 2 + [(catalog["curve"], 0, 1)] * 4),
        build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["ramp"], 0, 1)]),
        build_chain([(catalog["ramp"], 0, 1), (catalog["span"], 0, 1)]),
    ]
    first = build_chain([(catalog["curve"], 0, 1)] * 3)
    second = build_chain([(catalog["curve"], 0, 1)] * 3,
                         start=first.pose_of((2, 1)).then(128, 0, 0, 0))
    bases.append(Layout(first.placements + second.placements, {**first.links, **{
        (i + 3, p): (j + 3, q) for (i, p), (j, q) in second.links.items()}}))
    compiled = []
    for base in bases:
        ends = base.connectable_ends()
        for grow, close in ((ends[-1], ends[0]), (ends[0], ends[-1])):
            for unlimited in (True, False):
                session = Session(history=[base], unlimited=unlimited)
                start, target = base.pose_of(grow), base.pose_of(close)
                lattice = _LatticeArcGeometry.compile(catalog, start, target)
                assert lattice is not None
                compiled.append(lattice)
                fast = session._arc_closures(grow, close, 8, 26)
                with pytest.MonkeyPatch.context() as mp:
                    mp.setattr(editor._LatticeArcGeometry, "compile",
                               classmethod(lambda cls, *a: None))
                    exact = session._arc_closures(grow, close, 8, 26)
                assert [s.layout for s in fast] == [s.layout for s in exact]
                assert [s.signature for s in fast] == [s.signature for s in exact]
    # The two geometries agree step by step, not only on the candidates found.
    exact = _ExactArcGeometry(catalog, Pose.make(), Pose.make(x=128, heading=6))
    lattice = compiled[0]
    for pid, entry, exit_port in _LatticeArcGeometry.STEPS:
        for count in (1, 2, 5):
            pose = exact.run(pid, entry, exit_port, count)(Pose.make(x=64, y=-128, heading=4))
            fast = lattice.run(pid, entry, exit_port, count)(_LatticeArcGeometry.compile(
                catalog, Pose.make(x=64, y=-128, heading=4), Pose.make()).start)
            assert editor._flat(editor._pose_to_lattice(pose)) == fast
    # An off-lattice end (a third of a millimetre, or a 15-degree heading)
    # falls back to the exact geometry.
    assert _LatticeArcGeometry.compile(catalog, Pose.make(x=Fraction(1, 3)), Pose.make()) is None
    assert _LatticeArcGeometry.compile(catalog, Pose.make(heading=1), Pose.make()) is None
