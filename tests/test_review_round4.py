"""Decimal-tie geometry, complete length, and bounded classification regressions."""

from __future__ import annotations

import importlib
import json
import math
import os
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

import pytest
from click.testing import CliRunner

from duplotrain import (
    ORIGIN,
    Alg,
    ClassificationLimitError,
    Layout,
    NetworkConfig,
    Placement,
    Pose,
    SolverConfig,
    build_chain,
    classify,
    default_catalog,
    enumerate_networks,
    layout_to_dict,
    parse_piece,
    solve,
)
from duplotrain.cli import main
from duplotrain.explore import congruence_key
from duplotrain.pieces import Arc, Straight
from duplotrain.solver import _solution_overlaps
from duplotrain.symmetry import placement_key


def _track(segments, *, start=ORIGIN):
    piece = parse_piece({"id": "custom", "width": 64, "paths": [{"segments": segments}]})
    return build_chain([(piece, 0, 1)], start=start)


def _transform(layout, heading, mirror=False):
    placements = []
    for placement in layout:
        piece, frame = placement.piece, placement.frame
        if mirror:
            paths = tuple(replace(
                path, start=path.start.mirrored(),
                segments=tuple(replace(s, degrees=-s.degrees) if type(s) is Arc else s
                               for s in path.segments),
            ) for path in piece.paths)
            ports = tuple(replace(port, pose=port.pose.mirrored()) for port in piece.ports)
            piece = replace(piece, paths=paths, ports=ports)
            frame = frame.mirrored()
        frame = frame.rotated_about_origin(heading)
        frame = Pose(frame.x + Alg(431, 0, 2), frame.y - 781, frame.z + 19, frame.heading)
        placements.append(Placement(piece, frame))
    return Layout(tuple(placements), layout.links, layout.accessories)


@pytest.mark.parametrize("run", ["2559/10", "256", "25599/100", "255999/1000"])
@pytest.mark.parametrize("kind", ["straight", "ramp", "arc", "mixed"])
def test_decimal_ties_keep_one_curve_key_under_all_rigid_motions(run, kind):
    straight = {"type": "straight", "run": run}
    arc = {"type": "arc", "radius": run, "degrees": -105}
    if kind == "straight":
        segments = [straight]
    elif kind == "ramp":
        segments = [{"type": "ramp", "run": run, "rise": "279/10"}]
    elif kind == "arc":
        segments = [arc]
    else:
        segments = [straight, arc, {"type": "ramp", "run": 96, "rise": 19}]
    layout = _track(segments)
    expected = congruence_key(layout)
    for heading in range(24):
        for mirror in (False, True):
            assert congruence_key(_transform(layout, heading, mirror)) == expected


@pytest.mark.parametrize("spacing,decimals", [(7.0, 0), (8.0, 1), (11.3, 3), (6.7, -1)])
def test_uneven_splits_reversals_and_duplicates_keep_decimal_tie_key(spacing, decimals):
    whole = _track([{"type": "straight", "run": "2559/10"}])
    pieces = [parse_piece({"id": f"part{i}", "paths": [{"segments": [
        {"type": "straight", "run": run},
    ]}]}) for i, run in enumerate(["73/3", "6947/30"])]
    split = build_chain([(pieces[0], 0, 1), (pieces[1], 1, 0)])
    duplicate = Layout(tuple(reversed(split.placements)) + split.placements)
    expected = congruence_key(whole, spacing, decimals)
    for heading in range(24):
        for mirror in (False, True):
            assert congruence_key(_transform(duplicate, heading, mirror), spacing, decimals) == (
                expected
            )


def _oval_catalog():
    return {
        "long": parse_piece({"id": "long", "width": 64, "paths": [{"segments": [
            {"type": "straight", "run": "2559/10"},
        ]}]}),
        "bend": parse_piece({"id": "bend", "width": 64, "paths": [{"segments": [
            {"type": "arc", "radius": 256, "degrees": 60},
        ]}]}),
    }


def _exact_piece_key(layout):
    """Independent whole-piece orbit oracle; only for equal piece inventories."""
    ports = [p.port_pose(i) for p in layout for i in range(len(p.piece.ports))]
    centre = tuple(sum((getattr(p, axis) for p in ports), Alg(0)) / len(ports)
                   for axis in ("x", "y", "z"))
    candidates = []
    for heading in range(24):
        for mirror in (False, True):
            items = []
            for placement in layout:
                f = placement.frame
                centred = Pose(f.x - centre[0], f.y - centre[1], f.z - centre[2], f.heading)
                items.append((placement.piece.id, placement_key(
                    placement.piece, centred.rotated_about_origin(heading), mirror)))
            candidates.append(tuple(sorted(items)))
    return min(candidates)


def test_networks_do_not_count_the_decimal_tie_oval_twice():
    inventory, catalog = {"long": 2, "bend": 6}, _oval_catalog()
    result = enumerate_networks(inventory, catalog, NetworkConfig(
        use_all_pieces=True, max_pieces=8, max_results=100, max_nodes=100_000,
    ))
    reference = solve(inventory, catalog, SolverConfig(use_all_pieces=True, max_results=100))
    assert result.stats.complete and reference.stats.complete
    assert len(result.layouts) == len(reference.solutions) == 1
    assert _exact_piece_key(result.layouts[0]) == _exact_piece_key(reference.solutions[0].layout)
    assert result.layouts[0].is_closed and not result.layouts[0].joint_issues()
    assert not _solution_overlaps(result.layouts[0], 0, 120, 8)


@pytest.mark.parametrize("pid", list(default_catalog()))
def test_total_length_includes_every_stock_route(pid):
    piece = default_catalog()[pid]
    layout, _ = Layout().with_piece(piece, ORIGIN)
    assert layout.track_length() == pytest.approx(sum(path.length() for path in piece.paths))


def test_cli_check_reports_the_complete_crossing_length(tmp_path):
    layout, _ = Layout().with_piece(default_catalog()["crossing"], ORIGIN)
    path = tmp_path / "crossing.json"
    path.write_text(json.dumps(layout_to_dict(layout)))
    result = CliRunner().invoke(main, ["check", str(path)])
    assert "26 cm of track" in result.output
    assert "13 cm of track" not in result.output


@pytest.mark.parametrize("kind", ["straight", "ramp", "arc"])
def test_length_unions_shared_paths_and_uneven_splits(kind):
    if kind == "arc":
        whole = [{"type": "arc", "radius": 128, "degrees": 90}]
        split = [{"type": "arc", "radius": 128, "degrees": d} for d in (15, 30, 45)]
        expected = 64 * math.pi
    elif kind == "ramp":
        whole = [{"type": "ramp", "run": 256, "rise": 28}]
        split = [{"type": "ramp", "run": run, "rise": rise}
                 for run, rise in ((67, "469/64"), (189, "1323/64"))]
        expected = math.hypot(256, 28)
    else:
        whole = [{"type": "straight", "run": "2559/10"}]
        split = [{"type": "straight", "run": run} for run in ("73/3", "6947/30")]
        expected = 255.9
    piece = parse_piece({"id": "duplicate", "paths": [
        {"segments": whole}, {"segments": split},
    ]})
    layout, _ = Layout().with_piece(piece, ORIGIN)
    for heading in range(24):
        for mirror in (False, True):
            assert _transform(layout, heading, mirror).track_length() == pytest.approx(expected)


def test_length_includes_both_arms_but_counts_a_shared_prefix_once():
    piece = parse_piece({"id": "branch", "paths": [
        {"segments": [{"type": "straight", "run": 64},
                      {"type": "arc", "radius": 128, "degrees": d}]}
        for d in (30, -30)
    ]})
    layout, _ = Layout().with_piece(piece, ORIGIN)
    assert layout.track_length() == pytest.approx(64 + 128 * math.pi / 3)


def test_length_unions_partial_overlaps_but_not_gaps_or_parallel_layers():
    first = _track([{"type": "straight", "run": 100}])
    second = _track([{"type": "straight", "run": 100}], start=Pose.make(60, 0, 0))
    gap = _track([{"type": "straight", "run": 100}], start=Pose.make(101, 0, 0))
    raised = _track([{"type": "straight", "run": 100}], start=Pose.make(0, 0, 1))
    assert Layout(first.placements + second.placements).track_length() == 160
    assert Layout(first.placements + gap.placements).track_length() == 200
    assert Layout(first.placements + raised.placements).track_length() == 200
    assert Layout(first.placements * 2).track_length() == 100
    assert Layout().track_length() == 0


@pytest.mark.parametrize("turn", [-720, -360, 360, 720])
def test_multi_turn_arc_length_counts_its_curve_once(turn):
    layout = _track([{"type": "arc", "radius": 128, "degrees": turn}])
    assert layout.track_length() == pytest.approx(256 * math.pi)


def test_unknown_segment_uses_declared_length_not_its_endpoint_distance():
    class Measured(Straight):
        def length(self):
            return 177.0

    piece = default_catalog()["straight"]
    path = replace(piece.paths[0], segments=(Measured(Alg(128)),))
    custom = replace(piece, paths=(path,))
    assert build_chain([(custom, 0, 1)]).track_length() == 177.0


def _switch_chain():
    switch = default_catalog()["switch"]
    return build_chain([(switch, 0, 1 if i % 2 == 0 else 2) for i in range(25)])


def test_existing_classifier_budget_rejects_connected_large_layout_without_simulation(monkeypatch):
    module = importlib.import_module("duplotrain.drive")
    calls = []
    monkeypatch.setattr(module, "drive", lambda *args, **kwargs: calls.append(args))
    with pytest.raises(ClassificationLimitError, match="max_runs"):
        classify(_switch_chain())
    assert calls == []


@pytest.mark.skipif(sys.platform != "linux", reason="isolated Linux memory-budget probe")
def test_unbounded_classifier_reaches_first_simulation_with_bounded_memory():
    # Stop on the first call to drive: exercise lazy allocation without running an
    # exponential search. The default-budget case above must fail informatively.
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
