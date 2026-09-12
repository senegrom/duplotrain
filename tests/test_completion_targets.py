"""Longer lookahead, projected geometry, and present/future reversing targets."""

from dataclasses import replace

import pytest

from duplotrain import (
    ORIGIN,
    Layout,
    Pose,
    SolverConfig,
    build_chain,
    default_catalog,
    parse_piece,
    solve,
)
from duplotrain.solver import (
    _compile_lattice,
    _FieldEngine,
    _flat,
    _moves_for,
    _pose_to_lattice,
    _solution_overlaps,
)


def signatures(result):
    return {(s.signature, s.kind, s.gap) for s in result.solutions}


def assert_budget(result, config):
    assert result.stats.completion_work <= min(4096, config.max_nodes // 8)
    assert (result.stats.completion_states + result.stats.completion_height_states
            <= result.stats.completion_work + 2)


def test_six_step_lookahead_reduces_long_gap_work_again():
    catalog = default_catalog()
    base = build_chain([(catalog["straight"], 0, 1)] * 4 + [(catalog["curve"], 0, 1)] * 2)
    inventory = {"curve": 14, "straight": 8}
    cfg = SolverConfig(min_pieces=0, max_pieces=20, max_results=8, max_nodes=25_000)
    previous = solve(inventory, catalog, replace(cfg, completion_lookahead=4), base=base)
    improved = solve(inventory, catalog, cfg, base=base)
    assert len(improved.solutions) == 8
    assert signatures(improved) == signatures(previous)
    assert improved.stats.nodes < previous.stats.nodes // 2
    assert_budget(improved, cfg)


@pytest.mark.parametrize("engine", ["lattice", "field"])
@pytest.mark.parametrize("branch", [1, 2])
def test_retargeting_preserves_every_reversing_completion(engine, branch):
    catalog = default_catalog()
    base = build_chain([(catalog["switch"], 0, branch)],
                       start=Pose.make(x=317, y=-290, z=77, heading=4))
    cfg = SolverConfig(min_pieces=0, max_results=1000, max_nodes=100_000,
                       engine=engine, reversing_loops=True)
    options = dict(base=base, grow_from=(0, branch), close_onto=(0, 0))
    reference = solve({"curve": 12}, catalog, replace(cfg, completion_lookahead=0), **options)
    improved = solve({"curve": 12}, catalog, cfg, **options)
    assert reference.stats.complete and improved.stats.complete
    assert signatures(improved) == signatures(reference)
    assert {s.kind for s in improved.solutions} == {"loop", "reversing"}
    assert improved.stats.nodes < reference.stats.nodes // 3
    assert_budget(improved, cfg)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_future_switch_can_close_even_when_original_target_is_unreachable(engine):
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)])
    base, far = base.with_piece(catalog["straight"], Pose.make(x=100_000))
    # A known teardrop closes into a junction that is not yet part of the base.
    witness, switch = base.attach(catalog["switch"], 1, (0, 1))
    cursor = (switch, 0)
    for _ in range(11):
        witness, index = witness.attach(catalog["curve"], 0, cursor)
        cursor = (index, 1)
    witness = witness.join(cursor, (switch, 2))
    assert not witness.joint_issues()
    assert not _solution_overlaps(witness, len(base), 120, 8)

    cfg = SolverConfig(min_pieces=0, engine=engine, max_nodes=100_000,
                       max_results=1000, reversing_loops=True)
    result = solve({"curve": 11, "switch": 1}, catalog, cfg,
                   base=base, grow_from=(0, 1), close_onto=(far, 0))
    assert result.stats.complete
    assert any(s.layout == witness for s in result.solutions)
    assert all(s.kind == "reversing" and s.exact for s in result.solutions)
    assert_budget(result, cfg)


def test_broad_bridge_inventory_closes_within_the_existing_node_budget():
    catalog = default_catalog()
    base = build_chain([(catalog["curve"], 0, 1)] * 6 + [(catalog["ramp"], 0, 1)])
    inventory = {"curve": 18, "straight": 8, "ramp": 1, "span": 2, "switch": 2,
                 "crossing": 1, "slope": 2, "level_crossing": 2}
    cfg = SolverConfig(min_pieces=0, max_pieces=20, max_results=8, max_nodes=25_000,
                       reversing_loops=True)
    result = solve(inventory, catalog, cfg, base=base)
    assert len(result.solutions) == 8 and not result.stats.aborted
    assert result.stats.nodes < 5000
    assert result.stats.stop_reason == "result_limit" and not result.stats.complete
    assert all(s.exact and not s.layout.joint_issues() for s in result.solutions)
    assert all(not _solution_overlaps(s.layout, len(base), 120, 8) for s in result.solutions)
    assert_budget(result, cfg)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_projected_membership_cannot_emit_a_false_height_and_position_match(engine):
    catalog = default_catalog()
    catalog["short_up"] = parse_piece({"id": "short_up", "paths": [{"segments": [
        {"type": "ramp", "run": 128, "rise": 1},
    ]}]})
    catalog["long_flat"] = parse_piece({"id": "long_flat", "paths": [{"segments": [
        {"type": "straight", "run": 256},
    ]}]})
    base, left = Layout().with_piece(catalog["straight"], ORIGIN)
    base, right = base.with_piece(catalog["straight"], Pose.make(x=256))
    # The planar projection can span 128 mm; the height projection can stay level.
    # No actual spare piece can do both, and the final exact geometry must reject it.
    cfg = SolverConfig(min_pieces=0, engine=engine)
    result = solve({"short_up": 1, "long_flat": 1}, catalog, cfg,
                   base=base, grow_from=(left, 1), close_onto=(right, 0))
    assert result.stats.complete and not result.solutions
    assert_budget(result, cfg)


@pytest.mark.parametrize("engine", ["lattice", "field"])
def test_retarget_transform_agrees_with_pose_composition(engine):
    catalog = default_catalog()
    moves = {pid: _moves_for(piece) for pid, piece in catalog.items()}
    headings = range(0, 24, 2 if engine == "lattice" else 1)
    anchor = Pose.make(x=321, y=-47, z=83, heading=4)
    if engine == "lattice":
        eng = _compile_lattice(anchor, anchor, catalog, moves)

        def convert(pose):
            return _flat(_pose_to_lattice(pose))
    else:
        eng = _FieldEngine(anchor, anchor, catalog, moves)

        def convert(pose):
            return pose

    delta = Pose.make(x=128, y=-64, z=-23, heading=8)
    expected = anchor.then(delta.x, delta.y, delta.z, delta.heading)
    for heading in headings:
        target = Pose.make(x=-73, y=911, z=152, heading=heading)
        cursor = target.then(delta.x, delta.y, delta.z, delta.heading)
        assert eng.retarget(convert(cursor), convert(target)) == convert(expected)
