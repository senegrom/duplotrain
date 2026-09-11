"""Anchored completions must retain exact witnesses and eligible base transits."""

import pytest

from duplotrain import ORIGIN, Layout, Pose, SolverConfig, default_catalog, parse_piece, solve
from duplotrain.explore import congruence_key
from duplotrain.gui import Session
from duplotrain.solver import _solution_overlaps


def reversing_base_and_witnesses():
    """Connected, stock-piece base with two different four-curve completions."""
    catalog = default_catalog()
    base, switch = Layout().with_piece(catalog["switch"], Pose(512, 0, 0, 0))
    end = (switch, 1)
    # A large upper lobe ends at (0, 0), facing east. Its asymmetry distinguishes
    # inward and outward four-curve completions even up to global congruence.
    for pid in ["curve"] * 5 + ["straight"] * 5 + ["curve"] * 6 + ["straight"]:
        base, index = base.attach(catalog[pid], 0, end)
        end = (index, 1)
    grow, close = end, (switch, 2)
    assert not base.joint_issues()
    assert not _solution_overlaps(base, 0, 120.0, 8.0)

    witnesses = []
    # L,R,R,L and R,L,L,R both end exactly at the switch stem (512, 0).
    for entries in ((0, 1, 1, 0), (1, 0, 0, 1)):
        layout, cursor = base, grow
        for entry in entries:
            layout, index = layout.attach(catalog["curve"], entry, cursor)
            cursor = (index, 1 - entry)
        layout = layout.join(cursor, (switch, 0))
        assert not layout.joint_issues()
        assert not _solution_overlaps(layout, 0, 120.0, 8.0)
        witnesses.append(layout)
    assert congruence_key(witnesses[0]) != congruence_key(witnesses[1])
    return catalog, base, grow, close, witnesses


@pytest.mark.parametrize("engine", ["field", "lattice"])
def test_reversing_completion_keeps_both_distinct_anchored_witnesses(engine):
    catalog, base, grow, close, witnesses = reversing_base_and_witnesses()
    result = solve(
        {"curve": 4}, catalog,
        SolverConfig(
            min_pieces=4, use_all_pieces=True, max_nodes=100_000,
            max_results=100, reversing_loops=True, engine=engine,
        ),
        base=base, grow_from=grow, close_onto=close,
    )
    assert result.stats.complete and result.stats.stop_reason == "exhausted"
    found = {congruence_key(solution.layout) for solution in result.solutions}
    missing = sum(congruence_key(witness) not in found for witness in witnesses)
    assert missing == 0, (
        f"{engine}: {result.stats.closures_found} closures found, but "
        f"{len(result.solutions)} returned; {missing} exact, collision-free, "
        "non-congruent anchored witness was incorrectly deduplicated"
    )


@pytest.mark.parametrize("reverse", [False, True])
def test_editor_height_bound_includes_transitable_preplaced_junctions(reverse):
    catalog = default_catalog()
    catalog["ramp_switch"] = parse_piece({
        "id": "ramp_switch", "width": 64,
        "paths": [
            {"segments": [{"type": "ramp", "run": 128, "rise": 64}]},
            {"segments": [{"type": "arc", "radius": 256, "degrees": 30}]},
        ],
    })
    base, junction = Layout().with_piece(catalog["ramp_switch"], ORIGIN)
    base, left = base.attach(catalog["straight"], 1, (junction, 0))
    base, right = base.attach(catalog["straight"], 0, (junction, 1))
    # Imported/prepositioned pieces: retain exact frames, leaving the joints open.
    # The core solver explicitly supports preplaced-junction-only completion.
    base = Layout(base.placements, {})
    grow, close = (left, 1), (right, 0)
    if reverse:
        grow, close = close, grow
    witness = base.join((left, 1), (junction, 0)).join((junction, 1), (right, 0))
    assert not witness.joint_issues()
    assert not _solution_overlaps(witness, 0, 120.0, 8.0)
    for engine in ("field", "lattice"):
        result = solve(
            {}, catalog, SolverConfig(min_pieces=0, max_pieces=1, engine=engine),
            base=base, grow_from=grow, close_onto=close,
        )
        assert result.stats.complete and len(result.solutions) == 1
        assert result.solutions[0].exact

    session = Session(catalog=catalog, inventory=dict(base.piece_counts), history=[base])
    result = session.solve_gap(grow, close, slop=0.0, max_results=10, max_pieces=1)
    assert result["found"] == 1, (
        "Both core engines found an exact zero-new-piece completion, but the "
        f"editor rejected it: {result}"
    )


@pytest.mark.parametrize("cyclic", [False, True])
def test_reversing_signature_reflection_only_applies_to_fresh_layouts(cyclic):
    from duplotrain.solver import (
        _canonical_signature,
        _canonical_traversals,
        _mirror_ports,
        _mirror_traversals,
        _Place,
    )

    catalog = default_catalog()
    left = [_Place("switch", 0, 1), _Place("curve", 0, 1)]
    right = [_Place("switch", 0, 2), _Place("curve", 1, 0)]
    options = {
        "cyclic": cyclic,
        "canon_for": {pid: _canonical_traversals(p) for pid, p in catalog.items()},
        "mirror_for": {pid: _mirror_traversals(p) for pid, p in catalog.items()},
        "port_mirror_for": {pid: _mirror_ports(p) for pid, p in catalog.items()},
    }
    left_key = _canonical_signature(left, closing_stub=(0, 2), **options)
    right_key = _canonical_signature(right, closing_stub=(0, 1), **options)
    assert (left_key == right_key) is cyclic


def test_anchored_signatures_preserve_closing_port_and_base_placement_identity():
    from duplotrain.solver import _canonical_signature, _Place, _Transit

    options = {"canon_for": {}, "base_pids": ["switch", "switch"], "cyclic": False}
    steps = [_Place("curve", 0, 1)]
    keys = {
        _canonical_signature(steps, closing_stub=stub, **options)
        for stub in [(0, 0), (0, 1), (1, 0), (1, 1)]
    }
    assert len(keys) == 4
    assert _canonical_signature([_Transit(0, 0, 1)], **options) != _canonical_signature(
        [_Transit(1, 0, 1)], **options,
    )
