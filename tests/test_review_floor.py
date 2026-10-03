"""Whole-piece completion floors, including hidden and unused-path minima."""
from fractions import Fraction

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.editor import Session
from duplotrain.editor_search import SearchJob, search_options, valid_extension
from duplotrain.exact import Alg
from duplotrain.geometry import Pose
from duplotrain.layout import Layout, Placement
from duplotrain.pieces import parse_piece
from duplotrain.solver import SolverConfig, solve


def problem(rise, height=0):
    catalog = default_catalog()
    catalog['probe'] = parse_piece({'id': 'probe', 'width': 40, 'paths': [{'segments': [
        {'type': 'ramp', 'run': 128, 'rise': str(rise)},
        {'type': 'ramp', 'run': 128, 'rise': str(-rise)},
    ]}]})
    base = Layout([Placement(catalog['straight'], Pose.make(-128, 0, height)),
                   Placement(catalog['straight'], Pose.make(256, 0, height))])
    return catalog, base


@pytest.mark.parametrize('engine', ['lattice', 'field'])
@pytest.mark.parametrize('reverse', [False, True])
@pytest.mark.parametrize('height', [0, -80, 80])
@pytest.mark.parametrize('rise', [-40, Fraction(-1, 10**12), 40])
def test_hidden_dip_rejected_and_hump_accepted(engine, reverse, height, rise):
    catalog, base = problem(rise, height)
    ends = [(0, 1), (1, 0)][::(-1 if reverse else 1)]
    result = solve({'probe': 1}, catalog,
                   SolverConfig(min_pieces=1, max_pieces=1, max_results=8,
                                max_nodes=10000, engine=engine),
                   base=base, grow_from=ends[0], close_onto=ends[1])
    assert len(result.solutions) == int(rise > 0)
    assert catalog['probe'].minimum_z == Alg(min(0, rise))
    for candidate in result.solutions:
        assert not candidate.layout.joint_issues()
        assert candidate.layout.placements[:len(base)] == base.placements


@pytest.mark.parametrize('engine', ['lattice', 'field'])
def test_unused_path_must_also_stay_above_floor(engine):
    catalog, base = problem(40)
    catalog['probe'] = parse_piece({'id': 'probe', 'width': 40, 'paths': [
        {'segments': [{'type': 'straight', 'run': 256}]},
        {'start': {'y': 200, 'z': -40}, 'segments': [{'type': 'straight', 'run': 256}]},
    ]})
    assert catalog['probe'].minimum_z == Alg(-40)
    result = solve({'probe': 1}, catalog,
                   SolverConfig(min_pieces=1, max_pieces=1, max_nodes=10000, engine=engine),
                   base=base, grow_from=(0, 1), close_onto=(1, 0))
    # Entering the lower route raises the whole piece and is legitimate; entering
    # its upper route would put the unused lower line below the floor.
    assert len(result.solutions) == 2
    assert all(sol.steps[0].entry in (2, 3) for sol in result.solutions)
    assert all((sol.layout.placements[-1].frame.z + catalog['probe'].minimum_z).sign() >= 0
               for sol in result.solutions)


@pytest.mark.parametrize('all_gaps', [False, True])
@pytest.mark.parametrize('rise', [-40, 40])
def test_editor_acceptance_and_apply_undo(all_gaps, rise):
    catalog, base = problem(rise)
    # Cap the outward ends, leaving only the gap under test.
    for end in [(0, 0), (1, 1)]:
        base, _ = base.attach(catalog['buffer'], 0, end)
    inventory = dict(base.piece_counts, probe=1)
    session = Session(catalog=catalog, history=[base], inventory=inventory)
    before = session.snapshot()
    job = SearchJob(session, {'grow': [0, 1], 'close': [1, 0],
                              'max_pieces': 1, 'all_gaps': all_gaps})
    for _ in range(2000):
        if job.status != 'running':
            break
        job.tick()
    assert job.status != 'running'
    assert len(job.solutions) == int(rise > 0)
    assert session.snapshot() == before
    if job.solutions:
        job.publish(session)
        session.apply_candidate(0, session.revision)
        assert session.layout.is_closed and not session.layout.joint_issues()
        session.undo()
        assert session.snapshot() == before
    job.close()


def test_final_extension_guard_rejects_hidden_dip_independently():
    catalog, base = problem(-40)
    # A fresh loop has no absolute floor. Build a candidate without solver pruning
    # to test the independent editor guard rather than trust that pruning.
    from duplotrain.solver import Solution

    layout, index = base.attach(catalog['probe'], 0, (0, 1))
    layout = layout.join((index, 1), (1, 0))
    candidate = Solution(layout=layout, steps=(), exact=True, gap=0, signature=(), open_stubs=0)
    assert not valid_extension(base, candidate, {'probe': 1}, 1,
                               search_options(None, catalog), floor=base.floor(catalog.values()))
