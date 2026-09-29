"""Paged publication and per-analysis immutable drive preparation."""
import json
from dataclasses import replace
from pathlib import Path

import pytest

from duplotrain.catalog import default_catalog
from duplotrain.drive import (_all_starts, _prepare_drive, _tongue_assignments,
                               classify, drive, DriveLimitError)
from duplotrain.editor import PREVIEW_FORMAT, Session, dispatch_session
from duplotrain.editor_routes import RouteJob
from duplotrain.editor_search import SearchJob
from duplotrain.layout import layout_from_dict

FIXTURES = Path(__file__).parent / 'fixtures'


def session_for(name):
    catalog = default_catalog()
    layout = layout_from_dict(json.loads((FIXTURES / name).read_text()), catalog)
    return Session(catalog=catalog, history=[layout], unlimited=True)


def finish(job):
    for _ in range(10000):
        if job.status != 'running':
            return
        job.tick()
    pytest.fail('bounded fixture did not finish')


@pytest.mark.parametrize('page_only', [False, True])
def test_publication_only_samples_requested_collection(monkeypatch, page_only):
    session = session_for('bridge-gap.json')
    before = session.snapshot()
    job = SearchJob(session, {'max_results': 16})
    session._interactive_job = job
    finish(job)
    assert len(job.solutions) == 16
    calls, original = [], session._candidate_json

    def record(index, *args, **kwargs):
        calls.append(index)
        return original(index, *args, **kwargs)

    monkeypatch.setattr(session, '_candidate_json', record)
    response = dispatch_session(session, '/api/search/publish', {
        'job_id': job.id, 'revision': session.revision, 'preview_format': PREVIEW_FORMAT,
        'page_only': page_only, 'page': 1, 'sort': 'pieces',
    })
    assert len(calls) == (8 if page_only else 24)
    assert len(response['candidates']) == (0 if page_only else 16)
    shown = response['search_job']['candidates']
    assert len(shown) == 8 and len(session.candidates) == 16
    assert session.snapshot() == before
    assert all(c['revision'] == session.revision for c in shown)
    assert all(c['preview']['base_revision'] == session.revision for c in shown)
    # A later-page index, not its position on the screen, selects the exact layout.
    index = shown[-1]['index']
    expected = session.candidates[index].layout
    session.apply_candidate(index, session.revision)
    assert session.layout == expected
    session.undo()
    assert session.snapshot() == before


@pytest.mark.parametrize('value', [None, 1, 'true', []])
def test_bad_page_option_cannot_publish_or_change_revision(value):
    session = session_for('bridge-gap.json')
    job = SearchJob(session, {})
    session._interactive_job = job
    before, revision = session.snapshot(), session.revision
    with pytest.raises(ValueError, match='page_only'):
        dispatch_session(session, '/api/search/publish', {
            'revision': revision, 'job_id': job.id, 'page_only': value,
        })
    assert session.snapshot() == before and session.revision == revision
    assert session._interactive_job is job
    job.close()


def test_prepared_runs_match_fresh_runs_and_share_no_mutable_state():
    layout = session_for('bridge-completed.json').layout
    context = _prepare_drive(layout)
    assignments = _tongue_assignments(layout, choices=context.choices)
    for _ in range(3):
        settings = next(assignments)
        original = dict(settings)
        for start in _all_starts(layout)[::11]:
            expected = drive(layout, start, settings)
            actual = drive(layout, start, settings, _context=context)
            assert actual == expected and settings == original
            assert actual.final_switch_states is not expected.final_switch_states
            actual.final_switch_states.clear()
            assert drive(layout, start, settings, _context=context) == expected
    with pytest.raises(TypeError):
        context.stones[0] = ()
    with pytest.raises(ValueError, match='different layout'):
        drive(layout, _context=replace(context, layout=type(layout)(layout.placements)))


@pytest.mark.parametrize('stone', ['stone_stop', 'stone_direction'])
def test_context_preserves_stone_positions_and_limits(stone):
    from duplotrain.geometry import Pose
    from duplotrain.layout import Layout, Placement

    catalog = default_catalog()
    layout = Layout([Placement(catalog['straight'], Pose.make())])
    for face in [None, 0, 1]:
        variant = layout.with_accessory(0, stone, at_port=face)
        context = _prepare_drive(variant)
        for start in [(0, 0), (0, 1)]:
            assert drive(variant, start) == drive(variant, start, _context=context)
    complete = session_for('bridge-completed.json').layout
    for context in [None, _prepare_drive(complete)]:
        with pytest.raises(DriveLimitError):
            drive(complete, (0, 0), max_steps=1, _context=context)


def test_classifier_and_route_job_prepare_choices_once(monkeypatch):
    import importlib

    module = importlib.import_module('duplotrain.drive')
    layout = session_for('bridge-completed.json').layout
    calls, original = [], module._tongue_choices

    def record(layout):
        calls.append(layout)
        return original(layout)

    monkeypatch.setattr(module, '_tongue_choices', record)
    verdict = classify(layout)
    assert verdict.runs == 11008 and verdict.looping
    assert len(calls) == 1
    calls.clear()
    job = RouteJob(Session(history=[layout], unlimited=True), {})
    finish(job)
    assert job.complete and job.runs == 11008
    assert len(calls) == 1
    assert job.best['visited'] == 57 and job.best['cycle_visited'] == 26
    job.close()
    assert job.drive_context is None
