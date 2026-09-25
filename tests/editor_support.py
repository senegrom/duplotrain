"""Small transport helpers; each test keeps its own scenarios and assertions."""

import http.client
import importlib.util
import json
import threading
from contextlib import contextmanager
from pathlib import Path

from duplotrain.gui import Session, make_server


def unchanged(session):
    """Include candidate identity state and the undo AND redo history, not only
    visible geometry: a rejected edit must keep redo (docs/editor.md, History)."""
    return (session.snapshot(), list(session.history), list(session._history_state),
            list(session._future), session.revision, list(session.candidates),
            session._candidate_revision)


@contextmanager
def running_server(session):
    server = make_server(session, 0)
    thread = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.01})
    thread.start()
    try:
        yield server
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=3)
        assert not thread.is_alive(), "local test server did not stop"


def post(server, path, body):
    conn = http.client.HTTPConnection("127.0.0.1", server.server_port, timeout=3)
    try:
        conn.request("POST", path, json.dumps(body), {"Content-Type": "application/json"})
        response = conn.getresponse()
        return response.status, json.loads(response.read())
    finally:
        conn.close()


def load_adapter(session=None):
    """Every caller receives a fresh, isolated adapter and session."""
    spec = importlib.util.spec_from_file_location(
        "test_editor_adapter", Path(__file__).parents[1] / "webapp/adapter.py",
    )
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    adapter.session = Session() if session is None else session
    return adapter


def complete(session, grow=None, close=None, **body):
    """Run a closing search through the editor's routes to its stop, and publish
    its suggestions so ``apply_candidate`` can use them. Returns the job."""
    from duplotrain.editor import dispatch_session

    if grow is not None:
        body = {**body, "grow": grow, "close": close}
    dispatch_session(session, "/api/search/start", {**body, "revision": session.revision})
    job = session._interactive_job
    while job.status == "running":
        job.tick()
    dispatch_session(session, "/api/search/publish",
                     {"revision": session.revision, "job_id": job.id})
    return job
