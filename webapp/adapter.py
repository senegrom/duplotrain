"""Expose the same editor API in Pyodide as the local HTTP server."""

import json

from duplotrain.gui import RevisionConflictError, Session, dispatch_session
from duplotrain.validation import MAX_JSON_BYTES

session = Session()

try:
    from js import postMessage as _post

    def _progress(nodes: int) -> None:
        _post(nodes)

except ImportError:  # CPython tests/local host
    _progress = None


def dispatch(path: str, body_json: str | None) -> str:
    """Validate a request, then run the shared dispatcher without partial updates."""
    try:
        if body_json and len(body_json.encode("utf-8")) > MAX_JSON_BYTES:
            raise ValueError("request body larger than 2 MB")
        body = json.loads(body_json) if body_json else {}
        return json.dumps(dispatch_session(session, path, body, progress=_progress))
    except RevisionConflictError as exc:
        return json.dumps({
            "__error": str(exc), "code": "stale_revision", "state": session.state(),
        })
    except (ValueError, KeyError, TypeError, IndexError, OverflowError, RecursionError) as exc:
        return json.dumps({"__error": str(exc)})
