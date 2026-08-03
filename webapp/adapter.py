"""Pyodide adapter: the GUI's HTTP routes as one in-process dispatch function.

Runs the exact same :class:`duplotrain.gui.Session` the local server uses; the
browser front end calls :func:`dispatch` (via ``webapp/boot.js``) instead of fetch.
"""

import json

from duplotrain.gui import Session
from duplotrain.layout import layout_from_dict, layout_to_dict

session = Session()


def dispatch(path: str, body_json: str | None) -> str:
    """Handle one editor API call; returns the JSON the HTTP server would send."""
    body = json.loads(body_json) if body_json else {}
    try:
        if path == "/api/state":
            return json.dumps(session.state())
        if path == "/api/export":
            return json.dumps(layout_to_dict(session.layout))
        if path == "/api/attach":
            at = tuple(body["at"]) if body.get("at") is not None else None
            session.attach(body["piece"], int(body["entry"]), at)
        elif path == "/api/join":
            session.join(tuple(body["a"]), tuple(body["b"]))
        elif path == "/api/undo":
            session.undo()
        elif path == "/api/remove":
            session.remove_piece(int(body["placement"]))
        elif path == "/api/clear":
            session.clear()
        elif path == "/api/inventory":
            session.set_inventory(body.get("counts", {}))
        elif path == "/api/add_set":
            session.add_set(str(body["code"]))
        elif path == "/api/stone":
            session.toggle_stone(
                int(body["placement"]),
                str(body["id"]),
                int(body["at_port"]) if body.get("at_port") is not None else None,
            )
        elif path == "/api/solve":
            found = session.solve_gap(
                tuple(body["grow"]) if body.get("grow") else None,
                tuple(body["close"]) if body.get("close") else None,
                float(body.get("slop", 0.0)),
                int(body.get("max_results", 10)),
                reversing=bool(body.get("reversing", False)),
            )
            return json.dumps({"found": found, **session.state()})
        elif path == "/api/apply":
            session.apply_candidate(int(body["index"]))
        elif path == "/api/import":
            session._push(layout_from_dict(body["data"], session.catalog))
        else:
            return json.dumps({"__error": f"no route {path}"})
        return json.dumps(session.state())
    except (ValueError, KeyError, TypeError) as exc:
        return json.dumps({"__error": str(exc)})
