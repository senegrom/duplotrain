"""The editor's HTTP API, exercised over a real local socket."""

import json
import threading
import urllib.request

import pytest

from duplotrain.gui import Session, make_server


@pytest.fixture()
def server():
    session = Session()
    srv = make_server(session, port=0)
    thread = threading.Thread(target=srv.serve_forever, daemon=True)
    thread.start()
    base = f"http://127.0.0.1:{srv.server_port}"

    def call(path, body=None):
        if body is None:
            req = urllib.request.Request(base + path)
        else:
            req = urllib.request.Request(
                base + path,
                data=json.dumps(body).encode(),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
        try:
            with urllib.request.urlopen(req) as res:
                return res.status, json.loads(res.read())
        except urllib.error.HTTPError as exc:
            return exc.code, json.loads(exc.read())

    call.base = base  # expose for raw fetches
    yield call
    srv.shutdown()
    srv.server_close()


def test_editor_page_serves(server):
    with urllib.request.urlopen(server.base + "/") as res:
        assert res.status == 200
        body = res.read().decode("utf-8")
    assert "duplotrain editor" in body

    status, state = server("/api/state")
    assert status == 200
    assert state["layout"]["placements"] == []
    curve = next(p for p in state["palette"] if p["id"] == "curve")
    assert {v["label"] for v in curve["variants"]} == {"turn left", "turn right"}


def test_attach_undo_clear(server):
    status, state = server("/api/attach", {"piece": "curve", "entry": 0, "at": None})
    assert status == 200
    assert len(state["layout"]["placements"]) == 1
    assert len(state["open_ends"]) == 2

    status, state = server(
        "/api/attach", {"piece": "straight", "entry": 0, "at": state["open_ends"][-1]}
    )
    assert status == 200
    assert len(state["layout"]["placements"]) == 2

    status, state = server("/api/undo", {})
    assert len(state["layout"]["placements"]) == 1
    status, state = server("/api/clear", {})
    assert state["layout"]["placements"] == []


def test_inventory_is_enforced(server):
    status, state = server("/api/inventory", {"counts": {"switch": 1}})
    assert status == 200
    status, state = server("/api/attach", {"piece": "switch", "entry": 0, "at": None})
    assert status == 200
    end = state["open_ends"][-1]
    status, err = server("/api/attach", {"piece": "switch", "entry": 0, "at": end})
    assert status == 409
    assert "no 'switch' left" in err["error"]


def test_solve_and_apply_close_the_loop(server):
    _, state = server("/api/attach", {"piece": "curve", "entry": 0, "at": None})
    for _ in range(5):
        _, state = server(
            "/api/attach", {"piece": "curve", "entry": 0, "at": state["open_ends"][-1]}
        )
    assert len(state["layout"]["placements"]) == 6

    status, state = server("/api/solve", {"slop": 0, "max_results": 8})
    assert status == 200
    assert state["found"] >= 1
    exact = [c for c in state["candidates"] if c["exact"]]
    assert exact
    assert exact[0]["added"] == {"curve": 6}

    status, state = server("/api/apply", {"index": exact[0]["index"]})
    assert status == 200
    assert state["layout"]["closed"] is True
    assert len(state["layout"]["placements"]) == 12


def test_manual_join_when_ends_mate(server):
    _, state = server("/api/attach", {"piece": "curve", "entry": 0, "at": None})
    for _ in range(11):
        _, state = server(
            "/api/attach", {"piece": "curve", "entry": 0, "at": state["open_ends"][-1]}
        )
    assert state["matable"], "a full circle's two ends must be reported matable"
    a, b = state["matable"][0]
    status, state = server("/api/join", {"a": a, "b": b})
    assert status == 200
    assert state["layout"]["closed"] is True


def test_export_round_trips(server):
    _, state = server("/api/attach", {"piece": "curve", "entry": 0, "at": None})
    status, exported = server("/api/export")
    assert status == 200
    assert exported["format"].startswith("duplotrain-layout/")
    status, state = server("/api/clear", {})
    status, state = server("/api/import", {"data": exported})
    assert status == 200
    assert len(state["layout"]["placements"]) == 1


def test_add_set_bumps_inventory(server):
    status, before = server("/api/state")
    owned_before = before["inventory"]["owned"]["curve"]
    status, state = server("/api/add_set", {"code": "10882"})
    assert status == 200
    assert state["inventory"]["owned"]["curve"] == owned_before + 10
    assert state["inventory"]["owned"]["buffer"] >= 2
    assert state["stones"]["owned"]["stone_stop"] >= 1
    status, err = server("/api/add_set", {"code": "1234"})
    assert status == 409
    assert "unknown set" in err["error"]


def test_stone_toggles_on_straights_only(server):
    _, state = server("/api/attach", {"piece": "straight", "entry": 0, "at": None})
    status, state = server("/api/stone", {"placement": 0, "id": "stone_direction"})
    assert status == 200
    assert state["layout"]["placements"][0]["stones"] == ["stone_direction"]
    # Toggling again removes it.
    status, state = server("/api/stone", {"placement": 0, "id": "stone_direction"})
    assert state["layout"]["placements"][0]["stones"] == []

    _, state = server(
        "/api/attach", {"piece": "curve", "entry": 0, "at": state["open_ends"][-1]}
    )
    status, err = server("/api/stone", {"placement": 1, "id": "stone_stop"})
    assert status == 409
    assert "clip onto straights" in err["error"]


def test_sealed_buffer_end_is_not_clickable(server):
    _, state = server("/api/attach", {"piece": "straight", "entry": 0, "at": None})
    _, state = server(
        "/api/attach", {"piece": "buffer", "entry": 0, "at": state["open_ends"][-1]}
    )
    ports = state["layout"]["placements"][1]["ports"]
    assert any(p["sealed"] for p in ports)
    # The sealed face is not among the offered open ends.
    assert [1, 1] not in state["open_ends"]
    status, err = server(
        "/api/attach", {"piece": "straight", "entry": 0, "at": [1, 1]}
    )
    assert status == 409
    assert "sealed" in err["error"]


def test_errors_are_json_not_500(server):
    status, err = server("/api/attach", {"piece": "warp_gate", "entry": 0, "at": None})
    assert status == 409
    assert "unknown piece" in err["error"]
    status, err = server("/api/apply", {"index": 3})
    assert status == 409