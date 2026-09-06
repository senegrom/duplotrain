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

    revision = 0

    def call(path, body=None):
        nonlocal revision
        if isinstance(body, dict):
            body = {"revision": revision, **body}
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
                data = json.loads(res.read())
                revision = data.get("revision", revision)
                return res.status, data
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


def test_buffer_is_placeable_from_the_palette(server):
    status, state = server("/api/state")
    buffer = next(p for p in state["palette"] if p["id"] == "buffer")
    assert buffer["variants"], "route-less pieces still need a placement button"
    variant = buffer["variants"][0]
    assert variant["label"] == "cap the end"

    _, state = server("/api/attach", {"piece": "straight", "entry": 0, "at": None})
    status, state = server(
        "/api/attach",
        {"piece": "buffer", "entry": variant["entry"], "at": state["open_ends"][-1]},
    )
    assert status == 200
    assert state["layout"]["placements"][1]["piece"] == "buffer"


def test_remove_piece_reindexes(server):
    _, state = server("/api/attach", {"piece": "straight", "entry": 0, "at": None})
    _, state = server(
        "/api/attach", {"piece": "curve", "entry": 0, "at": state["open_ends"][-1]}
    )
    _, state = server(
        "/api/attach", {"piece": "curve", "entry": 0, "at": state["open_ends"][-1]}
    )
    _, state = server("/api/stone", {"placement": 0, "id": "stone_stop"})
    assert len(state["layout"]["placements"]) == 3

    # Remove the middle curve: the chain splits, the stone stays on the straight.
    status, state = server("/api/remove", {"placement": 1})
    assert status == 200
    assert len(state["layout"]["placements"]) == 2
    assert [p["piece"] for p in state["layout"]["placements"]] == ["straight", "curve"]
    assert state["layout"]["placements"][0]["stones"] == ["stone_stop"]
    assert len(state["open_ends"]) == 4  # two loose chains now

    status, err = server("/api/remove", {"placement": 7})
    assert status == 409


def test_errors_are_json_not_500(server):
    status, err = server("/api/attach", {"piece": "warp_gate", "entry": 0, "at": None})
    assert status == 409
    assert "unknown piece" in err["error"]
    status, err = server("/api/apply", {"index": 3})
    assert status == 409

def test_unlimited_sandbox_mode(server):
    # Exhaust a scarce piece under normal rules: only 1 crossing in the default box.
    status, state = server("/api/attach", {"piece": "crossing", "entry": 0, "at": None})
    assert status == 200
    status, err = server(
        "/api/attach", {"piece": "crossing", "entry": 0, "at": [0, 1]}
    )
    assert status == 409  # none left in the box

    status, state = server("/api/unlimited", {"on": True})
    assert status == 200
    assert state["inventory"]["unlimited"] is True
    assert state["inventory"]["remaining"]["crossing"] > 1

    status, state = server(
        "/api/attach", {"piece": "crossing", "entry": 0, "at": [0, 1]}
    )
    assert status == 200
    assert len(state["layout"]["placements"]) == 2

    # Switching back restores the real counts (now over-budget, clamped to 0).
    status, state = server("/api/unlimited", {"on": False})
    assert status == 200
    assert state["inventory"]["unlimited"] is False
    assert state["inventory"]["remaining"]["crossing"] == 0


def test_arc_oracle_finds_winding_ring_closures():
    """A gap whose only closure winds AWAY from the target (10 same-sign curves
    looping around) starves the DFS -- the arc oracle must find it instantly."""
    from duplotrain.gui import Session

    session = Session()
    session.set_inventory({"curve": 24, "straight": 8})
    session.attach("curve", 0, None)
    session.attach("curve", 0, (0, 1))
    opens = session.layout.connectable_ends()
    outcome = session.solve_gap(opens[1], opens[0], slop=0.0, max_results=5)
    assert outcome["found"] > 0
    assert outcome["searched"] == 0  # the oracle, not the search
    added = session.candidates[0].layout.piece_counts["curve"] - 2
    assert added == 10  # completes the 12-curve circle


def test_height_impossibility_is_reported_with_a_reason():
    """Both ramps and spans climbing in series leave a sky-high end no search
    can ever bring down -- solve_gap must say so instead of searching."""
    from duplotrain.gui import Session

    session = Session()
    session.set_inventory({"ramp": 2, "span": 2, "curve": 12, "straight": 8})
    session.attach("ramp", 0, None)
    session.attach("span", 0, (0, 1))
    session.attach("span", 0, (1, 1))
    session.attach("ramp", 0, (2, 1))
    opens = session.layout.connectable_ends()
    outcome = session.solve_gap(opens[1], opens[0], slop=0.0, max_results=5)
    assert outcome["found"] == 0
    assert "height" in outcome["reason"]
    assert "154" in outcome["reason"]


def test_arc_oracle_levels_through_ramps():
    """One end atop a half-built climb, the other at ground: no flat chain can
    close this -- the oracle must descend through a ramp, then ring around."""
    from duplotrain.gui import Session

    session = Session()
    session.set_inventory({"curve": 12, "ramp": 2, "straight": 8})
    session.attach("curve", 0, None)
    for _ in range(5):
        session.attach("curve", 0, (len(session.layout) - 1, 1))
    high_end = session.layout.connectable_ends()[-1]
    session.attach("ramp", 0, high_end)
    tips = session.layout.connectable_ends()
    grow = next(t for t in tips if float(session.layout.pose_of(t).z) > 1)
    close = next(t for t in tips if float(session.layout.pose_of(t).z) <= 1)
    outcome = session.solve_gap(grow, close, slop=0.0, max_results=5)
    assert outcome["found"] > 0
    assert outcome["searched"] == 0
    counts = dict(session.candidates[0].layout.piece_counts)
    assert counts["ramp"] == 2  # the descending ramp was added
    assert counts["curve"] == 12


@pytest.mark.parametrize("coefficient", ["1e999999999", "1/0"])
def test_invalid_numeric_import_returns_json_and_preserves_state(server, coefficient):
    _, before = server("/api/attach", {"piece": "straight", "entry": 0, "at": None})
    _, data = server("/api/export")
    data["placements"][0]["frame"]["x"][0] = coefficient
    status, error = server("/api/import", {"data": data})
    assert status == 409
    assert "error" in error
    _, after = server("/api/state")
    assert before == after


def test_non_object_body_and_invalid_port_return_json(server):
    status, error = server("/api/inventory", [])
    assert status == 409
    assert "object" in error["error"]
    status, error = server("/api/attach", {"piece": "straight", "entry": -1, "at": None})
    assert status == 409
    assert "port" in error["error"]
