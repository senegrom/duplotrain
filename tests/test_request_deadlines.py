"""Total request-read deadlines, not resettable per-read idle timeouts."""

import http.client
import socket
import threading
import time
from email.message import Message
from types import SimpleNamespace

import pytest

import duplotrain.gui as gui
from duplotrain.gui import Session, _handler_for, make_server


def simulated_handler(monkeypatch, length=100):
    handler = object.__new__(_handler_for(Session()))
    handler.headers = Message()
    handler.headers["Content-Length"] = str(length)
    clock = SimpleNamespace(now=0.0, timeout=10.0, reads=0, timeouts=[])
    monkeypatch.setattr(gui, "monotonic", lambda: clock.now)

    def settimeout(value):
        clock.timeout = value
        clock.timeouts.append(value)

    def read1(size):
        assert size > 0
        clock.reads += 1
        clock.now += min(0.1, clock.timeout)
        if clock.timeout < 0.1:
            raise TimeoutError
        return b"x"

    handler.connection = SimpleNamespace(gettimeout=lambda: clock.timeout, settimeout=settimeout)
    handler.rfile = SimpleNamespace(read1=read1)
    return handler, clock


def test_trickling_bytes_cannot_extend_the_drain_deadline(monkeypatch):
    handler, clock = simulated_handler(monkeypatch)
    handler._drain_body()
    assert clock.now == pytest.approx(handler.DRAIN_SECONDS)
    assert clock.reads == 3
    assert clock.timeouts[:3] == pytest.approx([0.25, 0.15, 0.05])
    assert clock.timeout == 10.0


def test_accepted_body_reads_also_have_a_total_deadline(monkeypatch):
    handler, clock = simulated_handler(monkeypatch)
    handler.BODY_SECONDS = 0.25
    with pytest.raises(TimeoutError):
        handler._body()
    assert clock.now == pytest.approx(0.25)
    assert handler._body_read_failed
    assert handler._body_bytes_read == 2
    handler._drain_body()
    assert clock.reads == 3  # No retry on the now-unreadable buffered socket.
    assert clock.timeout == 10.0


def test_already_consumed_bad_json_is_not_drained_again(monkeypatch):
    handler, clock = simulated_handler(monkeypatch, length=1)
    with pytest.raises(ValueError):
        handler._body()  # x is not JSON, but its one declared byte was consumed.
    assert handler._body_bytes_read == 1
    handler._drain_body()
    assert clock.reads == 1


def test_drain_reads_only_the_unconsumed_declared_bytes(monkeypatch):
    handler, clock = simulated_handler(monkeypatch, length=3)
    handler._body_bytes_read = 2
    handler._drain_body()
    assert clock.reads == 1
    assert clock.now == pytest.approx(0.1)


def test_drain_byte_budget_is_still_enforced(monkeypatch):
    handler, clock = simulated_handler(monkeypatch, length=100000)
    sizes = []

    def read1(size):
        sizes.append(size)
        return b"x" * size

    handler.rfile.read1 = read1
    handler._drain_body()
    assert sum(sizes) == handler.DRAIN_BYTES
    assert clock.timeout == 10.0


def test_real_socket_refuses_slow_body_without_waiting_for_all_bytes():
    session = Session()
    session.attach("straight", 0, None)
    before = session.snapshot(), session.revision
    server = make_server(session, 0)
    serving = threading.Thread(target=server.serve_forever, kwargs={"poll_interval": 0.01})
    serving.start()
    stop = threading.Event()
    sender = None
    sock = socket.create_connection(("127.0.0.1", server.server_port), timeout=3)
    try:
        started = time.monotonic()
        sock.sendall((
            f"POST /api/clear HTTP/1.1\r\nHost: 127.0.0.1:{server.server_port}\r\n"
            "Origin: https://foreign.invalid\r\nContent-Type: text/plain\r\n"
            "Content-Length: 4096\r\n\r\n"
        ).encode())

        def trickle():
            for _ in range(40):
                if stop.wait(0.05):
                    break
                try:
                    sock.sendall(b"x")
                except OSError:
                    break

        sender = threading.Thread(target=trickle)
        sender.start()
        response = http.client.HTTPResponse(sock)
        response.begin()
        # Timestamp actual response receipt; do not measure the sender loop.
        elapsed = time.monotonic() - started
        stop.set()
        assert response.status == 403
        assert b"forbidden" in response.read()
        assert elapsed < 1.0  # Generous CI margin; the old idle timeout exceeds 2s.
        assert (session.snapshot(), session.revision) == before
    finally:
        stop.set()
        if sender is not None:
            sender.join(timeout=3)
        sock.close()
        server.shutdown()
        server.server_close()
        serving.join()
