"""Is any perfectly-looping track possible with 3+ switches?  Exhaustive proof.

Abstract model: n switches, each with ports S (stem), L, R.  A network wires
every port either to another port (a path of plain track -- length irrelevant
to the sweep question) or to a guarded stub (buffer + direction stone = a
reflector; this also covers every mid-path stone, since a stone splits its path
into two reflector-terminated stubs).

Switch dynamics (the real DUPLO rules): facing entry (stem) exits via the
tongue's branch, tongue unchanged; trailing entry (branch X) exits the stem and
forces tongue := X.  Reflectors bounce the train back.

A network is PERFECT iff from EVERY start (edge, direction) and EVERY initial
tongue assignment, the eventually-periodic run sweeps every edge in both
directions AND every switch route (S-L, S-R) in both directions.

We enumerate every wiring for n = 1..4 and report the perfect ones.
"""

import itertools
import sys
from functools import lru_cache

S, L, R = "S", "L", "R"


def all_wirings(n):
    """Yield (edges, caps): edges = tuple of frozen port pairs, caps = ports."""
    ports = [(k, a) for k in range(n) for a in (S, L, R)]

    def rec(remaining, edges, caps):
        if not remaining:
            yield tuple(edges), tuple(caps)
            return
        p = remaining[0]
        rest = remaining[1:]
        # cap p with a guarded reflector stub
        yield from rec(rest, edges, caps + [p])
        # pair p with any later port
        for i, q in enumerate(rest):
            yield from rec(
                rest[:i] + rest[i + 1 :], edges + [(p, q)], caps
            )

    yield from rec(ports, [], [])


def is_connected(n, edges, caps):
    adj = {k: set() for k in range(n)}
    for (k1, _a1), (k2, _a2) in edges:
        adj[k1].add(k2)
        adj[k2].add(k1)
    seen, todo = {0}, [0]
    while todo:
        k = todo.pop()
        for m in adj[k]:
            if m not in seen:
                seen.add(m)
                todo.append(m)
    return len(seen) == n


def classify_wiring(n, edges, caps):
    """True iff the wiring is perfect under the tongue automaton."""
    # Build connection map: port -> ('edge', edge index, end) for wired ports,
    # or ('cap', stub index) for guarded stubs.
    conn = {}
    for i, (p, q) in enumerate(edges):
        conn[p] = ("edge", i, 0)
        conn[q] = ("edge", i, 1)
    for j, p in enumerate(caps):
        conn[p] = ("cap", j, None)

    n_edges = len(edges)
    n_caps = len(caps)
    # Sweep targets: edges both directions, caps (stub swept by any bounce),
    # switch routes (k, X, direction) for X in L,R and direction in 0 (S->X),
    # 1 (X->S).
    route_ids = {}
    for k in range(n):
        for X in (L, R):
            for d in (0, 1):
                route_ids[(k, X, d)] = len(route_ids)
    N_TARGETS = 2 * n_edges + n_caps + len(route_ids)

    def target_edge(i, d):
        return 2 * i + d

    def target_cap(j):
        return 2 * n_edges + j

    def target_route(k, X, d):
        return 2 * n_edges + n_caps + route_ids[(k, X, d)]

    # State: (position, tongues) where position = ('e', i, d) travelling along
    # edge i in direction d (0: first->second port, 1: reverse), or
    # ('c', j) bouncing at cap j (transient).  Tongues: tuple of L/R per switch.
    def arrive(port, tongues, swept):
        """Train arrives INTO *port* of a switch; returns (exit_port, tongues)."""
        k, a = port
        if a == S:  # facing: follow the tongue
            X = tongues[k]
            swept.add(target_route(k, X, 0))
            return (k, X), tongues
        # trailing: force the tongue, exit the stem
        swept.add(target_route(k, a, 1))
        tongues = tongues[:k] + (a,) + tongues[k + 1 :]
        return (k, S), tongues

    def step(pos, tongues, swept):
        kind, i, d = pos
        assert kind == "e"
        swept.add(target_edge(i, d))
        dest = edges[i][1] if d == 0 else edges[i][0]
        what, idx, end = conn[dest]
        assert what == "edge" and idx == i  # arriving at dest port
        # leave the edge INTO the switch at dest
        exit_port, tongues = arrive(dest, tongues, swept)
        out = conn[exit_port]
        if out[0] == "cap":
            swept.add(target_cap(out[1]))
            # bounce: come straight back INTO the switch via the same port
            back_port, tongues = arrive(exit_port, tongues, swept)
            out = conn[back_port]
            if out[0] == "cap":
                swept.add(target_cap(out[1]))
                # bouncing between two caps of one switch: loops via arrive
                # again -- handle by iterating until we reach an edge
                seen_ports = set()
                while out[0] == "cap":
                    if back_port in seen_ports:
                        return None, tongues  #永 stuck between caps: no edge
                    seen_ports.add(back_port)
                    back_port, tongues = arrive(back_port, tongues, swept)
                    out = conn[back_port]
                    if out[0] == "cap":
                        swept.add(target_cap(out[1]))
            exit_port = back_port
            out = conn[exit_port]
        _w, j, end = out
        return ("e", j, 0 if end == 0 else 1), tongues

    def run_covers_all(start_pos, start_tongues):
        seen_states = {}
        swept_trace = []
        pos, tongues = start_pos, start_tongues
        swept = set()
        while True:
            key = (pos, tongues)
            if key in seen_states:
                cycle_start = seen_states[key]
                cycle_swept = set()
                for s in swept_trace[cycle_start:]:
                    cycle_swept |= s
                return len(cycle_swept) == N_TARGETS
            seen_states[key] = len(swept_trace)
            step_swept = set()
            nxt = step(pos, tongues, step_swept)
            swept_trace.append(step_swept)
            pos2, tongues = nxt
            if pos2 is None:
                return False
            pos = pos2

    tongue_space = list(itertools.product(*[(L, R)] * n))
    for i in range(n_edges):
        for d in (0, 1):
            for t in tongue_space:
                if not run_covers_all(("e", i, d), t):
                    return False
    return n_edges > 0


for n in (1, 2, 3, 4):
    total = 0
    connected = 0
    perfect = []
    for edges, caps in all_wirings(n):
        total += 1
        if not edges or not is_connected(n, edges, caps):
            continue
        connected += 1
        if classify_wiring(n, edges, caps):
            perfect.append((edges, caps))
    print(f"n={n}: {total} wirings, {connected} connected, "
          f"{len(perfect)} PERFECT")
    for edges, caps in perfect[:8]:
        e_str = ", ".join(f"{a[0]}{a[1]}-{b[0]}{b[1]}" for a, b in edges)
        c_str = ", ".join(f"{p[0]}{p[1]}*" for p in caps) or "none"
        print(f"    edges: {e_str}   guarded stubs: {c_str}")
    if len(perfect) > 8:
        print(f"    ... and {len(perfect) - 8} more")
