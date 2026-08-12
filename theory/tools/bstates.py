#!/usr/bin/env python3
"""Distinct-tongue-vector counter for lazy-point wirings.

Faithful port of DuplotrainProofs.lean's maxStates machinery:
ports of switch k are 3k (stem), 3k+1, 3k+2 (branches); a wiring is a
list of undirected port edges plus capped ports; arrive INTO a port
follows the lazy-point rule (stem: follow tongue, no flip; branch:
exit stem, flip tongue onto the entered branch).

Used to (a) locate the maxStates witnesses at small N, (b) evaluate
parametric families at larger N, (c) random-probe for counterexamples
to the min(2^N, N+4) conjecture.
"""

import sys
import random
from itertools import combinations


def arrive(t, p):
    k, a = divmod(p, 3)
    if a == 0:
        b = 2 if (t >> k) & 1 else 1
        return 3 * k + b, t
    # branch entry: exit stem, point tongue at entered branch
    if a == 2:
        t |= 1 << k
    else:
        t &= ~(1 << k)
    return 3 * k, t


def run_vectors(edge_of, n, start_port, t, seen):
    """Walk from arriving state; count distinct tongue vectors until the
    machine state repeats or the train falls off. Machine state =
    (port-about-to-arrive-at, tongues)."""
    states = set()
    vecs = set(seen)
    p = start_port
    fuel = 6 * n * (1 << n) + 16
    for _ in range(fuel):
        st = (p, t)
        if st in states:
            break
        states.add(st)
        exit_p, t = arrive(t, p)
        vecs.add(t)
        nxt = edge_of.get(exit_p)
        if nxt is None:
            break
        p = nxt
    return len(vecs)


def max_states(edges, n, tongue_subset=None):
    """Max distinct vectors over all starts. tongue_subset limits the
    initial tongue vectors tried (None = all 2^n)."""
    edge_of = {}
    for a, b in edges:
        edge_of[a] = b
        edge_of[b] = a
    tongues = range(1 << n) if tongue_subset is None else tongue_subset
    best = 0
    ports = set(edge_of)
    for p in ports:
        for t in tongues:
            vecs = run_vectors(edge_of, n, p, t, {t})
            if vecs > best:
                best = vecs
    return best


def all_wirings(n):
    """All perfect-matchings-with-caps of the 3n ports (edges only kept;
    caps are the unmatched ports and irrelevant to edge_of)."""
    ports = list(range(3 * n))

    def go(rest):
        if not rest:
            yield []
            return
        p = rest[0]
        tail = rest[1:]
        # p capped
        for e in go(tail):
            yield e
        # p paired with a later port
        for i, q in enumerate(tail):
            rem = tail[:i] + tail[i + 1:]
            for e in go(rem):
                yield [(p, q)] + e
    return go(ports)


def connected(n, edges):
    seen = {0}
    for _ in range(n):
        for a, b in edges:
            if a // 3 in seen:
                seen.add(b // 3)
            if b // 3 in seen:
                seen.add(a // 3)
    return len(seen) == n


def witnesses(n, target):
    out = []
    for edges in all_wirings(n):
        if not connected(n, edges):
            continue
        if max_states(edges, n) >= target:
            out.append(edges)
    return out


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "w3"
    if cmd == "w3":
        ws = witnesses(3, 7)
        print(f"N=3 witnesses with >=7 states: {len(ws)}")
        for w in ws[:12]:
            print("  ", w)
    elif cmd == "family":
        # evaluate a family given as a python expression file arg
        pass
    elif cmd == "rand5":
        # random probe at N=5 for >= 10 vectors
        n = 5
        rng = random.Random(20260811)
        best = 0
        best_w = None
        trials = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
        for i in range(trials):
            ports = list(range(3 * n))
            rng.shuffle(ports)
            edges = []
            # random matching: pair 2m ports, cap the rest
            m = rng.randint(n, 3 * n // 2)
            for j in range(m):
                a, b = ports[2 * j], ports[2 * j + 1]
                edges.append((a, b))
            if not connected(n, edges):
                continue
            s = max_states(edges, n, tongue_subset=[0, (1 << n) - 1,
                                                    0b10101, 0b01010])
            if s > best:
                best = s
                best_w = edges
                print(f"trial {i}: {s} vectors  {edges}")
        print(f"best over {trials} random 5-switch wirings: {best}")
        print(best_w)
