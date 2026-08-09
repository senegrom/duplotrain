"""Test the write-alternation law: on every periodic cycle, do productive
writes strictly alternate between the two active cells?"""
import random
import sys
from itertools import product

def matchings(slots):
    if not slots:
        yield []
        return
    a = slots[0]
    rest = slots[1:]
    for i, b in enumerate(rest):
        for m in matchings(rest[:i] + rest[i+1:]):
            yield [(a, b)] + m

def bar_from_matching(m, S):
    bar = [0] * S
    for a, b in m:
        bar[a] = b
        bar[b] = a
    return bar

def writes_on_cycle(cellOf, star, bar, r0, e0, stats, max_steps=6000):
    ncells = len(star)
    reg = list(r0)
    reg[cellOf[e0]] = e0
    e = e0
    seen = {}
    trail = []
    state = (e, tuple(reg))
    step = 0
    while state not in seen:
        if step >= max_steps:
            return
        seen[state] = step
        trail.append(state)
        read = reg[star[cellOf[e]]]
        e = bar[read]
        reg[cellOf[e]] = e
        state = (e, tuple(reg))
        step += 1
    cyc = trail[seen[state]:]
    n = len(cyc)
    # productive write cells in cycle order
    wcells = []
    for i in range(n):
        (e1, r1) = cyc[i]
        (e2, r2) = cyc[(i + 1) % n]
        c2 = cellOf[e2]
        if r1[c2] != e2:
            wcells.append(c2)
    if not wcells:
        return
    stats['active'] += 1
    consec = any(wcells[i] == wcells[(i + 1) % len(wcells)]
                 for i in range(len(wcells)))
    if len(wcells) < 2:
        consec = True  # a lone write repeating each period = same cell twice
    if consec:
        stats['consec'] += 1
        if stats['consec'] <= 3:
            print("CONSECUTIVE SAME-CELL WRITES:", wcells)
            print(f"  cellOf={list(cellOf)} star={list(star)} "
                  f"bar={list(bar)} r0={list(r0)} e0={e0}")
    stats['wlens'][len(wcells)] = stats['wlens'].get(len(wcells), 0) + 1

def run_exhaustive(ncells, S, stats):
    star = [c ^ 1 for c in range(ncells)]
    for cellOf in product(range(ncells), repeat=S):
        if len(set(cellOf)) != ncells:
            continue
        slots_of = [[s for s in range(S) if cellOf[s] == c]
                    for c in range(ncells)]
        for m in matchings(list(range(S))):
            bar = bar_from_matching(m, S)
            for r0 in product(*slots_of):
                for e0 in range(S):
                    writes_on_cycle(cellOf, star, bar, r0, e0, stats)

def run_random(ncells, S, trials, stats, seed):
    rng = random.Random(seed)
    star = [c ^ 1 for c in range(ncells)]
    for _ in range(trials):
        slots = list(range(S))
        rng.shuffle(slots)
        cellOf = [0] * S
        for c in range(ncells):
            cellOf[slots[c]] = c
        for s in slots[ncells:]:
            cellOf[s] = rng.randrange(ncells)
        slots_of = [[s for s in range(S) if cellOf[s] == c]
                    for c in range(ncells)]
        pairing = list(range(S))
        rng.shuffle(pairing)
        bar = [0] * S
        for i in range(0, S, 2):
            a, b = pairing[i], pairing[i + 1]
            bar[a] = b
            bar[b] = a
        for _ in range(6):
            r0 = [rng.choice(slots_of[c]) for c in range(ncells)]
            e0 = rng.randrange(S)
            writes_on_cycle(cellOf, star, bar, r0, e0, stats)

def main():
    stats = {'active': 0, 'consec': 0, 'wlens': {}}
    run_exhaustive(2, 4, stats)
    run_exhaustive(2, 6, stats)
    run_exhaustive(4, 6, stats)
    print("[exhaustive done]")
    sys.stdout.flush()
    run_random(4, 8, 60000, stats, seed=1)
    run_random(4, 10, 50000, stats, seed=2)
    run_random(4, 12, 40000, stats, seed=3)
    run_random(6, 12, 40000, stats, seed=5)
    run_random(8, 14, 30000, stats, seed=7)
    print("[random done]")
    print(f"active cycles: {stats['active']}   "
          f"with consecutive same-cell writes: {stats['consec']}")
    print("writes-per-period histogram:",
          dict(sorted(stats['wlens'].items())))

if __name__ == "__main__":
    main()
