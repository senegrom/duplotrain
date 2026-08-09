"""Classify the (2,2) active cycles of the abstract echo machine.

For every cycle with profile (2,2): which two cells are active, are they
star partners, are their values lobe pairs (bar inside the cell) or
cross pairs (bar into the other active cell) or outward (bar into a
frozen cell)?
"""
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

def classify(cellOf, star, bar, r0, e0, stats, max_steps=6000):
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
    vals = [set() for _ in range(ncells)]
    for (_, rr) in cyc:
        for c in range(ncells):
            vals[c].add(rr[c])
    active = [c for c in range(ncells) if len(vals[c]) >= 2]
    if len(active) != 2:
        return
    c1, c2 = active
    if not (len(vals[c1]) == 2 and len(vals[c2]) == 2):
        stats['odd'] += 1
        return
    is_star = (star[c1] == c2)

    def celltype(c, other):
        kinds = set()
        for v in vals[c]:
            p = cellOf[bar[v]]
            if p == c:
                kinds.add('lobe')
            elif p == other:
                kinds.add('cross')
            else:
                kinds.add('out')
        if kinds == {'lobe'}:
            return 'lobe'
        if kinds == {'cross'}:
            return 'cross'
        if kinds == {'out'}:
            return 'out'
        return 'mixed(' + ','.join(sorted(kinds)) + ')'

    t1 = celltype(c1, c2)
    t2 = celltype(c2, c1)
    tt = tuple(sorted([t1, t2]))
    # for cross-cross: are the value sets bar-images of each other?
    xtra = ''
    if tt == ('cross', 'cross'):
        paired = (vals[c1] == {bar[v] for v in vals[c2]})
        xtra = ' bar-paired' if paired else ' UNPAIRED'
    # lockstep: number of distinct (regC1, regC2) pairs on the cycle
    pairs = set()
    for (_, rr) in cyc:
        pairs.add((rr[c1], rr[c2]))
    key = (tt, 'star' if is_star else 'far', len(pairs), xtra)
    stats['classes'][key] = stats['classes'].get(key, 0) + 1

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
                    classify(cellOf, star, bar, r0, e0, stats)

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
            classify(cellOf, star, bar, r0, e0, stats)

def main():
    stats = {'classes': {}, 'odd': 0}
    run_exhaustive(2, 4, stats)
    run_exhaustive(2, 6, stats)
    run_exhaustive(4, 6, stats)
    print("[exhaustive done]")
    sys.stdout.flush()
    run_random(4, 8, 60000, stats, seed=1)
    run_random(4, 10, 50000, stats, seed=2)
    run_random(4, 12, 40000, stats, seed=3)
    run_random(6, 10, 40000, stats, seed=4)
    run_random(6, 12, 40000, stats, seed=5)
    run_random(8, 12, 30000, stats, seed=6)
    run_random(8, 14, 30000, stats, seed=7)
    print("[random done]")
    print(f"odd (2,2)-like but not clean: {stats['odd']}")
    print("(2,2) cycle classes  [types, star-relation, lockstep-pairs]:")
    for key, n in sorted(stats['classes'].items(), key=lambda kv: -kv[1]):
        print(f"  {key}   {n}")

if __name__ == "__main__":
    main()
