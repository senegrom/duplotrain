"""Abstract echo machine: search for periodic tails violating lemma B.

Machine: slots 0..S-1, cells 0..2m-1 with star = canonical pairing
(0,1),(2,3),...; cellOf : slot -> cell (surjective); bar : fixed-point-free
involution on slots (perfect matching, lobes allowed); r0 : well-formed
initial registers (cellOf(r0 c) = c, otherwise arbitrary); e0 : any slot.

Run: e' = bar(reg[star[cellOf[e]]]); reg[cellOf[e']] = e'.
Detect the rho, take the cycle, compute per-cell sigma = #values of reg[c]
on the cycle.  Lemma B (abstract form): sum(sigma-1) <= 2, hence <= 4
distinct register snapshots on the cycle.  Report any violation.
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

def simulate(cellOf, star, bar, r0, e0, max_steps=6000):
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
            return None
        seen[state] = step
        trail.append(state)
        read = reg[star[cellOf[e]]]
        e = bar[read]
        reg[cellOf[e]] = e
        state = (e, tuple(reg))
        step += 1
    start = seen[state]
    cyc = trail[start:]
    vals = [set() for _ in range(ncells)]
    snaps = set()
    for (ee, rr) in cyc:
        snaps.add(rr)
        for c in range(ncells):
            vals[c].add(rr[c])
    sig = [len(v) for v in vals]
    excess = sum(s - 1 for s in sig)
    prof = tuple(sorted((s for s in sig if s >= 2), reverse=True))
    return excess, prof, len(snaps), len(cyc), start

def report_hit(tag, cellOf, star, bar, r0, e0, res):
    excess, prof, nsnaps, plen, pre = res
    print("=" * 60)
    print(f"VIOLATION [{tag}] excess={excess} profile={prof} "
          f"snapshots={nsnaps} period={plen} preperiod={pre}")
    print(f"  cellOf={list(cellOf)}")
    print(f"  star  ={list(star)}")
    print(f"  bar   ={list(bar)}")
    print(f"  r0    ={list(r0)}  e0={e0}")
    print("=" * 60)
    sys.stdout.flush()

def check(tag, cellOf, star, bar, r0, e0, stats, hits):
    res = simulate(cellOf, star, bar, r0, e0)
    if res is None:
        stats['nocycle'] += 1
        return
    excess, prof, nsnaps, plen, pre = res
    stats['profiles'][prof] = stats['profiles'].get(prof, 0) + 1
    stats['maxsnaps'] = max(stats['maxsnaps'], nsnaps)
    if excess > stats['maxexcess']:
        stats['maxexcess'] = excess
    if excess >= 3 or nsnaps > 4:
        hits.append((tag, list(cellOf), list(star), list(bar),
                     list(r0), e0, res))
        report_hit(tag, cellOf, star, bar, r0, e0, res)

def exhaustive(ncells, S, stats, hits, cap=None):
    star = [c ^ 1 for c in range(ncells)]
    count = 0
    for cellOf in product(range(ncells), repeat=S):
        if len(set(cellOf)) != ncells:
            continue
        slots_of = [[s for s in range(S) if cellOf[s] == c]
                    for c in range(ncells)]
        for m in matchings(list(range(S))):
            bar = bar_from_matching(m, S)
            for r0 in product(*slots_of):
                for e0 in range(S):
                    check(f"exh c{ncells} S{S}", cellOf, star, bar,
                          r0, e0, stats, hits)
                    count += 1
                    if cap and count >= cap:
                        return count
    return count

def random_search(ncells, S, trials, stats, hits, seed):
    rng = random.Random(seed)
    star = [c ^ 1 for c in range(ncells)]
    count = 0
    for _ in range(trials):
        # random surjective cellOf
        slots = list(range(S))
        rng.shuffle(slots)
        cellOf = [0] * S
        for c in range(ncells):
            cellOf[slots[c]] = c
        for s in slots[ncells:]:
            cellOf[s] = rng.randrange(ncells)
        slots_of = [[s for s in range(S) if cellOf[s] == c]
                    for c in range(ncells)]
        # random perfect matching
        pairing = list(range(S))
        rng.shuffle(pairing)
        bar = [0] * S
        for i in range(0, S, 2):
            a, b = pairing[i], pairing[i + 1]
            bar[a] = b
            bar[b] = a
        # several r0/e0 per machine
        for _ in range(6):
            r0 = [rng.choice(slots_of[c]) for c in range(ncells)]
            e0 = rng.randrange(S)
            check(f"rnd c{ncells} S{S}", cellOf, star, bar, r0, e0,
                  stats, hits)
            count += 1
    return count

def main():
    stats = {'profiles': {}, 'maxsnaps': 0, 'maxexcess': 0, 'nocycle': 0}
    hits = []
    total = 0

    total += exhaustive(2, 4, stats, hits)
    print(f"[exh c2 S4 done] total={total}")
    total += exhaustive(2, 6, stats, hits)
    print(f"[exh c2 S6 done] total={total}")
    total += exhaustive(4, 6, stats, hits)
    print(f"[exh c4 S6 done] total={total}")
    sys.stdout.flush()

    total += random_search(4, 8, 60000, stats, hits, seed=1)
    print(f"[rnd c4 S8 done] total={total}")
    total += random_search(4, 10, 50000, stats, hits, seed=2)
    print(f"[rnd c4 S10 done] total={total}")
    total += random_search(4, 12, 40000, stats, hits, seed=3)
    print(f"[rnd c4 S12 done] total={total}")
    total += random_search(6, 10, 40000, stats, hits, seed=4)
    print(f"[rnd c6 S10 done] total={total}")
    total += random_search(6, 12, 40000, stats, hits, seed=5)
    print(f"[rnd c6 S12 done] total={total}")
    total += random_search(8, 12, 30000, stats, hits, seed=6)
    print(f"[rnd c8 S12 done] total={total}")
    total += random_search(8, 14, 30000, stats, hits, seed=7)
    print(f"[rnd c8 S14 done] total={total}")

    print()
    print(f"TOTAL SIMULATIONS: {total}   no-cycle(cap): {stats['nocycle']}")
    print(f"MAX excess sum(sigma-1) seen: {stats['maxexcess']}")
    print(f"MAX cycle snapshots seen:     {stats['maxsnaps']}")
    print(f"VIOLATIONS: {len(hits)}")
    print("profile histogram (top 20):")
    for prof, n in sorted(stats['profiles'].items(),
                          key=lambda kv: -kv[1])[:20]:
        label = str(prof) if prof else '()'
        print(f"  {label:<20} {n}")

if __name__ == "__main__":
    main()
