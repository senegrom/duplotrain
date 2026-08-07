"""The echo machine: abstract cycle dynamics of lazy-point wirings.

T9 (docs/lazy-point-theory.md) compiles any wiring's trailing structure
into a forest of trees whose eventual-cycle dynamics is this register
machine:

  - cells (= trees), paired by an involution `star` (mouth edges pair
    roots, hence trees, symmetrically);
  - slots (= free branch ports), each in one cell, paired by an
    involution `bar` (jump edges = branch-branch track edges);
  - one register per cell = the slot of that cell's most recent ascent
    (proved: a root-descent exits at the last-ascent slot);
  - step, from ascent-entry e:
        T = cell(e); reg[T] := e          (ascend T at e)
        f = reg[star(T)]                  (descend the partner tree)
        next entry = bar(f)               (jump edge)
    reg[.] = None -> fall (only possible pre-cycle / with caps).

Measured per run:
  * distinct entries on the eventual cycle
  * actives = sum over cells of (distinct cycle slots - 1)
             [lemma B / C* predicts <= 2]
  * deep returns on the cycle (reads older than the previous ascent)
  * transient alternations  [lemma C predicts O(1); observed <= 1]

Results (this file's sweep plus larger ones, 2026-08-06):
  C=2 S<=6 exhaustive (3,272 runs)          max actives 2, transient alt 1
  C=4 S<=8 exhaustive (183,012 runs)        max actives 2, transient alt 1
  C=6 two-2-slot-cells exhaustive (50,400)  max actives 2, transient alt 1
  C=8 random 300k                           max actives 2, transient alt 1
  C=10 random 300k                          max actives 2, transient alt 1
Cycles carry up to 12 distinct entries, but the surplus always lives in
one-slot cells, which pin nothing: actives never exceed 2.  Sharper: the
per-cell sigma profile of every observed cycle (C=4 exhaustive, C=8
random 300k) is either () — no cell alternates — or exactly (2, 2): two
cells of two slots each, the dogbone Gray square.  Never (2) alone,
never (3).
"""

import itertools
import random
import time


def matchings(elems):
    if not elems:
        yield []
        return
    a, rest = elems[0], elems[1:]
    for i, b in enumerate(rest):
        for m in matchings(rest[:i] + rest[i + 1:]):
            yield [(a, b)] + m


def run(cellOf, star, bar, r0, e0, limit=100000):
    regs = list(r0)
    seen = {}
    hist = []
    e = e0
    while len(hist) < limit:
        state = (e, tuple(regs))
        if state in seen:
            s = seen[state]
            return hist[:s], hist[s:]
        seen[state] = len(hist)
        hist.append(e)
        T = cellOf[e]
        regs[T] = e
        f = regs[star[T]]
        if f is None:
            return hist, None
        e = bar[f]
    raise RuntimeError("limit hit")


def analyze(cellOf, star, transient, cycle):
    """Return (entries, actives, deep, pre_alt, cyc_alt)."""
    ents = sorted(set(cycle))
    percell = {}
    for e in cycle:
        percell.setdefault(cellOf[e], set()).add(e)
    actives = sum(len(s) - 1 for s in percell.values())
    hist = transient + cycle * 3
    P = len(cycle)
    deep = 0
    for k in range(len(hist) - P, len(hist)):
        tgt = star[cellOf[hist[k]]]
        j = None
        for i in range(k - 1, -1, -1):
            if cellOf[hist[i]] == tgt:
                j = i
                break
        if j is not None and k - j > 1:
            deep += 1

    def alternations(seq, last):
        alt = 0
        for e in seq:
            c = cellOf[e]
            if c in last and last[c] != e:
                alt += 1
            last[c] = e
        return alt, last

    pre_alt, last = alternations(transient, {})
    cyc_alt, _ = alternations(cycle, last)
    return len(ents), actives, deep, pre_alt, cyc_alt


def sweep(C, star, comps, tag):
    best = dict(entries=0, actives=0, deep=0, pre_alt=0, cyc_alt=0)
    examples = {}
    total = cycles = 0
    for comp in comps:
        S = sum(comp)
        cellOf = []
        for c, n in enumerate(comp):
            cellOf += [c] * n
        slots_of = [[i for i in range(S) if cellOf[i] == c] for c in range(C)]
        for m in matchings(list(range(S))):
            bar = list(range(S))
            for a, b in m:
                bar[a], bar[b] = b, a
            for r0 in itertools.product(*slots_of):
                for e0 in range(S):
                    total += 1
                    transient, cycle = run(cellOf, star, bar, list(r0), e0)
                    if cycle is None:
                        continue
                    cycles += 1
                    ent, act, deep, pa, ca = analyze(
                        cellOf, star, transient, cycle)
                    for key, val in (("entries", ent), ("actives", act),
                                     ("deep", deep), ("pre_alt", pa),
                                     ("cyc_alt", ca)):
                        if val > best[key]:
                            best[key] = val
                            examples[key] = (comp, m, r0, e0,
                                             transient, cycle)
    print(f"[{tag}] runs {total:,} ({cycles:,} cycling): "
          f"max entries {best['entries']}, max actives {best['actives']}, "
          f"max deep/period {best['deep']}, "
          f"max transient alternations {best['pre_alt']}, "
          f"max cycle alternations/period {best['cyc_alt']}", flush=True)
    return best, examples


def show(tag, ex):
    comp, m, r0, e0, transient, cycle = ex
    print(f"  {tag}: cells {comp} bar {m} r0 {r0} e0 {e0}")
    print(f"    transient {transient} cycle {cycle}")


def main():
    t0 = time.perf_counter()
    star2 = [1, 0]
    comps2 = [c for S in (2, 4, 6)
              for c in itertools.product(range(1, S), repeat=2)
              if sum(c) == S]
    b2, ex2 = sweep(2, star2, comps2, "C=2 S<=6")

    star4 = [1, 0, 3, 2]
    comps4 = [c for S in (4, 6, 8)
              for c in itertools.product(range(1, 4), repeat=4)
              if sum(c) == S]
    b4, ex4 = sweep(4, star4, comps4, "C=4 S<=8")

    for b, ex in ((b2, ex2), (b4, ex4)):
        if b["actives"] > 2:
            show("ACTIVES>2 (refutes lemma B!)", ex["actives"])
        if b["pre_alt"] > 1:
            show("TRANSIENT ALT>1 (weakens lemma C!)", ex["pre_alt"])

    random.seed(1)
    best = dict(entries=0, actives=0, deep=0, pre_alt=0)
    exr = {}
    star6 = [1, 0, 3, 2, 5, 4]
    for _ in range(200000):
        comp = [random.randint(1, 3) for _ in range(6)]
        S = sum(comp)
        if S % 2:
            comp[0] += 1
            S += 1
        cellOf = []
        for c, n in enumerate(comp):
            cellOf += [c] * n
        perm = list(range(S))
        random.shuffle(perm)
        bar = list(range(S))
        for i in range(0, S, 2):
            a, b = perm[i], perm[i + 1]
            bar[a], bar[b] = b, a
        slots_of = [[i for i in range(S) if cellOf[i] == c] for c in range(6)]
        r0 = [random.choice(s) for s in slots_of]
        e0 = random.randrange(S)
        transient, cycle = run(cellOf, star6, bar, r0, e0)
        if cycle is None:
            continue
        ent, act, deep, pa, ca = analyze(cellOf, star6, transient, cycle)
        for key, val in (("entries", ent), ("actives", act),
                         ("deep", deep), ("pre_alt", pa)):
            if val > best[key]:
                best[key] = val
                exr[key] = (tuple(comp), sorted(
                    (a, bar[a]) for a in range(S) if a < bar[a]),
                    tuple(r0), e0, transient, cycle)
    print(f"[C=6 random 200k] max entries {best['entries']}, "
          f"max actives {best['actives']}, max deep {best['deep']}, "
          f"max transient alternations {best['pre_alt']}", flush=True)
    if best["actives"] > 2:
        show("ACTIVES>2 (refutes lemma B!)", exr["actives"])
    if best["pre_alt"] > 1:
        show("TRANSIENT ALT>1 (weakens lemma C!)", exr["pre_alt"])
    print(f"total {time.perf_counter()-t0:.0f}s")


if __name__ == "__main__":
    main()
