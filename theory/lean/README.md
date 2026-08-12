# Formal proofs (Lean 4): the state law

**The state law is proved, from both sides.**  A single train on any
`N`-switch lazy-point layout visits at most `N + 6` distinct tongue
vectors, and for every `N ≥ 3` there is a layout on which it visits
`N + 4`:

```
GeneralN.stateLaw              : StateLaw   -- KnownEdgeNAddFiveAlt.lean
GeneralN.state_law_lower_bound              -- StateLawLowerBound.lean
```

where `StateLaw` (`StateLaw.lean`) is the raw statement over
`Wiring`/`stepN` — for every wiring `w` on switches `0 … N-1`, every start
configuration, and every duplicate-free list of live sample times, the
sampled restricted tongue vectors number at most `N + 6`.  The lower
bound produces, for every `N ≥ 3`, a wiring on switches `0 … N-1`, a
start configuration, and `N + 4` live sample times whose tongue vectors
are pairwise distinct.  Both proofs are fully symbolic in `N`: no
small-`N` enumeration, no conditional hypothesis, no Mathlib, no
`native_decide`, no `sorry`.  (The lower bound's `N = 3` base case is
checked by kernel `decide`; `N ≥ 4` is the symbolic trajectory.)

Two hundred and twenty-six libraries, all self-contained; every file in
this directory is part of the proofs' import closure (plus the auxiliary
files noted below).  To check everything:

```
lake build                      # builds all 226 libraries
lake build StateLawAxiomAudit   # prints the axioms of both theorems
```

`StateLawAxiomAudit.lean` runs `#print axioms` on both theorems; the
output is exactly `[propext, Classical.choice, Quot.sound]` — the three
standard Lean axioms.  The `state-law-check` workflow repeats both steps
on every push.

## How to read the statement

* A **wiring** `w` is a track layout: switch `k` owns three ports — its
  stem `3*k`, its left branch `3*k+1`, its right branch `3*k+2` — and
  `w.link` records which port is track-connected to which (symmetric,
  because physical track is).
* `hN` says the layout uses only switches `0 … N-1`.
* `stepN` drives the single train one track-piece at a time under the
  **lazy-point rule**: entering a switch at its stem follows the tongue
  unchanged; entering at a branch always exits at the stem and, if the
  tongue pointed at the other branch, flips it.
* `tonguesAt`/`restrictedTonguesAt` read off the `N` tongue directions at
  a given time — the *tongue vector*, the machine state of the layout.

## Shape of the lower bound

`StateLawLowerBound.lean` wires the extremal family symbolically: switch
`0` is a teardrop (branches tied, stem wired to switch `1`'s stem),
switches `1 … N-3` form a branch-to-stem chain, and switches
`N-2, N-1` are doubly linked (branch1–stem and branch2–branch2).  A cold
run started into branch 2 of switch `N-2` flips the chain down to the
teardrop — one fresh vector per switch — rides back, closes the far
switch, and then walks a four-corner Gray oscillation on switches `N-2`
and `0`.  The `N + 4` sample times are
`0, 1, …, N-2, N, 2N-1, 2N, 3N-1, 4N-1`; the trajectory is proved by
phase inductions, and pairwise distinctness by explicit witnessing
coordinates.

## Shape of the upper bound

The core theorem (`known_edge_all_run_distinct_le_N_add_five`) bounds
every run whose incoming physical edge is known by `N + 5`, with no
liveness horizon: wherever the run dies, the samples so far are covered
by the same histories.  Its branches — first death, settling on a stable
cycle, a completed opposite-reflector pair, and an arbitrary first
support-damage — are all charged into **one shared `N`-coordinate
construction history**, and in the formerly limiting protected-pair
branch both the activated state and the pre-return state are already
historical, so the four-state repair tail contributes at most two fresh
vectors.  Lifting an arbitrary start past its first successful step costs
at most the time-zero vector: `N + 6`.

The supporting layers, bottom to top: the raw track dynamics and
first-revisit normal forms (`TrackTrace`, `TrackLobe`,
`TrackNormalForm`, `TrackTheta`); manufactured reflectors, their repairs
and quantitative lassos (`TrackGlobalRepair`, `TrackQuantitative*`);
pointwise tongue-phase laws — every traversal shows two phases, every
capture two, every repairing traversal three, every reflector pair four
corners, protected repair prefixes two
(`ManufacturedPairNovelty`, `TrackThetaPointwiseCore`,
`TrackThetaAllTime`, `RepairLeadTwoPhase`, `TrackStayContactAllTime`,
`TrackStaySpliceAllTime`); constant tongue counts for every repair
branch (`*Constant`, `*Count*`, `ProtectedRepair*`); and the history
assemblies that share one `N`-coordinate budget across branches
(`TwoHistoryUnionCharge`, `StateLawTwoSixUltra`,
`StateLawCoefficientOneTop`, `KnownEdgeNAddFiveAlt`).

## Auxiliary files

* `DuplotrainProofs.lean` — the exhaustive small-`N` results (by
  `native_decide`, deliberately outside the symbolic proof): the exact
  state counts `f(1) = 2`, `f(2) = 4`, `f(3) = 7`, `f(4) = 8`, the
  perfect-layout classification, and the ≥3-switch imperfection sweep.
  These are the empirical anchors of the remaining conjecture.
* `FamilyLowerBound.lean` — `native_decide` instances of the same
  family for `N = 3 … 8`, checking the *exact* maximum: over all starts
  the family realizes exactly `N+4` distinct vectors (the symbolic
  theorem only exhibits `N+4`; these instances confirm the family
  itself does no better).  Discovered and cross-checked by
  `../tools/bstates.py`; a 60,000-wiring random probe at `N = 5` found
  nothing above `N+4`.
* `StateLawAxiomAudit.lean` — the permanent axiom check described above.

## What remains open

The conjectured sharp form is `f(N) = min(2^N, N + 4)`; the proved
bounds are `N + 4 ≤ f(N) ≤ N + 6` for every `N ≥ 3` (exhaustively
sharp at `N + 4` for `N ≤ 4`).  The remaining gap is exactly the two
additive units in the upper bound, and the extremal family explains
where they must close: the optimal runs spend exactly `N` vectors on
chain exploration and four on the terminal Gray oscillation, so the two
candidate savings are the arbitrary-start lift's time-zero vector and
the slack pair in the protected-repair tail.

## History

This proof is the end of a bound-tightening campaign
(`26N+3 → 24N+5 → 18N+3 → 17N+5 → 15N+7 → 14N+9 → 8N+7 → 5N+9 → 3N+7 →
2N+9 → N+7 → N+6`).  The full 391-library development — including the
superseded linear-bound stages and the echo-machine/four-beat-law
program aimed at the sharp constant — is preserved in git history;
commit `2b75dd8` is the last state before this cleanup.
