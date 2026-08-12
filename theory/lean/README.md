# Formal proofs (Lean 4): the state law

**The state law is proved.**  A single train on any `N`-switch lazy-point
layout visits at most `N + 6` distinct tongue vectors:

```
GeneralN.stateLaw : StateLaw            -- KnownEdgeNAddFiveAlt.lean
```

where `StateLaw` (`StateLaw.lean`) is the raw statement over
`Wiring`/`stepN` — for every wiring `w` on switches `0 … N-1`, every start
configuration, and every duplicate-free list of live sample times, the
sampled restricted tongue vectors number at most `N + 6`.  The proof is
fully symbolic in `N`: no small-`N` enumeration, no conditional
hypothesis, no Mathlib, no `native_decide`, no `sorry`.

Two hundred and twenty-four libraries, all self-contained; every file in
this directory is part of the proof's import closure (plus the two
auxiliary files noted below).  To check everything:

```
lake build                      # builds all 224 libraries
lake build StateLawAxiomAudit   # prints the axioms of GeneralN.stateLaw
```

`StateLawAxiomAudit.lean` runs `#print axioms` on the theorem; the output
is exactly `[propext, Classical.choice, Quot.sound]` — the three standard
Lean axioms.  The `state-law-check` workflow repeats both steps on every
push.

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

## Shape of the proof

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
* `StateLawAxiomAudit.lean` — the permanent axiom check described above.

## What remains open

The conjectured sharp form is `f(N) = min(2^N, N + 4)`; the proved
constant is `N + 6`.  The gap is purely additive: one candidate vector in
the arbitrary-start lift and one in the protected-repair tail.  A
matching parametric lower-bound family achieving `N + 4` (the small-`N`
witnesses above realize it for `N = 3, 4`) is the other half.

## History

This proof is the end of a bound-tightening campaign
(`26N+3 → 24N+5 → 18N+3 → 17N+5 → 15N+7 → 14N+9 → 8N+7 → 5N+9 → 3N+7 →
2N+9 → N+7 → N+6`).  The full 391-library development — including the
superseded linear-bound stages and the echo-machine/four-beat-law
program aimed at the sharp constant — is preserved in git history;
commit `2b75dd8` is the last state before this cleanup.
