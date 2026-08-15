# Formal proofs (Lean 4): the sharp state law

**The state law is sharp.** A single train on any `N`-switch lazy-point
layout visits at most `N + 4` distinct tongue vectors. For every `N ≥ 3`
there is a layout on which it visits exactly `N + 4`; the exact small values
are `f(1) = 2` and `f(2) = 4`. Together with the finite-state ceiling this
gives

```
f(N) = min(2^N, N + 4)       (N ≥ 1).
```

Headline theorems:

```
GeneralN.state_law_N_add_four             -- StateLawNAddFourSharp.lean
GeneralN.knownIncomingEdgeNAddFour        -- KnownEdgeNAddFourComplete.lean
GeneralN.productiveInitialBoundaryNAddFour -- StateLawNAddFourSharp.lean
GeneralN.state_law_lower_bound            -- StateLawLowerBound.lean
```

The raw upper-bound statement (`StateLawNAddFour.lean`) is over
`Wiring`/`stepN`: for every wiring `w` on switches `0 … N-1`, every start
configuration, and every duplicate-free list of live sample times, the
sampled restricted tongue vectors number at most `N + 4`. The proof is fully
symbolic in `N`: no finite-instance argument, no Mathlib, no `native_decide`,
and no `sorry`. The lower bound is also symbolic for `N ≥ 4`; its `N = 3`
base case is checked by kernel `decide`.

There are 149 self-contained Lean libraries. To check everything:

```
lake build
lake build StateLawAxiomAudit
```

`StateLawAxiomAudit.lean` runs `#print axioms` on the headline theorems. The
sharp upper bound depends only on `[propext, Classical.choice, Quot.sound]`,
the three standard Lean axioms, and not on `sorryAx`. The
`state-law-check` workflow repeats the full build and audit on every push to
`main`.

## How to read the statement

* A **wiring** `w` is a track layout: switch `k` owns three ports — its stem
  `3*k`, left branch `3*k+1`, and right branch `3*k+2` — while `w.link`
  records the symmetric physical track connection.
* `hN` says the layout uses only switches `0 … N-1`.
* `stepN` drives the train one track piece at a time under the lazy-point
  rule: entering at a stem follows the tongue unchanged; entering at a
  branch exits at the stem and flips the tongue when necessary.
* `tonguesAt` / `restrictedTonguesAt` read the `N` tongue directions at a
  given time — the machine state of the layout.

## Lower bound

`StateLawLowerBound.lean` wires the extremal family symbolically. Switch `0`
is a teardrop; switches `1 … N-3` form a branch-to-stem chain; and switches
`N-2, N-1` are doubly linked. A cold run flips the chain down to the
teardrop, rides back, closes the far switch, and then walks a four-corner
Gray oscillation on switches `N-2` and `0`.

The `N + 4` sample times are

```
0, 1, …, N-2, N, 2N-1, 2N, 3N-1, 4N-1.
```

Their trajectory is proved by phase inductions and their pairwise
distinctness by explicit witnessing coordinates.

## Upper bound

The known-incoming-edge core (`knownIncomingEdgeNAddFour`) already bounded
every shifted run by `N + 4`. Its death, stable-cycle, support-changing
contact, and protected-reflector-pair branches are charged into one shared
`N`-coordinate construction history.

The only remaining issue was an arbitrary productive first passage: could
its time-zero vector be genuinely new on top of the shifted known-edge
budget? `BoundaryResidualSharpening.lean` reduced that question to four
constructors. The new closing files eliminate all four:

* `BoundaryApproachActionElimination.lean` proves that a strict simple
  approach from the boundary stem cannot first-write the boundary switch.
  If it first-writes the old flip action instead, the tail has only one new
  corner, so the reserved boundary coordinate still yields `N + 3`.
* `BoundaryApproachWrittenElimination.lean` packages that charge to rule out
  the complete approach-written residual.
* `BoundaryAbsentPresentWriterElimination.lean` proves that the second
  manufacture, which also starts at the boundary stem, cannot productively
  first-write that switch. This kills the absent-present writer residual.
* `BoundaryOccurrenceDamageElimination.lean` handles both remaining support
  damage cases. A canonical unchanged occurrence forces a self-linked first
  reflector whose future has only two action phases, so a global `N+3`
  history contradicts saturation. A noncanonical occurrence gives two
  duplicate positions in the first manufacturing journey; the double-reduced
  boundary history has exactly the ordinary compressed lead's length but also
  contains the arbitrary time-zero vector. The existing zero/two/one-novelty
  changed-contact classification therefore fits time zero inside `N + 4`.

`StateLawNAddFourSharp.lean` combines these eliminations with
`productiveInitialBoundaryNAddFour_iff_no_sharp_residual`, then applies the
exact arbitrary-start wrapper from `StateLawNAddFourTop.lean`.

## Auxiliary files

* `DuplotrainProofs.lean` exhaustively checks `f(1) = 2` and
  `f(2) = 4` — the two legs of `min(2^N, N + 4)` below the symbolic
  family's reach.  These finite results deliberately use
  `native_decide`; they are separate from the symbolic proofs.
  (`f(3) = 7` and `f(4) = 8` follow from the symbolic bounds and need
  no exhaustion.)
* The `N+6` assembly (`GeneralN.stateLaw`, `KnownEdgeNAddFiveAlt.lean`)
  remains in the tree — not for history, but because the sharp
  protected-pair closure genuinely builds on it.

## Independent open directions

The sharp state-count law itself is closed. The echo-machine programme in
`../lazy-point-theory.md` still contains open Gray-tail and transient lemmas;
those would provide a different proof and stronger structural information,
but are no longer needed for the `N + 4` bound.

## History

The bound-tightening campaign is now complete:

```
26N+3 → 24N+5 → 18N+3 → 17N+5 → 15N+7 → 14N+9
→ 8N+7 → 5N+9 → 3N+7 → 2N+9 → N+7 → N+6 → N+5 → N+4.
```

The superseded stages and the echo-machine/four-beat-law programme remain
available in git history; commit `2b75dd8` is the last state before the large
cleanup of those historical libraries.
