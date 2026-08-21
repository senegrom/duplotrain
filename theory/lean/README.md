# Formal proof (Lean 4): the state law

**The theorem.** On `N` lazy-point switches the maximum number of distinct
switch settings a single train can visit is exactly

```
f(N) = min(2^N, N + 4).
```

There is one headline theorem, in `StateLaw.lean`, and everything else in
this directory exists to support it:

```
GeneralN.state_law :
    ∀ N, IsExactStateCount N (min (2 ^ N) (N + 4))
```

`IsExactStateCount N count` (same file) says `count` is the exact maximum:
every run on every `N`-switch layout samples at most `count`
pairwise-distinct restricted tongue vectors, **and** some layout, start,
and duplicate-free list of live sample times attains `count`.  The theorem
is unconditional — `N = 0` is witnessed by the empty layout.

To check everything (70 self-contained libraries, no Mathlib):

```
lake build
```

The build ends with `StateLawAxiomAudit.lean` printing `#print axioms`
for the theorem.  Expected output: exactly `[propext, Classical.choice,
Quot.sound]`, the three standard Lean axioms — no `sorryAx`, no
`Lean.ofReduceBool` (the few finite checks use kernel `decide`, never
`native_decide`).  The `state-law-check` workflow repeats the build and
audit on every push to `main`.

## How to read the statement

* A **wiring** `w` is a track layout: switch `k` owns three ports — its
  stem `3*k`, left branch `3*k+1`, and right branch `3*k+2` — while
  `w.link` records the symmetric physical track connection.  The bound
  `p < 3 * N` says the layout uses only switches `0 … N-1`.
* `stepN` drives the train one track piece at a time under the lazy-point
  rule: entering at a stem follows the tongue unchanged; entering at a
  branch exits at the stem and flips the tongue when necessary.  A `none`
  step means the train fell off an unconnected end; liveness asks each
  sampled time to still be on the track.
* `VectorCount.restrict N u` reads the `N` tongue directions — the machine
  state of the layout; `Nodup` makes the sampled vectors pairwise
  distinct.

## Proof shape

**Upper half** — `ks.length ≤ min(2^N, N+4)` is two bounds:

* `state_law_two_pow` (`StateLawSmallN.lean`): the finite-state ceiling.
  Restricted vectors are length-`N` boolean lists; their binary values are
  distinct naturals below `2^N`.  Fully symbolic, no liveness needed.
* `state_law_N_add_four` (`StateLawNAddFourSharp.lean`): the sharp
  symbolic `N + 4` bound — the mathematical core of the development.
  The known-incoming-edge theorem (`KnownEdgeNAddFourComplete.lean`)
  bounds every shifted run by charging its death, stable-cycle,
  support-changing contact, and protected-reflector-pair branches into one
  shared `N`-coordinate construction history.  The remaining question — an
  arbitrary productive first passage adding a genuinely new time-zero
  vector — is reduced to one saturated saving residual, which
  `BoundaryResidualSharpening.lean` eliminates using
  `BoundaryApproachActionElimination.lean` and
  `BoundaryOccurrenceDamageElimination.lean`.

**Attainment half** — a layout reaching the value for every `N`:

* `N = 0`: the empty layout (`StateLawSmallN.lean`).
* `N = 1, 2`: the `2^N` leg binds.  A one-switch teardrop visits both
  states; the two-switch dogbone walks the full Gray square
  `FF → TF → TT → FT` (`StateLawSmallN.lean`, kernel `decide`).
* `N ≥ 3`: the `N + 4` leg binds.  `StateLawLowerBound.lean` wires the
  extremal family symbolically: switch `0` is a teardrop, switches
  `1 … N-3` a branch-to-stem chain, switches `N-2, N-1` doubly linked.
  A cold run flips the chain, rides back, closes the far switch, and
  walks a four-corner Gray oscillation; the `N + 4` sample times
  `0, 1, …, N-2, N, 2N-1, 2N, 3N-1, 4N-1` are proved live and pairwise
  distinct by phase inductions.  (Symbolic for `N ≥ 4`; the `N = 3` base
  case is kernel `decide`.)

## History

The bound-tightening campaign that ended in the sharp constant:

```
26N+3 → 24N+5 → 18N+3 → 17N+5 → 15N+7 → 14N+9
→ 8N+7 → 5N+9 → 3N+7 → 2N+9 → N+7 → N+6 → N+5 → N+4.
```

The superseded stages remain in git history; commit `2b75dd8` is the last
state before the large cleanup of the historical libraries.
