# Consolidated upper-bound proof work

Branch: `agent/upper-bound-current`

This branch combines the strongest unconditional quantitative proof with the
current coefficient-one programme. It contains the complete source artifacts
from the active upper-bound branches, with a focused workflow checking their
compatibility in one tree.

## Unconditional theorem on this branch

The branch contains the kernel-checked coefficient-two proof:

```text
known incoming edge:  2*N + 6
arbitrary start:       2*N + 7
```

The final source endpoint is `theory/lean/StateLawTwoSharper.lean`.

## Coefficient-one target

The current programme targets:

```text
known incoming edge:  N + 5
arbitrary start:       N + 6
```

The exact residual is the raw theorem that at most four globally novel
repeated-writer events occur after entering through a known physical edge.

## Coefficient-one proof knowledge included here

* `TripleSelfLinkSimpleCycleTail.lean` closes the stable-simple-cycle half of
  the selected self-link raw-cycle obstruction.
* `CoefficientOneSeven.lean` proves the exact conditional payoff of the
  remaining sharp six-event residue:

```text
residue impossible => known-edge N+6 => arbitrary-start N+7
```

* `NoveltyChargeBound.lean` shows that a compatible pair adds only three new
  Gray corners because its initial corner is already historical.
* `SharpSixFinal.lean` removes the direct-lobe pure-support-crossing leaf from
  the six-event residue.
* `ShrinkingCurveFinal.lean` proves well-founded termination of strict
  old-contact subcurve recursion.

## Imported results from the other active agent branch

The following unique files from `codex/first-repeated-edge-proof` are also
preserved on this branch:

* `EchoRawBridgeSharp.lean`: extends a finite valid echo prefix to an abstract
  infinite echo run without assuming an infinite physical train trajectory,
  and transfers registers, tokens and finite repertoire bounds exactly.
* `EmptyCurvePotential.lean`: develops a global curve/stem potential; non-self
  productive pivots strictly grow the train-curve stem set while self pivots
  cannot increase it.
* `MellitDynamicResidual.lean`: retains exact transient and stable traces for
  the immediate two-phase simple-cycle branch instead of erasing them into a
  bare eventual-periodicity statement.
* `StateLawParametricAudit.lean`: symbolically rules out the naive direct
  double-sweep counterfamily for arbitrary `N`; repeated productive pairs
  force an intervening write.
* `TwoHistoryUnionCharge.lean`: charges the two opposite construction
  histories once and isolates the first concrete old-support contact when the
  union cannot be paid from a single switch budget.

The detailed proof map and correctness policy are in:

```text
theory/lean/COEFFICIENT_ONE_STATUS.md
```

The branch workflow `.github/workflows/upper-bound-current-check.yml` checks:

1. the unconditional `2*N+7` endpoint;
2. the selected-self-link simple-cycle closure and conditional coefficient-one
   arithmetic; and
3. all five imported proof-knowledge modules listed above.

## Remaining coefficient-one work

The remaining global work is concentrated in:

1. converting the forced early self-link into a replay or bounded tail;
2. closing the serial five-frame case while preserving the consecutive-event
   window; and
3. eliminating the residual strict-nest/support-contact placements.
