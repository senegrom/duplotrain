# Consolidated upper-bound proof work

Branch: `agent/upper-bound-current`

This branch combines the strongest unconditional quantitative proof with the
current coefficient-one programme. The merge commit retains both parent
histories rather than copying only a status note.

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

## New proof knowledge included here

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

The detailed proof map and correctness policy are in:

```text
theory/lean/COEFFICIENT_ONE_STATUS.md
```

The branch workflow `.github/workflows/upper-bound-current-check.yml` checks
both the unconditional theorem and the coefficient-one frontier.

## Remaining coefficient-one work

The remaining global work is concentrated in:

1. converting the forced early self-link into a replay or bounded tail;
2. closing the serial five-frame case while preserving the consecutive-event
   window; and
3. eliminating the residual strict-nest/support-contact placements.
