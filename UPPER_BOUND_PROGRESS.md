# Unified upper-bound proof work

Branch: `agent/upper-bound-unified`

This branch is the visible integration point for all active upper-bound work.
It now contains the coefficient-two proof, the coefficient-one obstruction
programme, the trace-retaining self-link/cycle closures, and the latest Codex
continuation lemmas in one repository tree.

## Strongest kernel-checked unconditional bound

The current verified endpoint is

```text
known incoming edge:  2*N + 4
arbitrary start:       2*N + 5
```

The public theorems are:

```lean
GeneralN.known_edge_all_run_distinct_le_two_mul_add_four
GeneralN.state_law_linear_two_add_five
```

in:

```text
theory/lean/StateLawTwoFive.lean
```

GitHub Actions run `31517925947` kernel-checked the complete endpoint chain,
including:

```text
StateLawTwoSharper
CodexStateLawTwoSharp
TwoHistoryUnionChargeLegacy
MellitFiveNoveltyAssembly
StateLawTwoFive
```

The workflow later failed in a separate continuation target, after the
`2*N+5` step had completed successfully.  That continuation import has since
been repaired.

## How the `2*N+5` theorem is assembled

For a run starting beyond a known incoming edge, the first-repeat split has
three substantive branches.

1. A dead second suffix is bounded by `2*N+2`.
2. A simple-cycle second suffix is bounded by `2*N+4`.
3. Two completed manufactured journeys use the sharper joint-history theorem
   `ManufacturedReflector.two_journeys_all_run_distinct_le_N_add_six`, giving
   `N+6` rather than charging two independent `N`-sized histories.

For `N >= 2`, all three branches are at most `2*N+4`; `N = 0,1` use the exact
`2^N` finite-state theorem.  An arbitrary start contributes at most its
unshifted time-zero vector, giving `2*N+5`.

## Imported continuation compression

`theory/lean/OneReflectorContinuation.lean` develops the next coefficient-one
accounting step.  It charges an old reflector's reusable support coordinates
and the productive first writers of a subsequent support-preserving
switch-simple continuation to the same set of `N` switch coordinates.

Its intended sharp endpoints are:

```text
one reflector + support-preserving fall:         N + 2
one reflector + simple lead + one-vector cycle:  N + 3
```

The module's missing manufacturing-endpoint import has been fixed at commit
`78e43524cc05966cf0c94576a840281910f6bed2`; the unified workflow is rerunning
it together with the rest of the branch.

## Coefficient-one milestones

### Conditional `N + 7`

`theory/lean/CoefficientOneSeven.lean` proves:

```text
sharp six-event residue impossible
  => known incoming edge: N + 6
  => arbitrary start:      N + 7
```

The implication is kernel-checked.  Its premise is the explicit remaining raw
six-event geometric residue, not a counting or periodicity assumption.

### Target `N + 6`

The sharper target is:

```text
known incoming edge:  N + 5
arbitrary start:       N + 6
```

It follows from proving that at most four globally novel repeated-writer
post-vectors occur after entry through a known physical edge.

## Integrated coefficient-one progress

### Pointwise simple-cycle and self-link tails

The branch contains the green trace-retaining modules:

```text
theory/lean/TraceRetainingFirstRevisit.lean
theory/lean/TraceRetainingBABASecondRepeat.lean
theory/lean/PointwiseSimpleCycleTail.lean
theory/lean/TripleSelfLinkSimpleCycleTail.lean
```

A reached same-exit simple cycle has one settled positive-time tongue vector.
The selected self-link periodic branch, in both its opposite-reflector and
stable-cycle outcomes, yields an explicit two-vector raw tail that rotates
back to the selected close.

### First old-support contact

The current contact calculus is in:

```text
theory/lean/TwoHistoryUnionCharge.lean
theory/lean/ContactHistorySharpBound.lean
```

Changing first contacts, and unchanged contacts which do not continue along
the old selected route, have a two-vector novelty cover over a history of
length at most `N+3`.

The unresolved aligned-forward branch has now been sharpened to an exact
physical residual:

```text
C.suffix = oldTail ++ extra
```

or the reverse prefix relation, together with the corresponding physical
trace and endpoint-state equality.  A fixed `N+3` contact history is probably
too rigid for the first case because `extra` may contain genuinely new first
writers.  The more robust route is to combine this residual with
`OneReflectorContinuation`: absorb those first writers into a larger but still
jointly charged history rather than incorrectly declaring them historical.

## Current proof frontier

The next local theorem should be a continuation-aware replacement for the
open fixed-history law.  A suitable target is:

```text
unchanged aligned forward contact
  => exists history, history.length <= N + 3 (or N + 4)
     and the complete continuation has a constant-size novelty cover
```

The proof should use:

1. the exact common-route decomposition from
   `SecondHistorySupportContact.facing_forward_residual_or_stable`;
2. the reusable-support/first-writer disjointness theorem from
   `OneReflectorContinuation`;
3. the pointwise constant or two-phase tail laws already proved for the
   terminal first-revisit outcomes.

Closing this local continuation charge would remove the most concentrated
obstruction to the `N+5` known-edge / `N+6` arbitrary-start target.

## Verification

The branch-local workflow is:

```text
.github/workflows/upper-bound-unified-check.yml
```

It registers every Lean source file and checks the unconditional endpoint,
the continuation compression, the coefficient-one reductions, the
trace-retaining cycle closures, and the imported structural modules in one
repository tree.
