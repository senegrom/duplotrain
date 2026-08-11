# Upper-bound proof work

Branch: `agent/coefficient-one-current`

This is the visible coefficient-one working branch. Its focused GitHub
Actions workflow is green at commit
`786672497c2975c51166f66240ef26ef8ddc68ff` (run `31507568011`).

## Current unconditional bound

The strongest unconditional theorem currently kernel-checked in the
repository is on `agent/push-below-5`:

```text
known incoming edge:  2*N + 6
arbitrary start:       2*N + 7
```

## Kernel-checked results on this branch

### Selected self-link cycle closure

`theory/lean/TripleSelfLinkSimpleCycleTail.lean` closes the stable
simple-cycle half of the selected self-link raw-cycle obstruction. Together
with the already closed opposite-reflector half, this proves that the
self-link forced by the selected `ABCABC` obstruction cannot first appear on
a later periodic raw cycle: it must occur at an actual raw time inside the
selected window.

The checked theorem chain is:

```lean
rawTwoVectorTail_of_stable_simple_cycle_exact
RawCycleThroughSelfLink.close_tail_of_simple_cycle_trace_exact
RawSixEventReduction.tail_simple_cycle_false
RawSixEventReduction.tail_cycle_self_link_false
CertifiedEndpointEmptyABCABC.tail_self_link_endpoint_is_early
```

### Trace-retaining first revisit and BABA second repeat

The ordinary predicate `SettlesOnSimpleCycle` stores only period endpoints,
which is too weak for pointwise novelty accounting. The branch now contains
kernel-checked trace-valued replacements:

```lean
PhysicalTrace.first_revisit_trace_or_activated_reflector
rawExactLobeWrite_second_repeat_cycle_traces_or_pair
ReachedStableSimpleCycle
reachedStableSimpleCycle_of_prefix
ReachedStableSimpleCycle.one_vector_tail
```

These preserve the transient lap, the stable switch-simple lap and the exact
absolute raw reach. Consequently the cycle leaf of a Mellit/BABA second
repeat can be converted into an explicit all-time one-vector tail rather than
an unqualified eventual-periodicity statement.

## Nearest coefficient-one bound: `N + 7`

`theory/lean/CoefficientOneSeven.lean` kernel-checks the exact quantitative
payoff of the canonical six-event reduction:

```lean
knownEdgeFiveRepeatedWriterNovelty_of_sharpSixEventResidueImpossible
knownEdge_distinct_le_N_add_six_of_fiveRepeatedWriterNovelty
stateLawNAddSeven_of_sharpSixEventResidueImpossible
```

Thus proving the single raw geometric proposition
`IncomingSharpSixEventResidueImpossible` would immediately give

```text
known incoming edge:  N + 6
arbitrary start:       N + 7
```

This is a conditional bridge, not yet an unconditional improved bound.

## Sharp coefficient-one target: `N + 6`

The final target remains:

```text
known incoming edge:  N + 5
arbitrary start:       N + 6
```

It follows from `KnownEdgeFourRepeatedWriterNovelty`, the raw theorem that at
most four globally novel repeated-writer events occur after entering through
a known physical edge.

The `N+7` milestone needs exclusion of six repeated novelties. The sharper
`N+6` milestone needs exclusion of five repeated novelties, so it cannot use
the two overlapping five-event windows available in the six-event reduction.
It requires one additional historical-vector overlap or a direct five-frame
runway extraction.

## Remaining geometry

For the six-event route to `N+7`, strict nesting is already paid by
well-founded descent through selected close times. The remaining work is:

1. transport the now trace-valued BABA cycle leaf to the literal five selected
   post-close times, paying only those selected closes before the stable tail;
2. convert the other overlap-minimal BABA leaves—late pair, early pure
   crossing, direct lobe, first-writer charge and quiet replay—into the
   existing forbidden four-vector cover or a strictly smaller raw residue;
3. close the serial/serial branch by a well-founded suffix argument that
   preserves the consecutive selected-event window.

For `N+6`, the preferred extra saving is the already visible Gray-corner
identity: the first-turnaround contact vector is the initial corner of the
following pair. A complete five-frame proof must ensure that this overlap is
available in every global branch, not only the compatible/direct-lobe cases.

Detailed proof map and verification policy:

```text
theory/lean/COEFFICIENT_ONE_STATUS.md
```
