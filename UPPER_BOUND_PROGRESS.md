# Upper-bound proof work

Branch: `agent/coefficient-one-current`

This is the visible coefficient-one working branch.  Its focused GitHub
Actions workflow is green at commit
`f3a9d1daf9955a236e4755b1d70c7d6d5ce9af9a` (run `31505493091`).

## Current unconditional bound

The strongest unconditional theorem currently kernel-checked in the
repository is on `agent/push-below-5`:

```text
known incoming edge:  2*N + 6
arbitrary start:       2*N + 7
```

## Kernel-checked result on this branch

`theory/lean/TripleSelfLinkSimpleCycleTail.lean` closes the stable
simple-cycle half of the selected self-link raw-cycle obstruction.  Together
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

## Nearest coefficient-one bound: `N + 7`

`theory/lean/CoefficientOneSeven.lean` now kernel-checks the exact quantitative
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

The `N+7` milestone needs exclusion of six repeated novelties.  The sharper
`N+6` milestone needs exclusion of five repeated novelties, so it cannot use
the two overlapping five-event windows available in the six-event reduction.
It requires one additional historical-vector overlap or a direct five-frame
runway extraction.

## Remaining geometry

For the six-event route to `N+7`, strict nesting is already paid by
well-founded descent through selected close times.  The remaining work is:

1. convert the finite list of overlap-minimal BABA leaves—cycle, late pair,
   early pure crossing, direct lobe, first-writer charge and quiet replay—into
   the existing forbidden four-vector tail cover or a strictly smaller raw
   residue; and
2. close the serial/serial branch by a well-founded suffix argument that
   preserves the consecutive selected-event window.

For `N+6`, the preferred extra saving is the already visible Gray-corner
identity: the first-turnaround contact vector is the initial corner of the
following pair.  A complete five-frame proof must ensure that this overlap is
available in every global branch, not only the compatible/direct-lobe cases.

Detailed proof map and verification policy:

```text
theory/lean/COEFFICIENT_ONE_STATUS.md
```
