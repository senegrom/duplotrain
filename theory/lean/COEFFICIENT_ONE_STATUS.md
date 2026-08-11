# Coefficient-one state-bound checkpoint

Branch: `agent/coefficient-one-current`

## Kernel-checked result

The self-link **raw-cycle** residual in the selected `ABCABC` five-frame obstruction is closed.

The checked theorem chain is:

- `rawTwoVectorTail_of_stable_simple_cycle_exact`
- `RawCycleThroughSelfLink.close_tail_of_simple_cycle_trace_exact`
- `RawSixEventReduction.tail_simple_cycle_false`
- `RawSixEventReduction.tail_cycle_self_link_false`
- `CertifiedEndpointEmptyABCABC.tail_self_link_endpoint_is_early`

A stable switch-simple cycle gives an all-time one-vector tail, represented through `RawTwoVectorTail`. The tail is rotated back to the selected raw close and yields the forbidden four-vector cover of the five selected post-close vectors. The opposite-reflector branch was already closed, so a self-link arising on a later raw cycle is impossible. Consequently the certified triple obstruction must expose the self-link at an actual raw time inside the selected window.

## Bound status

The strongest unconditional theorem currently verified in the repository remains:

- arbitrary start: `2 * N + 7`
- known incoming edge: `2 * N + 6`

The coefficient-one target `N + 6` is **not yet proved**. The remaining work is global placement rather than local novelty arithmetic:

1. turn the now-forced early self-link into an immediate replay or a bounded manufactured tail; and
2. finish the serial five-frame runway extraction / support-intersection placement.

The workflow `.github/workflows/coefficient-one-current-check.yml` compiles the theorem chain on every relevant push.
