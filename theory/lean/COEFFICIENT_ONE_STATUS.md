# Upper-bound proof frontier

Branch: `agent/coefficient-one-current`

This is the visible working branch for the coefficient-one programme. It
preserves source-level proof knowledge even when a theorem has not yet been
assembled into the public `GeneralN.StateLaw` endpoint.

## Verified quantitative baseline

The strongest unconditional theorem currently kernel-checked in the
repository is on branch `agent/push-below-5`:

```lean
GeneralN.known_edge_long_run_distinct_le_two_sharp
GeneralN.state_law_linear_two_sharp
```

with bounds

```text
known incoming edge:  f_edge(N) <= 2*N + 6
arbitrary start:       f(N)      <= 2*N + 7
```

The independent branch `codex/first-repeated-edge-proof` contains another
unconditional coefficient-two proof, ending in `StateLawTwoSharp.lean`, with
bound `2*N + 8`. Its local novelty lemmas remain useful for the
coefficient-one programme even though its final additive constant is weaker.

## Coefficient-one target

The target raw novelty statement is:

```lean
def KnownEdgeFourRepeatedWriterNovelty : Prop :=
  forall (w : Wiring) (N e : Nat),
    (forall p q, w.link p = some q -> p < 3*N /\ q < 3*N) ->
    forall (start : Nat × Tongues) (K : Nat),
      w.link e = some start.1 ->
      (rawRepeatedWriterNovelTimes w N start K).length <= 4
```

The existing counting bridge turns this into

```text
known incoming edge:  N + 5
arbitrary start:       N + 6
```

without any further asymptotic loss.

## Closed local mechanisms

The branch ancestry already formalises the following facts.

1. A compatible manufactured-reflector pair has a four-corner Gray cover.
2. The initial Gray corner is historical at the completed first turnaround,
   so the pair contributes only three additional novelty vectors.
3. A direct-lobe opposite pair is automatically compatible; the apparent
   support intersection is physically impossible.
4. A selected self-link is an exact two-step identity reflector.
5. An opposite reflector paired with that self-link has an all-time
   two-vector tongue cover.
6. The selected `ABCABC` fixed-entry alternative is placed inside the raw
   selected window, rather than merely somewhere in the certified run.

## Simple-cycle closure on this branch

`TripleSelfLinkSimpleCycleTail.lean` closes the other first-revisit outcome of
the selected self-link raw cycle. Its theorem chain is:

```lean
rawTwoVectorTail_of_stable_simple_cycle_exact
RawCycleThroughSelfLink.close_tail_of_simple_cycle_trace_exact
RawSixEventReduction.tail_simple_cycle_false
RawSixEventReduction.tail_cycle_self_link_false
CertifiedEndpointEmptyABCABC.tail_self_link_endpoint_is_early
```

The argument is:

* a stable switch-simple cycle is grooved and therefore carries one tongue
  vector throughout each lap;
* periodic extension packages it as a `RawTwoVectorTail`;
* `RawTwoVectorTail.rotate_back_to_period_base_exact` moves the tail back to
  the selected raw closing configuration;
* `five_close_noveltyCoverOn_four_of_two_vector_tail` gives the forbidden
  literal four-vector cover of the five selected post-close vectors.

The focused workflow `.github/workflows/coefficient-one-current-check.yml`
builds this theorem chain directly. A green run is the verification marker;
source presence alone is not treated as kernel verification.

## Remaining global bridges

After the simple-cycle closure, the coefficient-one proof is concentrated in
three global placement problems.

### Early self-link

The certified triple obstruction can now only expose a self-link at an actual
raw time between the third selected opening and the first selected close.
This early bounce must be turned directly into either a complete-state replay
or a manufactured two-/four-vector tail before enough later novelty closes
occur.

### Serial five-frame case

A serial break gives an exact completed caller retrace and a rebased later
novel last-writer frame. The missing theorem must prevent indefinite serial
iteration while retaining the remaining consecutive novelty events. The
preferred invariant is a well-founded decrease in the earliest outstanding
closing time together with preservation of the no-gap event window.

### Strict-nest or residual support contact

The `ABCABC` branch has been reduced to the self-link endpoint above. Any
remaining strict nest or changed-forward support contact must be converted to
the already proved three-/four-vector tail rather than charged by physical
path length.

## Correctness rules

* No theorem is described as verified until its focused Lean workflow is
  green for the commit containing it.
* Conditional certificate theorems are labelled conditional.
* Physical travel bounds and tongue-vector novelty bounds are kept separate.
* Self-linked external ports are handled explicitly; no hidden
  `IrreflexiveLinks` assumption is permitted.
* Every global tail claim must cover the literal selected raw post-close
  times, not merely macro endpoints or an eventual period.
