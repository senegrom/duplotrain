# Upper-bound proof frontier

Branch: `agent/coefficient-one-current`

Latest visible verified checkpoint:

```text
commit: 786672497c2975c51166f66240ef26ef8ddc68ff
workflow run: 31507568011
conclusion: success
```

This is the working branch for the coefficient-one programme. It preserves
source-level proof knowledge even when a theorem has not yet been assembled
into the public `GeneralN.StateLaw` endpoint.

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

## Bound ladder

There are now two exact coefficient-one milestones.

### Six-event milestone

`CoefficientOneSeven.lean` proves, conditionally on the single raw geometric
proposition `IncomingSharpSixEventResidueImpossible`, that

```text
known incoming edge:  N + 6
arbitrary start:       N + 7
```

The kernel-checked bridge is:

```lean
KnownEdgeFiveRepeatedWriterNovelty
knownEdgeFiveRepeatedWriterNovelty_of_sharpSixEventResidueImpossible
knownEdge_distinct_le_N_add_six_of_fiveRepeatedWriterNovelty
StateLawNAddSeven
stateLawNAddSeven_of_sharpSixEventResidueImpossible
```

This is the closest coefficient-one bound because the repository already has
a canonical reduction from six repeated-writer novelties to one explicit raw
residue.

### Five-event milestone

The sharp target is:

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
7. A selected strict nest is paid by strong induction on its raw closing
   time; no recursive strict-nest residue survives once the selected-close
   provenance is retained.

## Simple-cycle and trace-retention closure on this branch

`TripleSelfLinkSimpleCycleTail.lean` closes the first-revisit cycle outcome of
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

A second information-loss problem was then removed. `SettlesOnSimpleCycle`
records only two period endpoint equations and does not retain the physical
lap. The following additional theorems now kernel-check:

```lean
PhysicalTrace.first_revisit_trace_or_activated_reflector
rawExactLobeWrite_second_repeat_cycle_traces_or_pair
ReachedStableSimpleCycle
reachedStableSimpleCycle_of_prefix
ReachedStableSimpleCycle.one_vector_tail
```

The generic first-revisit theorem retains the transient and stable
switch-simple traces. The BABA second-repeat theorem propagates those traces
through the exact direct-lobe construction, while preserving the original
opposite-reflector branch. `ReachedStableSimpleCycle.one_vector_tail` converts
the absolute trace witness into an explicit all-time one-vector suffix.

The focused workflow `.github/workflows/coefficient-one-current-check.yml`
builds these theorem chains and directly checks `CoefficientOneSeven.lean`.
The GitHub Actions step summary displays the checked theorem names and the
conditional quantitative payoff.

## Exact six-event frontier toward `N+7`

`SharpSixEventAssembly.lean` packages every alleged six-event counterexample
as `RawSharpSixEventResidue`. `SelectedTripleSharpClosure.lean` then strengthens
that residue:

* strict nesting is fully paid by well-founded selected-close descent;
* a selected `ABCABC` triple becomes an overlap-minimal physical BABA;
* the BABA is reduced to the explicit `RawBABAChargeReplayClosure` leaves;
* the serial/serial alternative retains two actual completed caller returns
  and strictly rebased later novelty frames.

The remaining proof of `IncomingSharpSixEventResidueImpossible` should be an
eliminator over those two top-level forms.

### Selected BABA leaves

The current physical leaves are:

* a reached stable simple cycle, now with exact physical traces and an
  all-time one-vector tail;
* a direct opposite pair reached after the first selected close;
* an early pure support crossing;
* an interior direct lobe;
* a first-writer charge;
* a quiet interval paid entirely by first writers; or
* a least quiet replay frame.

The assembly task is to transport their covers to the literal list

```lean
[z1 + 1, z2 + 1, z3 + 1, z4 + 1, z5 + 1]
```

and contradict `RawSharpSixEventResidue.noTailFourCover`. For the cycle leaf,
the remaining issue is now only timing: count how many selected post-close
vectors precede the start of the stable lap. The tongue-state geometry itself
is closed. Escaping finite segments and productive outer gaps already come
with strict recursion data.

### Serial/serial leaf

The serial branch provides exact completed caller retraces and suffix rebasing.
The needed recursion measure is not path length. It is the earliest
outstanding selected close, together with preservation of the consecutive
six-event/no-gap window. A successful recursive step must either consume one
selected close as historical or return a strictly smaller residue carrying
the remaining selected events.

## Additional saving needed for `N+6`

The six-event route can establish at most five repeated novelties and hence
`N+7` from an arbitrary start. To obtain `N+6`, one must rule out five
repeated novelties. The five-frame obstruction has no second overlapping
window, so it loses the strongest serial/serial comparison used by the
six-event proof.

The most plausible one-vector saving is already visible locally:

```text
first turnaround contact = initial Gray corner of the following pair
```

Consequently the pair costs three new vectors, not four. A sharp five-frame
proof must force every support-intersection/serial branch into a tail where
that historical starting corner is retained. Equivalently, it needs either:

1. `KnownEdgeFiveFrameRunwayExtraction`, placing a changed-forward tail before
   the second close; or
2. a direct proof that one of the five repeated-novel post-vectors is paid by
   first-writer history or by the initial Gray corner.

## Prospects below `N+6`

A global `N+5` bound would require at most three repeated-writer novelty
vectors after a known edge, or another universal historical overlap. Nothing
currently proves such a saving. A global `N+4` bound would additionally need
to remove the arbitrary time-zero surcharge or sharpen the first-writer
history itself. These remain conjectural directions, not established
consequences of the present machinery.

## Correctness rules

* No theorem is described as verified until its focused Lean workflow is
  green for the commit containing it.
* Conditional certificate theorems are labelled conditional.
* Physical travel bounds and tongue-vector novelty bounds are kept separate.
* Self-linked external ports are handled explicitly; no hidden
  `IrreflexiveLinks` assumption is permitted.
* Every global tail claim must cover the literal selected raw post-close
  times, not merely macro endpoints or an eventual period.
