# Coefficient-one proof frontier

Branch: `agent/upper-bound-current`

This branch contains both the strongest unconditional bound and the current
coefficient-one source programme.

## Unconditional kernel-checked baseline

The source endpoint `StateLawTwoSharper.lean` proves:

```text
known incoming edge:  f_edge(N) <= 2*N + 6
arbitrary start:       f(N)      <= 2*N + 7
```

The consolidated workflow recompiles that endpoint on this branch.

## Final coefficient-one target

The preferred raw statement is:

```lean
def KnownEdgeFourRepeatedWriterNovelty : Prop :=
  forall (w : Wiring) (N e : Nat),
    (forall p q, w.link p = some q -> p < 3*N /\ q < 3*N) ->
    forall (start : Nat × Tongues) (K : Nat),
      w.link e = some start.1 ->
      (rawRepeatedWriterNovelTimes w N start K).length <= 4
```

The existing counting bridge would then give:

```text
known incoming edge:  N + 5
arbitrary start:       N + 6
```

## Intermediate coefficient-one theorem

`CoefficientOneSeven.lean` isolates the exact payoff of the canonical
six-event reduction. It defines `IncomingSharpSixEventResidueImpossible` as
the sole open geometric premise and proves:

```lean
knownEdgeFiveRepeatedWriterNovelty_of_sharpSixEventResidueImpossible
knownEdge_distinct_le_N_add_six_of_fiveRepeatedWriterNovelty
stateLawNAddSeven_of_sharpSixEventResidueImpossible
```

Therefore, once the displayed sharp six-event residue is impossible:

```text
known incoming edge:  N + 6
arbitrary start:       N + 7
```

This is conditional, not an unconditional replacement for `2*N + 7`.

## Closed local mechanisms

The branch ancestry formalises the following facts.

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
7. Strict old-contact recursion terminates because both residual supports are
   strict tracked subcurves.

## Stable simple-cycle closure

`TripleSelfLinkSimpleCycleTail.lean` closes the stable-simple-cycle half of
the selected self-link raw-cycle branch. Its theorem chain is:

```lean
rawTwoVectorTail_of_stable_simple_cycle_exact
RawCycleThroughSelfLink.close_tail_of_simple_cycle_trace_exact
RawSixEventReduction.tail_simple_cycle_false
RawSixEventReduction.tail_cycle_self_link_false
CertifiedEndpointEmptyABCABC.tail_self_link_endpoint_is_early
```

The proof packages a grooved stable cycle as an all-time one-vector tail,
uses `RawTwoVectorTail.rotate_back_to_period_base_exact` to rotate it to the
selected raw close, and invokes the literal five-close four-cover theorem.
Thus the later raw-cycle self-link alternative is impossible; any selected
self-link must occur at an actual early raw time inside the endpoint window.

## Six-event residue reductions already completed

`SharpSixFinal.lean` eliminates the direct-lobe pure-support-crossing leaf.
`MellitDirectSharpAssembly.lean` retains exact first-revisit and old-contact
geometry. `ShrinkingCurveFinal.lean` proves the well-founded rank decrease of
old-contact subcurves. These are structural reductions, not a hidden claim
that the remaining residue is empty.

## Remaining global bridges

### Early self-link

Convert the forced early self-link into either a complete-state replay or a
manufactured two-/four-vector tail before the later selected closes.

### Serial five-frame case

A serial break yields an exact completed caller retrace and a rebased later
novel frame. The missing well-founded argument must preserve the no-gap
consecutive-event window while decreasing the earliest outstanding close.

### Strict nest or residual support contact

Any remaining strict nest or changed-forward support contact must be routed
to the existing finite Gray/tail laws rather than charged by physical path
length.

## Correctness policy

* A theorem is called kernel-checked only after the branch workflow is green
  for a commit containing it.
* Conditional residue implications remain labelled conditional.
* Physical travel length and tongue-vector novelty are never interchanged.
* Self-linked ports are handled explicitly; no hidden `IrreflexiveLinks`
  assumption is used.
* A global tail theorem must cover the literal selected raw post-close times,
  not merely macro endpoints or eventual periods.
