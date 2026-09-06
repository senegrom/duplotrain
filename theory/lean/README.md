# Formal proof (Lean 4): the state law

**The theorem.** On `N` lazy-point switches the maximum number of distinct
switch settings a single train can visit is exactly

```
f(N) = min(2^N, N + 4).
```

The headline theorem is in `StateLaw.lean`:

```
GeneralN.state_law :
    ∀ N, IsExactStateCount N (min (2 ^ N) (N + 4))
```

`IsExactStateCount N count` says `count` is the exact maximum: every run
on every `N`-switch wiring samples at most `count` pairwise-distinct
restricted tongue vectors, **and** some wiring, start, and list of live
sample times attains `count`. The theorem is unconditional; `N = 0` is
witnessed by the empty wiring.

## Checking the proof

The toolchain is pinned in `lean-toolchain`; no Mathlib is required.

```
lake build StateLawAxiomAudit  # the headline theorem and its dependencies
lake build                    # every library in the tree
```

`StateLawAxiomAudit.lean` checks the exact `#print axioms` output with
`#guard_msgs`, then prints it for CI:

```
'GeneralN.state_law' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An added axiom therefore fails the build, not just a visual inspection.
The finite computations use kernel `decide`, never `native_decide`.
The workflow builds and audits on relevant pushes to `main` and pull requests.

## The model

A switch `k` owns ports `3*k` (stem), `3*k+1` (left), and `3*k+2` (right).
A wiring is a symmetric partial pairing of ports. Self-links are allowed
in this abstract model. Every linked endpoint is below `3*N`.

A configuration `(p, u)` records the entry port and all tongue directions.
Entering a stem follows its selected branch without changing the tongue;
entering a branch sets the tongue to that branch and exits the stem.
`step` then follows the outgoing track edge. An absent edge ends the run.
`stepN` iterates this rule, and `VectorCount.restrict N u` reads the first
`N` tongue directions. The theorem counts distinct vectors at live sample
times, not distinct train positions or elapsed steps.

## Upper bound: complete the wiring and keep time zero

The `2^N` ceiling is `state_law_two_pow` in `StateLawSmallN.lean`: the
restricted vectors are length-`N` Boolean lists.

The substantial dynamical result is the known-incoming-edge `N+4` bound,
derived from `ProtectedPairNAddFour.lean`. Its internal entry point now
assumes a bounded **total** wiring: every port below `3*N` has a partner.
Its construction-history and pointwise reflector arguments remain the
core of the proof, but both `N+1`-step exploration probes are automatically
live. The former dead-probe classification is unnecessary.

`StateLawNAddFourSharp.lean` reduces arbitrary starts and partial wirings
to this setting using `WiringCompletion.lean`:

1. Complete every free port below `3*N` with the self-link `p -> p`.
   Symmetry is preserved because no old edge can point to a free port.
   All existing links and initial tongue values remain unchanged; no
   switch is added.
2. Every live configuration of the original run is unchanged in the
   completion. Induct on the number of steps: each successful original
   step uses an existing edge, which has been preserved.
3. For an in-range start, symmetry supplies an incoming edge in the total
   completion. Apply the total-wiring bound and transfer the identical
   sample vectors back, at exactly their original sample times.
4. An out-of-range start cannot make a live first step: its outgoing port
   lies on that same out-of-range switch and cannot be linked. Thus only
   time zero can contribute, giving at most one vector.

The reusable lemma `stepN_preserved_by_wiring_extension` deliberately makes
no assertion that termination is preserved: the completion may continue
where the old run ended. Only originally live samples are transferred.

**No extra time-zero charge or totality assumption is added to the headline
theorem.** Totality is proved for the comparison wiring, not imposed on the
original one. This is an upper-bound comparison within the abstract model,
not a claim that a physical unwired end already acts as a reversing cap.

Completing just the starting port was the first reduction. Completing all
free ports additionally removes `OneReflectorSecondDead` and the general
eventual-periodicity detour that was used only to exclude dead continuations.
The pointwise cycle and repair facts still used for state counting remain.

## Protected pair: one history, two budgets

The next reduction is inside the known-incoming-edge proof, in
`ProtectedPairNAddFour.lean`. Let `A` be the first manufactured reflector
and `B` the opposite second reflector. Once the old paths are grooved at
both endpoints of `B`'s construction, use just the canonical history
`A.preservedTwoHistoryCore B N` in every branch.

For a stay reflector `A`, that history has at most `N+2` entries and the
repair tail has at most two fresh vectors. For a flip reflector, inspect
its action coordinate (the tongue it flips on reflection):

* **Absent from `B`'s productive first writers:** the coordinate is outside
  both the old reusable support and the new writers. Reserving it saves one
  history entry, again giving at most `N+2`, with at most two fresh tail vectors.
* **Present among those writers:** the history has at most `N+3` entries.
  Writing that coordinate causes a constant-tongue retrace to the second
  construction's start; switch simplicity forces it to be the last productive
  writer. Its pre-write state recovers a nominally fresh corner of the final
  Gray-square motion, so the repair tail adds at most one fresh vector.

Thus the arithmetic is `(N+2)+2 = (N+3)+1 = N+4`. The earlier split between
"first productive writer" and "an earlier writer exists" is unnecessary.
The doubly-erased history and its separate coverage and counting lemmas
have been removed. The existing generic tail lemmas work directly with the
same history, including the boundary configurations.

### One reservation lemma instead of repeated coordinate counting

`TwoHistoryUnionCharge.lean` now proves a common coordinate certificate:
the old reusable switches and `B`'s productive first-writer switches form
a duplicate-free list below `N`. `ReservedHistoryCharge.lean` appends any
duplicate-free list of reserved switches disjoint from that list, obtaining

```
old reusable coordinates + new productive writers + reserved coordinates <= N.
```

The zero-, one-, and two-reservation counts reuse that certificate rather
than independently reproving injectivity, disjointness, and the ambient bound.
The remaining reservation interfaces are used by the active proof.

### Endpoint agreement controls every intermediate state

`PhysicalTrace.prefix_coordinate_eq_endpoint` in `TrackTrace.lean` is a
small general observation: on a switch-simple trace, each intermediate
tongue value is either its starting value or its finishing value. Split
the trace at that intermediate point. Switch simplicity means a coordinate
cannot occur in both halves. The half not containing it preserves its value.

Consequently paths grooved at both endpoints stay grooved at every
intermediate configuration. `OneReflectorContinuation.lean` packages that
consequence as `PhysicalTrace.pathGrooves_at_prefix_of_endpoints`.
Two repeated contradiction proofs in the protected-pair and changed-contact
arguments now use this direct lemma. The new facts require neither a finite
switch bound nor extraction of a later productive writer.

## Selected-route fault analysis: one stem/branch split

`TrackThetaPointwiseCore.lean` now treats a disturbed traversal using the
single selected outward route (`orientedRoute`). Every retained support
passage appears on that route in the orientation the train actually takes.
Switch simplicity puts the disturbed coordinate at one unique contact.
Before it, the route is grooved and avoids that coordinate, so the original
and disturbed runs have the same ports and differ only at that coordinate.

Only two local cases remain, for either a flip or a stay reflector:

* **Stem entry:** the contact is the first reflector's mouth. Its existing
  capture law returns the disturbed run to the boundary, restoring the
  flipped tongue. Prepending the constant prefix creates no new phase.
* **Branch entry:** the lazy-point rule pins the tongue to the entering
  branch, repairing the fault. Both runs reach the same configuration after
  that step. Determinism then makes their configurations equal at every
  subsequent time, even beyond the reference route.

The reusable theorem `PhysicalTrace.trailing_fault_merges` states that last
synchronization explicitly. There are no separate runway, forward-candy,
and reverse-candy repair/capture proofs. The generic
`ManufacturedReflector.support_fault_dichotomy_pointwise` specializes directly
to flip/flip and flip/stay contacts, without adding a finite-switch or
totality assumption to the local theorem.

## Boundary invariants instead of explicit contact periods

For the all-time contact covers, it is enough to supply a positive-length
excursion from each allowed boundary configuration to another allowed
boundary configuration, with every intermediate tongue vector in the
claimed cover. `stepN_covered_of_progress` proves the general statement by
strong induction on the queried time. A query inside an excursion uses its
cover; a later query subtracts a strictly positive duration and continues
from the next invariant boundary. Neither eventual periodicity nor a finite
boundary set is required by this general lemma.

For mutual flip/flip contact, write `uA = flipAt u A.actionSwitch` and
`uB = flipAt u B.actionSwitch`. The boundary invariant consists of

```
(g,u), (e,uA), (g,uB), (e,u).
```

Normal traversals connect `(g,u)` to `(e,uA)` and `(e,u)` to `(g,uB)`.
From `(e,uA)`, the fault theorem either captures to `(e,u)` or repairs to
`(g,uB)`; the opposite disturbed traversal either captures to `(g,u)` or
repairs to `(e,uA)`. Each excursion exposes only `u`, `uA`, or `uB`.
Captures have positive length because time zero cannot restore a genuinely
flipped tongue. This proves the three-vector cover directly, without the
previous case-specific lead and period calculations.

The one-sided contact proof uses two boundary configurations and a four-vector
cover. The flip/stay proof uses three boundary configurations and a two-vector
cover. Ordinary periodicity results still needed elsewhere are retained;
this removes the contact-specific period construction, not every use of
periodicity from the development.

## Capture is a suffix of ordinary traversal

Start an ordinary flip-reflector traversal with its action tongue flipped.
The runway is still grooved because that action coordinate is outside its
support. After the runway, the run is exactly at the mouth in the disturbed
state. The remainder is therefore the capture run; the ordinary traversal's
second flip restores the original tongue vector. The endpoint capture law
and its pointwise two-phase law now follow by removing this unchanged
runway prefix. They no longer repeat the forward/reverse-arm analysis.

## Trim construction witnesses; do not reconstruct them

A manufactured reflector contains a recorded construction trace, but its
ordinary traversal theorem works in **any** state satisfying its support
grooves. These are different roles: the witness's original tongue states
need not equal the later state in which the reflector is used.

To cut off a runway prefix, `PhysicalTrace.suffix_after_passage` extracts
the original suffix and its recorded initial tongue state. The shorter
reflector reuses the original mouth, candy, terminal states and crossing
proof. Switch simplicity passes to the suffix, and its support is a subset
of the old support. Hence it remains grooved in the later state, and avoids
the discarded switch. Both flip and stay witnesses use this construction;
there is no need to reorient the candy or rebuild its terminal crossing.

The same principle removes redundant nil/nonempty path cases. Ordinary
runway replay is `PhysicalTrace.replay_grooved`. Reverse candy traversal,
reverse arbitrary lobes, and the final reverse-runway return all reuse
`physicalTrace_contact_retraces_prefix`. That theorem now follows directly
by induction on the recorded trace: reverse the tail, then prepend its
original head in reverse. Empty paths are handled once by the base case.

Finally, a split at a passage not in a runway must lie after the runway.
`split_after_prefix_of_not_mem` proves this as a plain list fact, without
switch simplicity or coordinate-counting machinery. Applied to the selected
outward route, it removes separate forward/reverse-candy cases from the
facing-approach contradiction and the remaining-tail foreignness proof.
Neither the old unique-key-split proof nor the separate linked-list retrace
construction is required any longer.

## Dependency and source reductions

The transitive local-source closure of `StateLaw` includes the theorem's
own module but excludes the separate audit module. Source lines count
comments and blanks, not just proof tactics.

| Stage | Modules | Source lines |
| --- | ---: | ---: |
| Before the capping reduction (`392ae27`) | 65 | 27,846 |
| After capping (`2e928b6` has the same proof) | 56 | 25,882 |
| After the shared-history and endpoint reductions | 53 | 24,104 |
| After deleting what left the closure | 52 | 23,706 |
| After total-wiring completion | 52 | 21,342 |
| After selected-route, boundary-invariant and suffix-capture reductions | 52 | 19,841 |
| After witness trimming and trace reuse | 52 | 19,175 |

The second pass removes a further **1,778 lines** from this dependency
closure (3,742 cumulatively). `ProtectedPairNAddFour.lean` itself decreases
from **2,068 to 1,587 lines**. These are smaller arguments and cleaner
imports, not merely whitespace compression or a change to the theorem.
The substantial trace/reflector classification still remains; this is not
a replacement of the whole upper bound by a one-paragraph proof.

The total-completion pass removes another **2,364 Lean source lines**,
net of its new completion module. The module count stays unchanged because
`WiringCompletion` replaces the now-unused `TraceRetainingFirstRevisit`.

The selected-route, boundary-invariant, and suffix-capture pass removes a
further **1,501 Lean source lines**, including the cost of its new generic
lemmas. That candidate had **19,860 total Lean lines** including the 19-line audit.
Witness trimming and trace reuse remove a further **666 lines**, leaving
**19,194 lines** in 53 files. The accumulated reduction from the reviewed
`b10aadd` baseline of 23,725 lines is **4,531 lines**. Counts include all new
helper proofs, comments and blank lines, not just deleted code.

Two small modules (`StateLawBounds` and `ReservedHistoryCharge`) hold the
shared statements and counting facts that the removed modules previously
supplied transitively.

The fifteen modules the two reductions took off the import path have been
deleted, along with the declarations inside retained modules whose only
users were in them. The tree contains the headline theorem, its local import closure, and the
separate axiom audit. The total-completion reduction additionally removes
the obsolete trace-retaining dead-probe wrapper. Git history holds the
superseded proofs.

`StateLaw.lean`, the `2^N` ceiling, the attainment construction, the wiring
model, and the exact axiom audit are unchanged. No `sorry`, additional
axiom, or `native_decide` is introduced by these reductions.

## Attainment: unchanged

For `N = 0`, the empty wiring attains one vector. For `N = 1, 2`, the
teardrop and dogbone attain `2^N` (`StateLawSmallN.lean`, kernel `decide`).
For `N >= 3`, the bound is `N+4`. `StateLawLowerBound.lean` constructs a
teardrop, a branch-to-stem chain, and a doubly linked pair. Its symbolic
phase inductions prove liveness and pairwise-distinctness of the chosen
sample vectors; the `N = 3` base case uses kernel `decide`.

## History

The bound-tightening campaign reached

```
26N+3 -> 24N+5 -> 18N+3 -> 17N+5 -> 15N+7 -> 14N+9
-> 8N+7 -> 5N+9 -> 3N+7 -> 2N+9 -> N+7 -> N+6 -> N+5 -> N+4.
```

Commit `2b75dd8` is the last state before the earlier cleanup of historical
libraries. The capping and shared-history reductions were added on
6 September 2026; the superseded modules were deleted the same day.
