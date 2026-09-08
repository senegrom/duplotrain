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
proved by `known_edge_N_add_four` in `StateLawNAddFourSharp.lean`. Its entry point
assumes a bounded **total** wiring: every port below `3*N` has a partner.
Its construction-history and pointwise reflector arguments remain the
core of the proof, but both `N+1`-step exploration probes are automatically
live. The former dead-probe classification is unnecessary.

Both probes consume the same `first_revisit_fork`: a simple prefix followed
by a settled cycle, or a manufactured reflector with its activated grooves.
The former count-only and trace-retaining wrappers are unnecessary. A shared
settled-tail lemma charges the constant future vector once after any
historical prefix.

Productive histories cover every live prefix by induction: an unchanged step
keeps the previous vector, while a changed step contributes its post-vector.
A switch-simple trace has injective writer labels, so its productive steps
already have distinct writers. No first-writer predicate or search through
earlier times is needed.

`StateLawNAddFourSharp.lean` reduces arbitrary starts and partial wirings
to this setting by completing the wiring:

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
both endpoints of `B`'s construction, use `A.continuationHistory` through
that construction plus `B`'s activated vector in every branch.

The continuation needs no repair classification. Write `u = B.preReturn.2`,
`s = B.activatedState`, and let `a`, `b` be the local actions of `A`, `B`.
Both supports are grooved at `u`, and `b(u) = s`. The comparison run beginning
at `(e,u)` traverses `B` to reach the actual boundary `(g,s)`. Therefore every
live continuation sample inherits the pair theorem's four states:

```
u, s, a(u), a(s).
```

The first two are historical. An action writer also makes `a(u)` historical,
leaving just `a(s)` to charge. This is `ManufacturedReflector.preReturn_pair_corners`
in `PairActionCorners.lean`; it replaces the protected repair classification
and the separate facing, backward, and completed-route novelty arguments.

For a stay reflector `A`, all four corners are already historical, so the
generic `N+3` history bound suffices. For a flip reflector, inspect
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
have been removed. One pointwise cover passes through each manufacturing
journey in turn; it needs no separate shifted sample list or two-journey
counting theorem.

### One reservation lemma instead of repeated coordinate counting

`TwoHistoryUnionCharge.lean` counts the old reusable switches, the productive
first writers of any support-preserving simple trace, and any disjoint
duplicate-free list of reserved switches together:

```
old reusable coordinates + new productive writers + reserved coordinates <= N.
```

Both reflector construction and continuation use this same argument.
`continuationHistory_length_le` accepts an optional list of reserved
coordinates, sharing the erasure and size calculation across both uses.
The separate `ReservedHistoryCharge` module and specialized counting
wrappers have been removed.

The first construction history also omits a known duplicate sample directly:
the stay activation equals its pre-return sample, and a flip reflector's
facing-mouth passage preserves the tongue vector. This replaces the former
duplicate-multiplicity and value-erasure proofs while retaining every vector.

### Endpoint agreement controls every intermediate state

`PhysicalTrace.prefix_coordinate_eq_endpoint` in `TrackTrace.lean` is a
small general observation: on a switch-simple trace, each intermediate
tongue value is either its starting value or its finishing value. Induct
directly over the recorded trace. After the first step, its switch remains
fixed for the rest of the simple trace; every other coordinate keeps its
initial value at that step. No indexed split or intermediate-endpoint
identification is needed.

Consequently paths grooved at both endpoints stay grooved at every
intermediate configuration. `OneReflectorContinuation.lean` packages that
consequence as `PhysicalTrace.pathGrooves_at_prefix_of_endpoints`.
Two repeated contradiction proofs in the protected-pair and changed-contact
arguments now use this direct lemma. The new facts require neither a finite
switch bound nor extraction of a later productive writer.

## Selected-route fault analysis: one stem/branch split

`PairActionCorners.lean` treats a disturbed traversal using the
single selected outward route (`orientedRoute`). Every retained support
passage appears on that route in the orientation the train actually takes.
The shared first-contact theorem selects the first occurrence of the disturbed
coordinate; it does not require the entire reference route to be switch-simple.
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

The shared theorem `ManufacturedFlipReflector.grooved_route_fault` states
that synchronization explicitly, even for reference routes with repeated switches. There are no separate runway, forward-candy,
and reverse-candy repair/capture proofs. `ManufacturedReflector.pair_progress`
uses that synchronization directly to close the next boundary excursion,
without a separate support-fault wrapper or a finite-switch assumption.

## Boundary invariants instead of explicit contact periods

For the all-time contact covers, it is enough to supply a positive-length
excursion from each allowed boundary configuration to another allowed
boundary configuration, with every intermediate tongue vector in the
claimed cover. `stepN_covered_of_progress` proves the general statement by
strong induction on the queried time. A query inside an excursion uses its
cover; a later query subtracts a strictly positive duration and continues
from the next invariant boundary. Neither eventual periodicity nor a finite
boundary set is required by this general lemma.

One invariant handles every opposite manufactured pair. Its reference vector
`u` belongs to the four-corner orbit of the two commuting actions `a` and `b`,
and grooves both supports. The current vector is `u` or `b(u)` at the first
boundary, and `u` or `a(u)` at the second.

If the next reflector remains grooved, its normal traversal takes the current
vector as the new reference. Otherwise the previous action must be a flip.
The first support contact either captures back to `u`, or repairs the fault
and completes the next traversal from `u`. Each excursion has positive length,
stays in the four corners, and restores the same boundary invariant.

`ManufacturedReflector.pair_progress` supplies this argument in either direction;
`manufactured_pair_all_time_action_corners_tongues` closes it by strong induction.
The separate stay/flip, one-sided, and mutual-contact modules are removed.

## One invariant for the arbitrary lobe

A flip reflector opposite an arbitrary lobe now uses one invariant at the
reflector's outer boundary: the current vector grooves both supports and
belongs to their four-corner orbit. `explicit_lobe_route_at` selects the
current grooved orientation and certifies that it represents every interior
switch. This same certificate supplies normal traversal and first-contact
fault analysis.

If the old action avoids the selected route, both components traverse normally.
Otherwise capture restores the reference vector before an ordinary lobe
traversal, or repair synchronizes with that traversal. Both outcomes preserve
the boundary invariant, so no separate reverse-lobe excursion is needed.
`LocalAction.corners_closed` supplies the common corner-closure calculation
for the abstract, manufactured, and arbitrary-lobe pair arguments.

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

## Spatial-loop invariants replace the candy-splice case split

The strict candy splice has a stronger invariant than eventual periodicity.
After its new tongue is latched, the remaining spatial lap is the old candy
completion, reverse runway, fresh approach, and final splice contact. Only
the old reflector's action tongue can vary. The existing facing-approach
contradiction proves that the lap never enters that variable switch through
its stem. Branch entry may pin its tongue but cannot change the exit port;
all other passages remain grooved. Thus either value of the old action follows
the same spatial route and stays within the same two-vector family.

`PhysicalTrace.replay_preserving` in `TrackTrace.lean` replays any recorded
route in a passage-local tongue invariant. The recorded states serve only as
witnesses for the route's track links; they need not satisfy that invariant.
`PhysicalTrace.spatial_loop_invariant` repeats a positive-length spatial lap,
whose recorded endpoint tongues need not equal its starting tongues. It uses
`stepN_covered_of_progress`, now in the trace core, rather than a period.

`manufactured_flip_candy_splice_all_two_phases` applies this to the one-bit
family. It replaces the separate approach-foreign and approach-contact
branches, their endpoint constructions, settled-state proofs, and all-time
period reductions. `EventuallyPeriodic` and its remaining construction-only
helpers are no longer used and have been removed. This does not assert that
the full development is free of period arguments: other bounds still use them.

Manufactured pairs use the same progress principle with a reference corner
that grooves both supports. The current vector differs by at most the
previous action. This covers ordinary traversals, captures, and repairs in
one invariant, with shared algebraic closure of the four corners.

The general capture-phase law and the selected far-arm arrival fact are also
shared at their earliest required layer. Ordinary traversal now returns its
live configuration and incoming/outgoing-phase proof together. Mouth capture
uses this result on a suffix, removing the intermediate `tonguesAt` theorem
and the separate recovery of liveness.

## Arbitrary lobes use positive excursions

`explicit_lobe_two_phase_at` supplies the incoming/outgoing-vector contract
for an arbitrary mouth-free grooved lobe. Pin the current mouth tongue to the
recorded entry arm. The current vector equals that pinned vector or its mouth
flip; the forward and reverse recorded routes cover both cases. This works
for every current state grooving the interior, even when switches repeat.

A flip reflector opposite that lobe closes one four-corner boundary invariant
through ordinary traversal, capture, or repair. A stay splice needs only two
phases. Its excursion starts with the unchanged traversal of the old stay
suffix, followed by the lobe's one mouth flip. At a self-linked boundary the
prefix has length zero. In both cases the lobe makes the complete excursion
positive, and the same two-phase invariant repeats indefinitely. This removes
`SupportedReflector.pair_all_time_four_phase` and the self-pair construction.

For intersecting actions, `ManufacturedFlipReflector.grooved_route_fault`
selects the first contact on any grooved reference route. The prefix avoids
the disturbed coordinate. Stem entry captures and returns to the reference
boundary; branch entry repairs the bit and synchronizes the complete
configuration for every subsequent time. No restriction on later repetitions
is required. This replaces the separately coded arbitrary-lobe and
switch-simple contact analyses.

## First-arrival synchronization

The cycle cases use first-arrival synchronization: if `arrive u p = (x, v)`,
then `arrive v p = (x, v)` as well. Hence `stepN_after_arrival` identifies the
complete runs from `(p, u)` and `(p, v)` at every **positive** time. It makes no
claim that either run is globally constant. `PhysicalTrace.grooved_loop_all_time`
provides the latter fact when the post-arrival vector grooves a nonempty closed
spatial trace. Backward contacts and same-exit cycles combine these two facts:
time zero is the original vector; every positive time is the settled one. There
is no separate transient lap, stable period, or modulo-time proof. The pointwise
reverse-trace theorem uses the same first-arrival synchronization.

The endpoint-coordinate law also proves that a productive writer cannot agree
at the trace endpoints: its adjacent values would then both equal the common
endpoint value. The separate theorem for traces with one net changed coordinate
became unnecessary when the pre-return orbit replaced protected repair analysis.

## One lobe route supplies endpoint and pointwise laws

`stem_lobe_route` records a grooved outward route and its final mouth arrival.
Pinning the mouth to the recorded entry arm gives a reference state; any
current grooved state is that state or its mouth flip. The recorded route and
its reverse cover these two possibilities. Both `stem_lobe_isReflector_foreign`
and `explicit_lobe_two_phase_at` now consume this same spatial certificate,
removing the separate two-state endpoint and reverse-travel derivations.

The common replay, reverse-trace, and prefix lemmas now live in `TrackTrace`,
where both consumers can use them. `PhysicalTrace.reverse_grooved` supplies
both reflector return and contact retrace; the separate linked-path retrace
engine is removed. A single `passage_step` extraction supplies the local
geometry and finite-switch bounds. Grooved replay and prefix coverage are
instances of `PhysicalTrace.replay_preserving`. `reversePassages` uses list
reversal followed by endpoint swapping, so its algebra and source-membership
facts follow directly from the standard list operations.

## Settled cycles and fresh samples need less bookkeeping

The cycle alternative of `first_revisit_fork` now returns exactly the fact
needed downstream: every positive-time configuration has the settled tongue
vector. Its proof still constructs the grooved loop, then uses first-arrival
synchronization. Consumers no longer carry transient/stable cycle traces,
cycle simplicity, or a separate finite-window phase law. A prefix of length
at most `N` followed by that one vector gives the `N+2` count directly.

The pair tail now has a pointwise cover, so transporting sampled times needs
only liveness. Distinctness is used once, when converting the final cover to
a count; no boundary-subtraction count or duplicate-free suffix proof remains.

First-repeat detection grows a duplicate-free prefix until the next key is
already present. This removes the two repeated extraction arguments in the
former tail-first induction. Reflector pairs obtain liveness and their phase
cover together from the common boundary invariant; the explicit period
construction and its two iteration helpers are removed.

## Shared trace cuts and reflector transport

`PhysicalTrace.split_grooved_at` cuts a recorded path at a named passage
and replays both sides in the chosen grooved state. It handles empty and
nonempty prefixes uniformly, replacing the separate linked-prefix and
boundary-link derivations. `PhysicalTrace.after_prefix` fixes a suffix's
starting configuration by determinism. Prefix comparability now returns
its endpoint trace directly.

`PhysicalTrace.sandwich_reflector` transports either core reflector through
an arbitrary grooved runway. The shared arrival-geometry and groove-agreement
lemmas remove repeated local stem/branch algebra. The candy suffix uses one
return proof for either starting phase, and the lobe boundary invariant
composes its pointwise covers with `stepN_cover_append`.

Forward contacts carry only the selected exit direction: the later splice
construction derives its own return law, so the extra intermediate repair
state and its two unused certificates are removed from the contact interfaces.

## Shared chain traversals in the lower bound

`StateLawLowerBound.lean` uses one upward-chain lemma for both grooved
return trips, and one downward-chain lemma that writes the visited interval
and includes the final exit to the teardrop stem. The cold descent and the
later unchanged descent are instances of that same result. Including their
endpoints removes the separate last-step case from the initial sample block.
One-step phase composition shares the time arithmetic, while direct branch
and stem laws replace the separate arrival wrappers. The wiring, named
vectors, sample times, and coordinate witnesses for distinctness are unchanged.

## Size

The tree is the headline theorem, its local import closure, and the
separate axiom audit: 25 files and 5,977 source lines, including the
19-line audit. The closure of `StateLaw` alone has 24 modules and 5,958
lines. Source lines count comments and blanks, not just proof tactics.
Every public theorem lies in the headline proof's kernel dependency
closure. There is no `sorry`, no additional axiom, and no `native_decide`;
the finite computations use kernel `decide`. Git history holds the
superseded proofs.

## Attainment

For `N = 0`, the empty wiring attains one vector. For `N = 1, 2`, the
teardrop and dogbone attain `2^N` (`StateLawSmallN.lean`, kernel `decide`).
For `N >= 3`, the bound is `N+4`. `StateLawLowerBound.lean` constructs a
teardrop, a branch-to-stem chain, and a doubly linked pair. Its symbolic
phase inductions prove liveness and pairwise-distinctness of the chosen
sample vectors; the `N = 3` base case uses kernel `decide`.
