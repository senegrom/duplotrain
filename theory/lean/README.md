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
lake build                    # all 68 retained libraries, including the old boundary route
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

## Upper bound: keep time zero instead of shifting it

The `2^N` ceiling is `state_law_two_pow` in `StateLawSmallN.lean`: the
restricted vectors are length-`N` Boolean lists.

The substantial dynamical result is the known-incoming-edge `N+4` bound:
`knownIncomingEdgeNAddFour`, derived from `ProtectedPairNAddFour.lean`.
It applies to every initial tongue assignment whenever the starting port
has an incoming edge. Its construction-history and reflector arguments
remain the core of the proof.

The reduction from arbitrary starts is now much simpler. It is implemented
in `StateLawNAddFourSharp.lean`:

1. If the starting port `p` is wired, symmetry supplies the incoming edge.
   Apply the known-edge theorem to the original run and original sample times.
2. If `p < 3*N` is unwired, add only the self-link `p -> p`. No other port
   could previously point to `p`, by symmetry, so the extended wiring is
   still symmetric and still uses only the same `N` switches.
3. Every live configuration of the original run is unchanged in the
   extended wiring. Induct on the number of steps: each successful original
   step uses an existing edge, and those edges are unchanged. The new cap
   can affect the run only where the old run would end. Apply the known-edge
   theorem to the extension and transfer the identical sampled vectors back.
4. If the starting port is outside the first `N` switches, its outgoing
   port is on that same switch and cannot be linked. Only time zero can be
   live, contributing at most one vector.

The key reusable lemma is `stepN_preserved_by_wiring_extension`: extending
a wiring preserves every configuration reached before the original run
ends. It deliberately makes no claim about the continuation after death.

**There is no extra time-zero charge.** Neither the start nor the sample
times are shifted, no switch is added, and the theorem statement is unchanged.
The former productive-boundary saturation proof is no longer required.

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
One- and two-reservation interfaces remain available to the older proof.

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

## Dependency and source reductions

The transitive local-source closure of `StateLaw` includes the theorem's
own module but excludes the separate audit module. Source lines count
comments and blanks, not just proof tactics.

| Stage | Modules | Source lines |
| --- | ---: | ---: |
| Before the capping reduction (`392ae27`) | 65 | 27,846 |
| After capping (`2e928b6` has the same proof) | 56 | 25,882 |
| After the shared-history and endpoint reductions | 53 | 24,104 |

The second pass removes a further **1,778 lines** from this dependency
closure (3,742 cumulatively). `ProtectedPairNAddFour.lean` itself decreases
from **2,068 to 1,587 lines**. These are smaller arguments and cleaner
imports, not merely whitespace compression or a change to the theorem.
The substantial trace/reflector classification still remains; this is not
a replacement of the whole upper bound by a one-paragraph proof.

Five more historical modules leave the headline theorem's import path:
`StateLawNAddFourTop`, `StateLawTwoSixUltra`, `BoundaryNAddFourSaturation`,
`BoundaryAbsentSecondWriter`, and `BoundaryDoubleDuplicate`. Two small
modules (`StateLawBounds` and `ReservedHistoryCharge`) hold the shared
statements and counting facts they previously supplied transitively. Old
modules still compile, using compatibility imports where appropriate.
The earlier capping reduction had already bypassed nine other modules.

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
libraries. The capping reduction above was added on 6 September 2026.
The paper in `../paper/` describes the earlier upper-bound organisation;
this guide and the Lean sources describe the current shorter proof.
