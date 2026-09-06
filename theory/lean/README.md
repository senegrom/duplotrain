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
lake build                    # all 66 retained libraries, including the old boundary route
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

### Dependency reduction

Relative to `392ae27`, the transitive local-source closure of `StateLaw`
(including itself, excluding the separate audit module) changes as follows:

| Measure | Before | After |
| --- | ---: | ---: |
| Modules | 65 | 56 |
| Source lines, including comments and blanks | 27,846 | 25,882 |

Nine modules, totalling 2,047 lines, leave that dependency path; the new
wrapper adds 83 lines, giving a net reduction of 1,964 lines. This is a
simpler final reduction, not a replacement of the known-edge core by a
one-paragraph proof.

The following modules remain in the checkout for comparison and are still
checked by `lake build`, but `StateLaw` no longer imports them transitively:

```
BoundaryAbsentProtectedPair
BoundaryApproachActionElimination
BoundaryCanonicalGeometry
BoundaryChangedContactSaving
BoundaryOccurrenceDamageElimination
BoundaryResidualNovelty
BoundaryResidualSharpening
PartialSecondRunNAddFour
ProductiveBoundaryNAddFourComplete
```

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
this guide and the Lean sources describe the shorter arbitrary-start reduction.
