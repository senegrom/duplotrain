# Exact-arithmetic and search-lifetime performance review — 18 September 2026

Baseline: `b7a37cb57fb2ba48c637a5c8935bd897ec425246`.
This baseline already includes alternating endpoint probes and retained reverse
reachability tables. Those earlier improvements are not attributed to this pass.

## Changes

`Alg` skips zero additions/subtractions/negations and multiplication by zero or
one; multiplication by minus one uses negation. Because values are immutable,
identity operations can safely return an operand. Scalar coercion, canonical
Fraction coefficients, hashing and equality remain unchanged.

When both operands lie in `Q(sqrt3)`, multiplication evaluates just the two
nonzero coefficient formulas. The general four-coefficient product remains for
`Q(sqrt2, sqrt3)`, including custom 15-degree and 45-degree geometry. There is no
floating-point approximation or extra cache.

Exact rotations by 0, 90, 180 and 270 degrees swap/negate coordinates instead of
performing field products. Other headings retain the exact sine/cosine formulas.
The existing rotation-table lookup still validates integer indices before taking
a shortcut, so whole-number float step arguments remain rejected as before.

The recursive DFS function previously retained itself through a closure cell,
keeping its collision workspace alive after a search returned until cyclic garbage
collection. Its existing `finally` block now clears that self-reference after the
stack unwinds, including on callback errors. Deliberately retained reachability
tables still survive; their ownership and cache keys are unchanged. No explicit
`gc.collect()` or GC-policy changes are added to the application.

## Measurements

The existing `benchmarks/editor_completion.py` now also reports process CPU time
and a SHA-256 of the ordered exact layouts, signatures, gaps, kinds and exactness
flags. Hash construction and independent candidate audits are outside timing.
It can be run unchanged against either checkout by setting `PYTHONPATH`.

The table below uses seven fresh-process runs per checkout on the same native
CPython 3.13.5 environment. Runs alternate old/new and new/old ordering. Each run
executes the same eight-case suite with `--repeats 1`, default garbage collection,
26 added pieces, eight requested results and zero slop. No tests or profilers run
concurrently. Values are median wall seconds, not browser, iPhone, network or
startup timings. The finite box contains the original layout plus precisely
16 curves, four straights, two ramps and two spans.

| Case | Nodes, unchanged | Previous seconds | New seconds |
|---|---:|---:|---:|
| Half circle | 0 | 0.0134 | 0.0107 |
| Winding circle | 0 | 0.0654 | 0.0366 |
| Mixed gap | 138 | 0.1283 | 0.1118 |
| Half-built bridge | 0 | 0.0230 | 0.0130 |
| Reported finite, forward | 1,742 | 0.3025 | 0.3036 |
| Reported finite, reverse | 718 | 0.2042 | 0.2001 |
| Reported unlimited, forward | 1,878 | 0.3875 | 0.3633 |
| Reported unlimited, reverse | 854 | 0.2938 | 0.2664 |

Winding and half-built-bridge cases use about 44% less time; the default reported
unlimited case uses about 6% less and its reverse about 9% less. The finite forward
case is effectively unchanged (0.4% slower in this sample); this is not a universal
speed-up. Absolute timings vary with allocation and GC history. All runs retain
identical per-case ordered solution hashes, node counts and added-piece counts.
Both orientations and inventories of the reported gap still find eight exact
24-piece completions. Every candidate is independently audited for unchanged base
placements/links, exact joints and whole-layout collisions.

A separate lifetime diagnostic disables cyclic GC and keeps only weak references
to collision fields, then runs three reported-gap searches. The old implementation
retains 3, 6 and 9 fields after successive calls; the new implementation retains
0, 0 and 0. A collection releases the old fields, so this is delayed reclamation,
not a permanent leak. Tests also retain result objects and table dictionaries to
ensure neither needs to own these workspaces. Retained exception tracebacks can
intentionally keep stack frames alive and are not covered by that release claim.

## Validation and limits

Eighty added regressions compare all coefficient masks, sparse/dense and large
rational operands, zero/one identities, immutability and hashes, all 24 headings,
invalid rotation arguments, both solver arithmetic engines, exact and forced fits,
and reversing closures against full reference formulas. Fully exhausted small
searches retain the same solutions and every non-timing counter. Workspace tests
cover normal exhaustion, node/piece limits, cached-table reuse, bridge portfolios,
and filter/progress callback failures.

Local validation: 1,672 Python tests passed (`not slow and not browser`, 23
cases deselected), 73 JavaScript tests passed, compileall and whitespace checks
passed. Ruff and Chromium/WebKit integration tests are delegated to CI, not
claimed as local results.

No dependency, new cache, search budget/order, bridge-clearance threshold, collision
predicate, UI contract or saved-layout format changes. This does not implement a
resumable search or add a minimum-piece guarantee.
