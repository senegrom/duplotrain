# The lazy-point cycle theorem: general-N structure

**Setting.** N switches, ports S/L/R each; a wiring pairs ports with edges
(plain-track paths) or caps them. Lazy-point dynamics: *facing* (enter S)
exits by the tongue and leaves it alone; *trailing* (enter branch X) sets the
tongue to X and exits S. Single forward train; fall mode (a capped edge ends
the run). All statements concern the *eventual cycle* of a run — caps are
never on a cycle in fall mode, and in reflect mode a bounce off a guarded cap
re-enters via the same branch it exited, re-pinning the same value, so the
lemmas below carry over.

A switch is **active** (on a cycle) if its tongue flips there; by periodicity
an active switch flips both ways. Distinct tongue vectors on a cycle with
`a` active switches number at most `2^a`, so the target theorem

> **Cycle theorem.** Every eventual cycle has at most 2 active switches,
> hence at most 4 distinct tongue vectors.

is reduced to bounding actives. Status: proved below for all N in every case
except one precisely isolated core, which T9 compiles — geometry and all —
into two lemmas (**B**, **C**) about a ten-line register machine.  Both are
verified exhaustively on the wiring side for N ≤ 4 (140,152 wirings, also
in Lean), unbeaten by cycle-objective search through N = 7, and verified
across every small machine exhausted so far (`docs/echo_machine.py`).
Modulo B + C the total state count obeys **f(N) ≤ N + O(1)**.

---

## T1 (Cascade pinning). *Between consecutive facing events the trajectory is
a deterministic cascade fixed by the wiring, and it pins every switch it
trails through to a wiring-determined constant.*

Proof. After a facing exit at (z, X) the train runs along the X-branch edge
of z. Arriving at a branch port of m it trails: sets t_m to that branch —
a constant of the wiring, not of the state — and exits S_m, whose single
edge determines the continuation. The cascade therefore visits a fixed
sequence of (switch, branch) pairs until it reaches a stem port (the next
facing event) or revisits a branch port (whereupon the run is trapped in a
pinned loop forever, with no further flips). ∎

Call the pair (z, X) an **arc**; its path, pins and landing stem are fixed.

## T2 (Merge and shared tails). *Two arcs that pass through a common switch
coincide from its stem onward: same subsequent pins, same landing. Hence an
unordered pair of arcs can make at most one switch active — their unique
first merge point — and both arcs of one stem, which merge at the latest at
their first common switch, pin identical values on every switch after it.*

Proof. Trailing exits leave via the stem, whose edge is unique; the
continuation of a cascade after a switch depends only on that switch. Two
arcs entering a common switch via different branches give it opposite pins
but share everything downstream, so no later switch sees two values from
this pair. ∎

## T3 (Retrace). *Let a trajectory traverse a path P consisting of an edge
into a branch port followed by a trailing cascade, ending at a stem S_z. If
the walk later exits S_z before any other traffic touches P's interior, it
retraces P exactly, backwards.*

Proof. Exiting S_z takes the unique stem edge, which is P's last edge,
backwards. Each interior switch of P was entered by P via some branch and
therefore pinned to it; the reverse traversal enters that switch via its
stem — a facing event — and exits by the tongue, i.e. by exactly the branch
P came in through. Induction along P. ∎

## T4 (Functional collapse). *If no faced stem flips on the cycle, nothing
flips on the cycle.*

Proof. If every faced stem has a constant tongue, each faced stem launches
one fixed arc, so the stem-to-stem itinerary is a walk in a functional graph
and its cycle visits each faced stem exactly once per period, using one arc
each. A switch can only flip if two used arcs enter it via opposite
branches; by T2 those arcs merge there and share their landing stem. But in
a functional cycle two distinct arcs never share a head — each stem has one
predecessor per period. Contradiction. ∎

## T5 (Flip successor). *Both flips of a switch m exit via the same stem
trail; the walk's continuation immediately after any flip of m is the same
fixed route regardless of the flip direction.*

Proof. A flip is a trailing event; both directions exit S_m and T1 applies. ∎

## T6 (The bounce, lobed case). *Suppose every active switch is "lobed": its
two flip arcs are its own launches, returning through its other branch (the
teardrop pattern). Then the reduced walk from active to next active is
functional AND symmetric — the successor of the successor of an active is
itself — so the cycle's actives number at most 2, and no further switch can
be active alongside them.*

Proof sketch, in three steps.

*(i) Functionality.* By T5 both launches of a lobed active a flip a and exit
S_a into the same trail; through any run of constant-tongued stems the
continuation is unique (each launches its single arc), so the next active
faced after a is a fixed φ(a).

*(ii) Symmetry.* The path from a to φ(a) consists of trails and constant
launches; by the time φ(a) flips and exits its stem, T3 applies to the just
laid pins: the exit retraces the incoming path segment by segment — trailing
interiors are re-entered facing and route backwards, each constant stem en
route re-launches its same arc — landing back at a. Hence φ(φ(a)) = a.

*(iii) A functional cycle with φ² = id has length ≤ 2.* Interior actives
cannot coexist: with two bouncing actives a, b, an interior active would
need opposite-branch feeder arcs with a common landing (T2); the four
available arcs pair off as (a,L)/(a,R) — which share tails by T2 and so
cannot opposite-pin anyone — and likewise for b, while cross pairs land on
opposite sides of the bounce. With one active, its two arcs share tails, and
constants' arcs recur inside the single fixed inter-a chain, whose
stem-route from any repeated constant is identical each period, pinning
identically — no second active. With zero actives, T4. ∎

## T7 (Reflector gadgets — formalised in `lean/GeneralN.lean`)

Abstract the rotator: a **reflector** is a one-port gadget with mouth stem
`g`: a train facing `g` wanders inside and emerges, a fixed number of steps
later, over `g`'s own edge, with the tongues transformed by a fixed map `τ`
on an invariant state class. A lobed switch is the smallest reflector
(`lobe_isReflector`, `τ = flip`); the compound rotators in the exhaustive
winners (e.g. switches 2–3 of the N = 4 maximiser) are two-switch
reflectors with involutive `τ`.

**Theorem (`reflector_period`, Lean, general N).** Any two reflectors
joined by any trailing cascade trap the train in a genuine cycle: one
half-period applies `τA` then `τB` and returns to A's mouth
(`reflector_halfPeriod`, via the cascade no-op and the retrace); for
involutive, commuting `τ` (disjoint gadget supports) two half-periods
restore the tongues exactly, and the cycle's tongue states are the orbit
`{u, τA u, τB (τA u), τB u}` — at most **4**, the Gray square.

## T8 (Systems and the one-mouth theorem — formalised)

Three further general-N results, machine-checked in `lean/GeneralN.lean`:

* **Simplicity** (paper): a cascade that revisits a switch trail-loops
  forever and never lands; used cascades are simple paths.
* **Merge-landing** (`merge_land`, Lean): two cascades whose paths share
  ANY switch land at the same stem.  Define two used cascades equivalent
  when their paths intersect; the equivalence classes — the **systems** —
  each have a unique landing stem, and all flips of a switch happen inside
  its system.
* **Landing injectivity** (`land_last_unique`, Lean): every cascade landing
  at a stem `s` ends at the same last switch (the one wired to `s`'s stem
  edge).  Hence **distinct systems have distinct landing stems**, and
  facing `s` identifies the system that just ran: each active cluster has
  exactly ONE mouth, and the mouth names the cluster.

This machine-checks the *static* half of the reflector interface: an active
cluster's traffic all exits through one identified mouth.  The cycle
decomposes as: system-runs (each depositing the train at its own mouth),
joined by forced facing-chains through connector arcs.

## T9 (The forest compilation and the echo machine — formalised in
## `lean/EchoMachine.lean`)

The trailing structure of *any* wiring compiles into a forest, and the
whole cycle dynamics into a ten-line register machine.

**The forest.** Each switch has one stem edge; call what it attaches to
the switch's *parent*.  A branch port of another switch → tree edge (the
switch is that branch's child).  A stem port of another switch → both are
**roots**, and the S–S edge **mouth-pairs their trees** (this is T8's
landing injectivity: a landing stem determines the landing tree).  A cap
or nothing → dead root.  So the switches partition into trees; used
cascades are exactly **ascents** (enter a tree at a free branch port,
trail up to the root, exit by the mouth, face the partner tree's root),
and the facing chains between cascades are **descents** of a tree from
its root, steered by the tongues.

**Three structural facts** (each proved on the concrete model):

1. tongues of a tree are written *only* during its own ascents
   (pins happen at trailed switches, which lie in the ascended tree);
2. an ascent from entry slot `e` points the whole ascent path back down
   at `e` (T1: each trailed switch is pinned toward where the train came
   from);
3. hence — the retrace theorem T3, generalised by last-writer-wins — **a
   descent from a root exits the tree at the slot of that tree's most
   recent ascent**, whatever older ascents did.

**The echo machine.**  Free branch ports (**slots**) are paired
involutively by the branch–branch track edges (**jump edges**); trees are
paired involutively by the mouth edges.  By facts 1–3 the eventual-cycle
dynamics is *exactly*: one register per tree — the slot of its last
ascent — and the step, from ascent entry `e`:

    write  reg[tree e] := e          (ascend the tree of e)
    read   f := reg[star (tree e)]   (descend the mouth partner)
    jump   next entry := bar f       (cross the jump edge)

Geometry is gone; falls and caps only truncate transients.  On a cycle,
**actives = Σ_T (σ_T − 1)** where σ_T is the number of distinct slots
from which T is ascended per period: a tree's σ ascent paths pairwise
diverge at exactly σ−1 branch nodes, each of which flips, and every
other tongue in the tree is eventually constant.

**Machine-checked, general N** (`lean/EchoMachine.lean`, no sorry, no
exhaustion): `reg_last_write` (registers hold the last ascent);
`return_jump` (the step re-enters through the slot by which the partner
tree was last entered); **`echo`** (an entry produced by two nested
returns *literally repeats an earlier entry* — the LIFO seed);
`succ_repeat` / `entry_change_read_change` (alternation propagation: two
ascents of the same tree produce the same successor unless the feeder's
partner register changed in between); **`bounce_orbit`** (a
partner-alternating orbit obeys `e(k+2) = bar(e k)` and visits at most
**four** distinct entries — the Gray square, for all N: the dogbone
pattern is closed, at any size).

## The remaining core, now two machine lemmas

The full theorems reduce to two statements *about the echo machine
alone*:

> **(B — the cycle lemma, = C\*.)**  Every eventual cycle of the echo
> machine has Σ_T (σ_T − 1) ≤ 2: at most two divergence nodes flip.
>
> **(C — the transient lemma.)**  A run of the echo machine makes O(1)
> **alternations** (ascents of a tree from a slot different from that
> tree's previous ascent) before entering its cycle.  Observed: never
> more than **one**.

Machine exhaustion (`docs/echo_machine.py`): all machines with 2 cells
(≤ 6 slots) and 4 cells (≤ 8 slots), all initial registers and starts —
183k configurations — plus 6-cell exhaustion over two-2-slot layouts and
300k random machines each at 8 and 10 cells: **max actives 2, max
transient alternations 1, throughout**.  Cycles can carry up to 12
distinct *entries*, but the surplus always lives in one-slot trees,
which pin nothing.  Sharper still, the per-tree σ-profile of every cycle
observed (C = 4 exhaustive, C = 8 random) is **either `()` — no tree
alternates, the functional collapse — or exactly `(2, 2)`** — two trees
of two slots each, the dogbone pattern.  No `(2)` alone (a lone
alternating tree cannot sustain itself in fall mode), no `(3)`, nothing
larger.  On the wiring side the same caps are exhaustive for all 143k
wirings with N ≤ 4 (in Lean) and unbeaten by cycle-objective search
through N = 7.

## The unconditional bounds (machine-checked, general N)

Two upper bounds hold with **no** open lemma behind them:

* **f(N) ≤ 2^N** (`lean/VectorCount.lean`, `vector_count_le` /
  `trajectory_count_le`): no run of any N-switch wiring, of any length,
  visits more than 2^N distinct tongue vectors.  Proved by a genuine
  pigeonhole induction (`pigeonhole`: a duplicate-free list of length-N
  boolean vectors has ≤ 2^N elements), not by assertion.

* **The accounting theorem** (`lean/EchoMachine.lean`,
  `unproductive_stall` + `productive_first_or_alternation`): a write
  that re-stores a register's current value changes *nothing*, and a
  write that changes a register is either the **first write of its
  cell** or an **alternation** (it differs from that cell's most recent
  previous write — proved via `reg_last_write`).  Hence, along any run,

      distinct machine states ≤ 1 + #first-ascents + #alternations
                              ≤ 1 + N + #alternations.

  This is the exact skeleton of N + O(1): the sole missing ingredient
  is a bound on alternations.

## f(N) ≤ N + O(1): what remains

Given **B** (cycle ≤ 2 actives ⇒ ≤ 4 cycle vectors) and **C** (O(1)
transient alternations — observed ≤ 1), the accounting closes to

    f(N) ≤ N + O(1),

matching the observed law f(N) = min(2^N, N + 4) up to the additive
constant.  Both open lemmas are finite-flavoured statements about a
ten-line machine with no geometry in it, and the observed σ-profiles
(`()` or `(2, 2)` only) say the eventual answer is exactly the dogbone
Gray square, every time.

## Consequences

* **Cycle vectors ≤ 4 (= the dogbone Gray square) for all N**, modulo B;
  **f(N) ≤ N + O(1)** modulo B + C.
* The machine is exactly as strong as the wiring dynamics on cycles, so
  B and C can be attacked — and exhausted — without ever enumerating
  wirings again.
* Everything is invariant under geometry: bridges, crossings and curvature
  never enter the argument, so cases (a)/(b)/(c) of the original question
  coincide, as observed.
