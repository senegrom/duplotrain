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

is reduced to bounding actives. Status: the specific coefficient-one
`GeneralN.StateLaw` (`N+6`) is **OPEN**, but the unconditional general bound
`f(N) ≤ 34N+3` is proved as `GeneralN.state_law_linear` in
`lean/TrackQuantitative.lean`.  The proof is a direct physical-track lasso
argument and does not assume the echo-machine Gray-tail properties.  The
separate echo-machine route still reduces the sharper bound to the Gray tail
(**B**) and one-alternation transient (**C**); those remain open.  Evidence:
exhaustive for N ≤ 4 on wirings (140,152, in Lean), unbeaten by
cycle-objective search through N = 7, and exhaustive across all small
machines (`echo_machine.py`).

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

Machine exhaustion (`echo_machine.py` + the structured hunt): all
machines with 2 cells (≤ 6 slots) and 4 cells (≤ 8 slots), **all
machines with 6 cells and up to 10 slots (10.4 million runs — every
composition, every jump matching, every initial register, every
start)**, plus hill-climbing with actives as the objective at 8, 10 and
12 cells: **max actives 2, max transient alternations 1, throughout**.
Cycles can carry up to 12 distinct *entries*, but the surplus always
lives in one-slot trees, which pin nothing.  Sharper still, the
per-tree σ-profile of every cycle ever observed is **either `()` — no
tree alternates, the functional collapse — or exactly `(2, 2)`** — two
trees of two slots each, the dogbone pattern.  No `(2)` alone, no
`(3)`, nothing larger.  The mechanism behind "never `(2)` alone": an
alternating tree's two branches merge immediately after its mouth, so
some *second* register must remember which branch to take next — the
variation cannot steer itself.  Alternating trees come in mutually
steering **pairs**, and lemma B says a single trajectory sustains at
most one pair.  On the wiring side the same caps are exhaustive for all
143k wirings with N ≤ 4 (in Lean) and unbeaten by cycle-objective
search through N = 7.

**Absorption (machine-checked).**  The lobed instance of B is now a
theorem for all N (`EchoMachine.lean`: `absorb`, `absorb_entries`): if
slots `a, bar a` share a cell, slots `b, bar b` share its mouth
partner, and the walk ever enters `a` while the partner's register
holds `b` or `bar b`, then **every subsequent entry lies in
`{a, bar a, b, bar b}`** — the doubly-lobed pair is a trap.  After
absorption all writes are confined to the two cells: the alternation
bound holds outright for every run that falls into a lobed Gray
square, which is the pattern every exhausted machine's active cycle
actually exhibits.

## T10 (The delivery chains: why a lone alternator is impossible)

Two further machine facts are Lean-checked
(`reg_cell`, `witness`, `succ_of_reg_eq`):

* **Witness identity.**  Every entry names its own delivery:
  `cell (bar (e (k+1))) = star (cell (e k))`, and the partner's
  register at read time *is* `bar (e (k+1))`.  So the walk's
  predecessor structure is forced: the cell ascended before an entry
  `x` is always `star (cell (bar x))`, and the witness cell
  `cell (bar x)` must hold register `bar x` at that moment.
* **Merge at the mouth.**  Two ascents of the same cell with equal
  partner registers have identical successors: a cell's variation
  cannot steer itself.

**The nesting argument** (paper, the emerging proof of B).  Suppose a
cycle has exactly one alternating cell C.  Every varying read is of C,
so C's varying entries must themselves be `bar (s C)` — delivered by
reading C — which by the witness identity makes C's own slots
bar-paired inside C (a lobe) and makes C\* the predecessor of every
C-ascent.  C\* is constant, entered always at some slot `w`, so its
witness cell `H = cell (bar w)` must hold `bar w` and be read by H\*;
H\*'s constant entry needs its own witness K read by K\*, and so on:
**each delivery pushes a fresh frame, and the walk realises the frames
as nested Z … Z\* excursions — a LIFO structure**.  Finitely many
cells force the innermost frame to close directly: Z reads Z\* (value
`q`) and jumps to `bar q` *inside* Z\* — so `q, bar q ∈ Z*`, i.e. the
innermost frame is a **lobed alternator**: a second member of M.
Contradiction — so m = 0 or m ≥ 2, and the observed saturation (each
alternator's variation is fully consumed steering the other) is what
caps m at exactly 2.  The two open steps to a full proof of B: (a)
rigorise the finiteness/nesting step, (b) show a third alternator has
no steering source left.

**The (2,2) attractor shapes** (exhaustive classification, C = 4 and
C = 6 complete, 10.6M runs): writing L for an alternator whose two
slots are bar-paired to each other (a lobe) and E for one steered
through external constant cells,

| signature | mouth relation | example |
|---|---|---|
| (L, L) | partners | the dogbone (covered by `absorb`) |
| (L, L) | non-partners | lobed pair steering at a distance |
| (E, L) | partners and non-partners | one lobe, one external steer |
| (E, E) | partners | all steering through constant cells |

A **direct cross** (alternators bar-paired into each other without
lobes) never occurs.  Non-partner pairs confirm that steering is
routed through constant chains, exactly as the nesting argument
predicts; generalising `absorb` to the E-signatures is the remaining
formal step of the lobed→general trap programme.

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

## Heat: the token calculus (machine-checked, general N)

Call a slot **confirmed** when its cell's register points at it, and
call an unconfirmed slot whose jump partner is confirmed a **token** —
a hot edge end.  All of the following are Lean theorems
(`lean/EchoMachine.lean`), unconditional, for every machine and every
run:

* **Productive steps land exactly on tokens** (`arrival_token`), and a
  step can create at most one token, at the written cell's evicted
  register (`token_step`).  So the token count never increases
  (`tokens_nonincreasing`, `tokens_antitone`), and it is at most one
  per cell at every moment (`tokens_le_cells`, via the bar-involution).
* **Freeze-out and the singleton lock** (`freezeout`,
  `singleton_lock`): a cell with no tokens never changes its register
  again; a cell whose tokens sit in `{t}` keeps its register in
  `{current, t}` forever — σ ≤ 2 for singleton-token cells.
* **The repertoire collapse** (`token_pedigree`, `future_register`):
  the machine can never invent values.  Every token alive at time
  `K + d` was already a token at `K` or sits at a slot that has held
  its own cell's register in between; consequently **every value a
  cell's register will ever hold is either its current value or the
  slot of a currently live token**.  The token profile at any moment
  spans the machine's entire future state space, and the space only
  collapses as tokens die.  Counted (`repertoire_count`,
  `fresh_values_le_tokens`): σ(C) ≤ 1 + #tokens(C) for every cell, and
  the whole run exhibits **at most `#cells` fresh values in total** —
  Σ(σ − 1) ≤ #tokens ≤ #cells, across all cells and all time.
* **Conservation on cycles** (`no_emission_drop`,
  `recurrence_emission`): a productive step whose evicted slot does
  not come out a token *strictly* cools the machine — so inside any
  register recurrence every productive step re-emits.  The eventual
  cycle's tokens are a **conserved population, handed from evicted
  slot to evicted slot, never destroyed**, and by the collapse the
  cycle's whole value repertoire is spanned by that fixed population.
* **The cycle dichotomy** (`recurrence_dichotomy`): inside a
  recurrence, every productive step either **flips its own edge** (the
  evicted slot is the arrival's jump partner — the Gray move) or
  **hands off through a foreign edge that was fully confirmed before
  the step**.  Cycles move a hole through full edges, or flip lobes.
* **The steering seed** (`change_has_productive`,
  `variation_needs_variation`, `trajectory_merge`,
  `divergence_names_steer`): registers move only through productive
  writes of their own cell; two different deliveries with a common
  witness cell force a productive write of that witness cell strictly
  between them; the walk's route can only branch where a read differs
  — and a recurring entry that later diverges *names* the steering
  cell (star of a visited cell) and the productive write that steered.
  Variation is never free: it must be fed by variation upstream.
* **The quiet mouth is unreachable** (`quiet_mouth_unreachable`,
  `read_back_productive`, `lone_write_no_mouth`, with
  `mouth_entry_productive` / `mouth_delivery_lobe`): a walk can
  **never** travel from a cell to that cell's mouth partner through
  unproductive steps alone.  The productive-free path is forced to be
  its own `bar`-reflection — entry `j` steps from the end is `bar` of
  entry `j+1` steps from the start, the machine-level *retrace* — so
  its middle would be a `star` fixed point (impossible) or an
  unproductive mouth crossing (impossible: mouth entries are always
  productive).  Hence **every read-back of a cell's variation costs a
  productive write strictly in between**, and a walk whose every
  productive write lands in its start cell can never reach that
  cell's mouth partner at all: **a lone alternating cell cannot steer
  itself** — the self-steering half of "no `(2)`-alone profile",
  machine-checked for all N.
* **Every run is a rho** (`Periodicity.lean`: `state_repeat`,
  `run_eventually_periodic`, `run_rho`): the pair (current entry,
  registers) evolves autonomously in a finite space, so within
  `|slots|^(|cells|+1) + 1` steps some state recurs and determinism
  replays the stretch forever — pre-period and period explicitly
  bounded, and on the tail entries *and* registers are periodic while
  every productive step re-emits its token (`recurrence_emission`
  instantiated on a real cycle, not a hypothetical one).
* **m ≠ 1 on cycles: the lone writer freezes** (`LoneWriter.lean`).
  If all productive steps of the periodic tail write one cell `C`,
  foreign registers freeze; the walk can never stand at `star C`
  after visiting `C` (the retrace palindrome), and a cell is only
  ever *read* from its mouth partner — so `C`'s variation is
  invisible to the routing.  Any two `C`-visits then have identical
  futures (`lone_merge`), periodicity turns merged futures into
  equal deliveries (`lone_arrivals_agree`), and `C` freezes too:
  there are **no productive steps at all** (`lone_writer_quiet`).
  Headline, composed with the rho theorem
  (`rho_quiet_or_two_mouths`): **every eventual cycle is completely
  quiet or steered from at least two distinct cells** — the dynamic
  half of the one-mouth theorem, machine-checked for all N.  The
  lone-alternating-tree case of lemma B is dead outright.

* **The steering law: active cycles stand at active mouths**
  (`SteeringLaw.lean`).  For an *arbitrary* writer set `S` — no
  palindrome, no `bar`-freeness needed: if the walk never stands at
  `star C` for any writer `C`, every read on the tail is a frozen
  foreign register (a cell is only read from its mouth partner), so
  same-cell visits merge, periodicity equalizes all deliveries, and
  every register freezes: **a stand-free tail is silent**
  (`no_stand_quiet`).  Hence every eventual cycle is quiet or stands
  at the mouth partner of an active cell
  (`active_tail_stands_at_mouth`, `rho_steering`).  The anatomy of a
  stand: it fetches exactly `bar (reg C)` (`stand_delivery`) — the
  only mechanism by which a writer's variation is ever read — and if
  `star C` is not itself a writer, all stands at `star C` carry one
  fixed frozen entry (`stand_entry_frozen`): the cycle is frozen
  rails between look-alike stands, with all variation concentrated
  in the fetched deliveries.  This is the machine-level skeleton of
  the reflector interface: the two-mouth (m = 2) cycle must
  physically execute mouth crossings at `star C1` / `star C2`,
  exactly as the dogbone bounce does.  And the flip anatomy: a
  delivery landing back in its writer cell is the Gray move
  (`stand_flip`), and a cell whose every arrival is the self-flip is
  locked in the two-element orbit `{v₀, bar v₀}` forever
  (`flip_lock`) — σ ≤ 2 for pure flippers, unconditional.  The m = 2
  Gray-pair question is now exactly: why must both writers of an
  active two-mouth cycle be pure flippers (or frozen)?

* **The lobe dichotomy** (`LobeDichotomy.lean`).  A slot can only be
  delivered by reading its bar-partner out of the partner's own cell
  (`partner_held`).  Hence foreign-partnered registers are
  *irreversible* (`cross_stays_cross`: delivering a lobe slot would
  need the cell itself to hold its other end), and while a cell is
  lobe-valued **every arrival is the Gray flip** — the register
  never leaves `{v₀, bar v₀}` (`lobe_gray_lock`; no writer-set, no
  productivity, no `bar`-freeness hypotheses).  With periodicity:
  every cell of every eventual cycle **is a Gray flipper (σ ≤ 2) or
  foreign-valued at every moment** (`rho_gray_or_cross`), and a
  foreign-valued cell's every delivery reads a *different* cell
  (`cross_delivery_reads_foreign`).  The dogbone's lobe pair is now
  a theorem-level attractor class; what remains of lemma B is the
  foreign-valued (cross-coupled) cells — for m = 2: writes into a
  cross cell read only the other writer or frozen rails, and the
  sync argument (a cross delivery sets `reg C1 := bar (reg C2)`,
  after which the pair reads back unproductively) is the target.

Together these turn lemma B into a single sharp question: **can three
or more tokens of the cycle's conserved population actually be
consumed on the cycle?**  Every exhaustion says no — the population's
effective size is 0 (functional collapse) or 2 (the Gray pair).  With
m ≠ 1 proved, the open profiles are exactly: m = 0 (quiet — done,
snapshots frozen), m = 2 (show it is the Gray pair, ≤ 4 vectors —
the steering law pins its walk to rails-and-stands, and the lobe
dichotomy makes each writer a Gray flipper or cross-coupled), and
m ≥ 3 (show it cannot happen).

## The abstract-machine exhaustion: B holds with arbitrary registers

Three experiments (`tools/bsearch.py`, `tools/bclassify.py`,
`tools/baltern.py`) settle whether abstract lemma B needs wiring
structure.  2,302,176 simulated runs — exhaustive over every abstract
machine with 2 cells (4 and 6 slots) and 4 cells (6 slots): every
surjective cell assignment × every fixed-point-free `bar` matching ×
**every** well-formed initial register map × every start slot — plus
~1.7M random machines up to 8 cells and 14 slots.  Results:

* **Zero violations**: max Σ(σ−1) = 2, max cycle snapshots = 4, even
  with adversarially pre-loaded initial registers.  Abstract B needs
  no wiring structure.
* **The only profiles are `()` and `(2,2)`** — `(2)` never occurs,
  exactly as `lone_writer_quiet` predicts (one writer ⇒ no writes).
* **Classification of all 315,081 active cycles**: each active cell
  is a *lobe flipper* (both values bar-partnered inside the cell —
  the case `lobe_gray_lock` already closes) or an *out cell* (both
  values partnered into frozen cells — fed by frozen witnesses,
  steered by the other writer).  The *cross-coupled* type (values
  bar-paired into the other active cell) **never occurs**: a cross
  import synchronizes the pair and freezes it.  Every active cycle
  visits the **full Gray square** (all four register pairs).
* **The four-beat law**: all 265,525 active cycles have **exactly
  four productive writes per period, strictly alternating** between
  the two active cells.  No exception.

Proof path for the alternation (the biggest remaining step): two
consecutive same-cell writes make the window between them
single-writer; all other registers are constant there, so the walk is
a finite automaton in (position, reg C1) and must close a
single-writer loop — making the whole future single-writer, which
`lone_writer_quiet` freezes, contradicting the writes themselves.
Alternation then caps each cell at two values per period and kills
every Σ(σ−1) ≥ 3 profile.

The first word-level step is now machine-checked in
`lean/Alternation.lean`.  A quiet return to the same cell repeats the
complete machine state and is quiet forever; a quiet visit to its mouth
partner is impossible by the retrace palindrome.  Combined with the
periodic replay theorem, `consecutive_productive_write_cells_ne` proves
that two consecutive productive writes always target different cells.
What remains is the genuinely stronger two-letter claim: after writers
`C,D`, the next productive writer is `C` (or the tail has already gone
quiet).  No such claim is assumed by the current state-law bounds.

## The strict-base ceiling: below 2^N unconditionally

Independently of the N + O(1) program, the support-epoch campaign
(merged from a parallel agent, repaired and verified) now proves a
**register-snapshot ceiling with exponential base strictly below 2**,
machine-checked and unconditional over any complete finite echo frame
(`CanonicalUnconditionalGlobalBound.lean`):

    T^8 ≤ (4N+2)^8 · 2^(7N+18),   i.e.   T ≤ poly(N) · 2^(0.875·N).

The engine: linearly many support epochs (support only shrinks);
inside a fixed support, no-full components freeze and tree components
replay from a single full-edge choice, so states inject into a sparse
code of capacity² ≤ 2^#cells; the first certified lobe-pair absorption
starts a ≤ 4-snapshot Gray tail.  The **overwrite lasso** (pin words
are idempotent, so a recurrent echo configuration carries at most two
tongue vectors per cascade prefix) transfers this to concrete tongue
vectors at cascade boundaries — conditional on the T9 compilation
interface (every wiring's `stepN` as configuration-driven pin words),
which is the open step of this route.

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
