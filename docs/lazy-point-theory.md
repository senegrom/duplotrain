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
except one precisely isolated configuration (C\*), which is verified
exhaustively for N ≤ 4 (140,152 wirings, also in Lean) and unbeaten by
dedicated cycle-objective search through N = 7.

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

## The remaining core (C\*), reduced again

> **(C\*)** On any eventual cycle, each active system's *dynamics* is a
> reflector: the walk re-entering the system returns through its mouth
> after a bounded excursion, with an involutive state map.

The static half (one mouth, mouth-identifiability) is now proved (T8); the
open half is return-through-the-mouth plus involutivity.  Given C\*, T4
rules out flip-free faced stems, T8 gives the mouths, and
`reflector_period` caps every cycle at the Gray square — at most 2 active
switches and 4 tongue vectors, for all N.  C\* holds in every exhaustively
checked wiring (all 143k with N ≤ 4, in Lean; N = 5 exhaustion of the
cycle wall in progress) and survived dedicated cycle-objective search
through N = 7 (max cycle vectors 4, max actives 2, always).

## Consequences

* **Cycle vectors ≤ 4 (= the dogbone Gray square) for all N**, modulo C\*.
* The state-count law f(N) = min(2^N, N + 4): the cycle contributes ≤ 4;
  the transient's contribution of at most one productive flip per switch is
  observed exactly (winners decompose as N transient vectors + the Gray
  square for every N measured) but its general-N proof remains open — the
  second open item besides C\*.
* Everything is invariant under geometry: bridges, crossings and curvature
  never enter the argument, so cases (a)/(b)/(c) of the original question
  coincide, as observed.
