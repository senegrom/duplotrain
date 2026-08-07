# Formal proofs (Lean 4)

Thirteen libraries, all self-contained (no Mathlib).  Core five below;
plus the accounting/monovariant satellites (all sorry-free, honestly
conditional where marked):

* `LinearBound.lean` — **snapshots ≤ #cells + #alts + 1**, for any
  alternation list covering the prefix: the unconditional accounting
  with an arbitrary alternation budget (no Gray tail needed).
* `SlotBound.lean` — **snapshots ≤ #slots + 1 under one hypothesis**,
  `ProductiveSlotReplay` (two productive arrivals at the same slot give
  the same snapshot): the cleanest known single-lemma reduction of the
  O(N) state law.
* `ReplayFacts.lean` — first steps toward proving that hypothesis:
  equal delivered entries force equal registers at the destination and
  source cells.
* `AlternationBound.lean` — forced-predecessor lemmas and a
  conditional two-alternations-per-cell bound.
* `SupportBound.lean` / `SupportMove.lean` — the edge-occupancy
  monovariant: an empty jump edge (neither end confirmed) stays empty
  forever; transfer laws for fully-confirmed edges.
* `EdgeReversal.lean` — the cell-level walk arrow reverses after
  traversal (the LIFO seed at cell level).
* `PairBound.lean` — distinct consecutive-entry pairs number ≤ #slots².

**`GeneralN.lean` — general-N theorems, no exhaustion.** Every result holds
for an arbitrary number of switches and arbitrary wirings, proved by
structural induction (no `native_decide`, no `sorry`):

| theorem | statement |
|---|---|
| `trailing_route`(`_independent`) | a trailing pass's route never reads the tongues (T1/T2) |
| `descent_sound` / `_pins` / `_noop` / `_rebase` | cascades run as recorded, pin exactly their branches, and are tongue-independent no-ops when re-run |
| `retrace` | **T3**: a train entering the last cascade switch's stem walks the cascade *backwards* by pure facing moves — the pins route it home — tongues untouched |
| `lobe_hop` | facing a lobed switch crosses the lobe, flips it, exits the stem (2 steps, both tongue values) |
| `dogbone_halfPeriod` | **the bounce**: lobed `a`, arbitrary trailing cascade, lobed `b` — `2·|ps|+6` steps flip exactly `a`,`b` and return to `a`'s stem |
| `dogbone_period` | two half-periods restore the tongues exactly: the orbit is a genuine cycle whose tongue states are the Gray square |
| `IsReflector` / `lobe_isReflector` | the one-port gadget interface; lobes are its smallest instances |
| `reflector_halfPeriod` / `reflector_period` | **any two reflectors joined by any cascade** bounce forever; for involutive commuting state maps the cycle's tongue states are exactly the Gray orbit — at most 4 |

`dogbone_period` and `reflector_period` cover infinite families of wirings
(any cascade length, any gadget size, any N) — the mechanism that caps every
observed cycle at 4 vectors, formalised.

**`EchoMachine.lean` — the abstracted cycle dynamics** (T9 in
../lazy-point-theory.md): any wiring's trailing structure compiles to a
forest of trees; the cycle dynamics reduces to a register machine (one
register per tree = slot of its last ascent; step = write own register,
read mouth-partner's, jump through its bar-involution).  General-N
theorems, no `native_decide`, no `sorry`:

| theorem | statement |
|---|---|
| `reg_write` / `reg_skip` / `reg_stable` / `reg_last_write` | a register holds exactly the slot of its cell's most recent ascent |
| `return_jump` | the step identity: the next entry is `bar` of the partner cell's last ascent entry |
| `echo` | the repetition identity: an entry produced by two nested returns **literally repeats an earlier entry** (the LIFO seed) |
| `succ_repeat` / `entry_change_read_change` | alternation propagation: same-cell ascents produce the same successor unless the partner register changed in between |
| `bounce_step` / `bounce_orbit` | a partner-alternating orbit obeys `e(k+2) = bar(e k)` and visits **at most 4 distinct entries** — the Gray square, for all N |
| `unproductive_stall` | a write that re-stores the current value changes **no** register: states move only through productive writes |
| `productive_first_or_alternation` | **the accounting theorem**: every productive write is the *first* write of its cell (≤ N over a run) or an *alternation* — the unconditional skeleton of f(N) ≤ N + O(1) |
| `absorb` / `absorb_entries` | **absorption**: a doubly-lobed mouth pair entered compatibly traps the walk forever — every later entry lies in `{a, bar a, b, bar b}`, so all subsequent alternations are confined to the two cells (the lobed case of lemma B, as an attractor) |
| `reg_cell` / `witness` | registers stay in their own cells, and **every entry names its delivery**: `cell (bar (e (k+1))) = star (cell (e k))` with the partner register equal to `bar (e (k+1))` — the predecessor structure is forced (seed of the T10 nesting argument) |
| `succ_of_reg_eq` | merge at the mouth, direct form: same cell + equal partner registers ⇒ identical successors — variation cannot steer itself |
| `snap_stall` / `snap_between` | register snapshots move only at productive steps and are constant across productive-free stretches |
| `state_law` | conditional counting scaffold — **not the state law**: IF a run has a ≤4-element Gray tail and ≤1 alternation before it (both **open** — the hard core of the problem), THEN ≤ `#cells + 6` distinct snapshots. Contributes only the counting around the open core |
| `confirmed_step` / `head_confirmed` | the confirmation dynamics: each cell confirms exactly its register slot, and every step's read value is confirmed — the walk always leaves a confirmed slot |
| `arrival_token` / `token_step` | a productive step lands exactly on a **token** (unconfirmed slot, confirmed partner) and can create at most one new token, at the evicted slot of the same cell |
| `tokens_nonincreasing` / `tokens_le_cells` | **heat never grows**: the number of tokens — the machine's capacity for future alternations — is non-increasing along any run and at most one per cell at every moment. (Does NOT bound alternation *events*: a token can be consumed and re-emitted forever — the Gray flip — so the open core stands) |
| `freezeout` | **freeze-out**: a cell with no tokens never changes its register again — productive arrivals need a token of the written cell, and fresh tokens appear only at the written cell's own evicted slot |
| `singleton_lock` / `singleton_lock_reg` | **the singleton lock**: a cell whose tokens are contained in `{t}` keeps its register in `{current register, t}` **forever** — single-token cells alternate between at most two slots: the σ ≤ 2 half of lemma B for singleton cells, unconditional |
| `token_pedigree` / `future_register` | **the repertoire collapse — the machine can never invent values**: every token traces back to a base-time token or to an evicted register, so every value a cell's register will *ever* hold is either its value now or the slot of a token alive now.  The current token profile spans the entire future state space, and it only shrinks |
| `repertoire_count` / `fresh_values_le_tokens` | the collapse, counted: σ(C) ≤ 1 + #tokens(C) for every cell, and **at most `#cells` fresh values ever appear in the whole run** — Σ(σ−1) ≤ #tokens ≤ #cells across all cells and all future time, unconditional |
| `tokens_antitone` / `no_emission_drop` | heat decreases over arbitrary intervals; a productive step whose evicted slot does not come out a token **strictly** cools the machine |
| `recurrence_emission` | **conservation on cycles**: inside any register recurrence every productive step re-emits — the eventual cycle's tokens are a conserved population, handed from evicted slot to evicted slot, never destroyed.  With the collapse, the cycle's whole value repertoire is spanned by that fixed population |
| `recurrence_dichotomy` | **the cycle dichotomy**: inside a recurrence every productive step either flips its own edge (evicted = bar of arrival — the Gray move) or hands off through a foreign edge that was fully confirmed before the step |
| `change_has_productive`(`_le`) | registers move only through productive writes of their own cell |
| `variation_needs_variation` | **the steering seed (T10 brick 1)**: two different deliveries with a common witness cell force a productive write of that witness cell strictly between them — a cell's variation must be steered by somebody's variation |
| `trajectory_merge` | **trajectory determinism**: two moments at the same cell whose subsequent reads all agree produce identical entry sequences — the walk branches only where a read differs |

**`StateLaw.lean` — the target theorem, in the language of tracks and
switches.**  `GeneralN.StateLaw` states the actual claim — a single
train on any `N`-switch lazy-point layout ever sees at most `N + 6`
distinct tongue vectors — directly over `Wiring`/`stepN`, decodable
piece by piece as track, switches and the lazy-point rule.  **It is
OPEN: nothing in this repository proves it.**  Proved alongside it:
`state_law_two_pow`, the identical statement with `2 ^ N` in place of
`N + 6` — the pigeonhole ceiling.  The open problem is exactly closing
`2 ^ N` down to `N + O(1)`.

**`VectorCount.lean` — the unconditional ceiling, f(N) ≤ 2^N**: a real
pigeonhole proof (induction on N, splitting on the first coordinate),
no `native_decide`:

| theorem | statement |
|---|---|
| `pigeonhole` | a duplicate-free list of length-N boolean vectors has at most 2^N elements |
| `vector_count_le` / `trajectory_count_le` | **no run of any N-switch wiring, of any length, visits more than 2^N distinct tongue vectors** |

The remaining unproved core of the full cycle theorem is two lemmas
about the echo machine (see ../lazy-point-theory.md): **B** (every
machine cycle has Σ(σ−1) ≤ 2 — this is C\*) and **C** (O(1) transient
alternations).  Modulo B + C, the accounting theorem closes the state
count to f(N) ≤ N + O(1); unconditionally, f(N) ≤ min(2^N, N + 1 + A)
with A the run's alternation count.  The lobed case of B is proved
outright (`absorb`).  The pedigree/conservation theorems reduce B to a
single sharp question: the cycle's conserved, repertoire-spanning
token population (`recurrence_emission` + `future_register`) — can
**three or more** of its tokens actually be consumed on the cycle?
Every exhaustion says no (profiles `()` and `(2,2)` only).  B and C are exhaustively verified across all
machines with ≤ 6 cells and ≤ 10 slots — 10.4M runs — plus climbs at
8–12 cells (max actives 2, max transient alternations 1, everywhere;
every cycle's σ-profile is `()` or `(2,2)` — functional collapse or the
dogbone Gray square, never a lone alternating tree, never three).

**`DuplotrainProofs.lean` — exhaustive small-N theorems** (`native_decide`):
the wiring enumerator, the perfection automaton (reflecting caps) and the
state-counting automaton (fall-off caps, including port-entry starts).

Verified by `native_decide`:

| theorem | statement |
|---|---|
| `no_perfect_three` / `no_perfect_four` | no connected 3- or 4-switch wiring is perfectly looping |
| `unique_perfect_one` / `unique_perfect_two` | the teardrop and the dogbone are the unique perfect wirings |
| `states_one..four` | max distinct tongue vectors = 2, 4, 7, 8 = min(2^N, N+4) |
| `cycle_cap_two..four` | eventual cycles carry at most 4 tongue vectors (the Gray square) |
| `count_two..four` | enumeration sizes 76 / 2,620 / 140,152 |

Build: `lake build` (needs elan; toolchain pinned in `lean-toolchain`).
The n ≤ 3 theorems check in seconds; the four n = 4 exhaustions bring the
full build to ~12 minutes.

Scope note: the theorems quantify over `allWirings n` as defined by the
enumerator; its completeness is by construction of the pairing recursion,
cross-checked by the count theorems. Formalising enumerator completeness
itself is the natural next step.
