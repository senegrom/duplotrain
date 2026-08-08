# Formal proofs (Lean 4)

Thirty-five libraries, all self-contained (no Mathlib).  Core five
below; plus the accounting/monovariant satellites (all sorry-free,
honestly conditional where marked):

* `LoneWriter.lean` — **m ≠ 1 on cycles: the lone writer freezes.**
  If every productive step of a periodic tail writes into a single
  cell `C`, then every register — including `C`'s own — is constant,
  and there are no productive steps at all.  The engine: foreign
  registers freeze (`lone_frozen_foreign`); the walk can never stand
  at `star C` after visiting `C` (`lone_no_partner`, by the retrace
  palindrome), and a cell is only ever *read* from its partner, so
  the lone writer's variation is invisible to its own steering; any
  two `C`-visits therefore have identical futures (`lone_merge`), and
  periodicity turns merged futures into equal deliveries
  (`lone_arrivals_agree`), freezing `C` too.  Headline:
  `rho_quiet_or_two_mouths` — **every eventual cycle is completely
  quiet or steered from at least two distinct cells**, for every
  machine, every run, every `N`.  The dynamic half of the one-mouth
  theorem, and the death of the lone-alternating-tree case of lemma B.

* `SteeringLaw.lean` — **active cycles stand at active mouths.**
  The generalization of the lone-writer engine to an *arbitrary*
  writer set `S`, needing neither the palindrome nor `bar`-freeness:
  a cell is only ever read from its mouth partner, so if the walk
  never stands at `star C` for any writer `C`, every read is frozen,
  same-cell visits merge (`no_stand_merge`), periodicity equalizes
  all deliveries (`no_stand_arrivals_agree`), every register freezes
  (`no_stand_freeze`) and nothing is productive (`no_stand_quiet`).
  Headline `active_tail_stands_at_mouth` / `rho_steering`: **every
  eventual cycle is completely quiet, or the walk physically stands
  at the mouth partner of one of its active cells** — for
  `S = [C1, C2]`, the two-mouth cycle must visit `star C1` or
  `star C2`, the dogbone's mouth crossings.  Plus the stand anatomy:
  `stand_delivery` (a stand fetches exactly `bar (reg C)` — the only
  way a writer's variation is ever read) and `stand_entry_frozen`
  (if `star C` is not itself a writer, all stands at `star C` carry
  one fixed entry: the cycle is frozen rails between look-alike
  stands, and only the fetched delivery varies).  `stand_flip`: a
  delivery landing back in its writer cell is the Gray move
  (register := its bar); `flip_lock`: **a cell whose every arrival
  is the self-flip keeps its register in the two-element orbit
  `{v₀, bar v₀}` forever** — σ ≤ 2, the two-value half of lemma B
  for pure flipper cells, unconditional.

* `Periodicity.lean` — **every run is a rho**: the state (current
  entry + registers of the listed cells) evolves autonomously and
  ranges over a finite space, so some state recurs within
  `|slots|^(|cells|+1) + 1` steps (`state_repeat`) and determinism
  replays the stretch forever (`run_eventually_periodic`): explicit
  pre-period and period bounds, machine-checked.  `run_rho` adds the
  payoff: on the tail all registers are periodic too, and — via
  `recurrence_emission` — **every productive step on the tail
  re-emits a token**: the eventual cycle's token population is
  conserved, unconditionally.  The cycle-classification theorems
  (`lone_write_no_mouth`, `divergence_names_steer`) now have a
  machine-checked cycle to run on.

* `FutureEntryBound.lean` — **the linear future entry alphabet**:
  every entry from any base time on lies in a fixed alphabet (the base
  entry, bars of base registers, bars of live tokens) of size
  ≤ `2·#cells + 1`; pair-duplicate-free phases are quadratically
  bounded.  Built on `future_register_le`.
* `CellHeat.lean` — **local heat never grows**: each cell's token
  count is individually non-increasing (tokens cannot migrate between
  cells) — so every condition of the Gray-tail token shape
  (tokenless cells, ≤1-token cells) is monotone once reached.
* `TokenState.lean` — occupancy and token-ends *determine* every
  register (`confirmed ↔ occupied ∧ ¬token`): state recurrence is
  finite token motion on the monotone occupied support.
* `PairMultiplicity.lean` — if every consecutive entry pair occurs
  ≤ `r` times in a phase, the phase has length
  ≤ `r·(2·#cells+1)²`: any uniform pair-multiplicity bound gives a
  polynomial state bound.

* The **support-epoch campaign** (`ReversalFacts`, `MonotoneSupport`,
  `SupportSize`, `HiddenFibre` / `HiddenAbsorb` / `HiddenDichotomy`,
  `LobeAbsorption`, `TreeReplay` / `TreeEpochCode` / `RootRank`,
  `ComponentCapacity` / `ProfileCodeBound` /
  `ThreeQuarterArithmetic` / `EpochAggregation`) — toward a
  subexponential ceiling `f ≤ poly · 2^(3N/4)`.  Proved outright:
  occupied support only ever shrinks, so along any run there are at
  most `#edges + 1` distinct support vectors (`support_epoch_bound`),
  and occupied edges inject into cells (`occupied_edges_le_cells`);
  a productive step whose cell-projection stalls is a parallel-edge
  move that is either a lobe Gray-flip (two in a row absorb —
  `two_hidden_preserved_absorb`) or permanently empties its old edge
  (`hidden_drop_forever`); within one support epoch, tree components
  with a decreasing-rank certificate replay their whole snapshot from
  the choice of one full edge (`tree_epoch_count`), with capacity²
  ≤ `2^#cells` (`treeCapacity_square`).  The capstone aggregation
  (`encoded_three_quarter_bound`, `aggregate_three_quarter_epochs`)
  is **conditional**: it still assumes states inject into the
  projected code plus active-lobe bits — that injection is the open
  step of this route.

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
| `token_shape_tail` / `gray_tail` | **the Gray tail from the token shape**: under the shape every exhaustion exhibits — ≤1 token in each of two cells, none anywhere else — every later snapshot is one of **four explicit candidates**, so at most 4 distinct snapshots occur, ever: the quantitative half of lemma B |
| `state_law_of_token_shape` | the conditional scaffold re-based: token shape at `K` + ≤1 alternation before `K` ⇒ ≤ `#cells + 6` snapshots.  The open core is now exactly *reaching* the token shape within one alternation |
| `divergence_names_steer` | **the steering locator**: a recurring entry that later diverges names a moment where the entries still agree and a productive write of `star(cellOf ·)` lands strictly between the visits — steering is never anonymous |
| `mouth_entry_productive` / `mouth_delivery_lobe` | mouth crossings are always productive; deliveries across a mouth hand out the entered cell's own lobe slots (witness + involution) |
| `quiet_mouth_unreachable` | **the quiet mouth is unreachable**: no productive-free stretch can lead from a cell to its mouth partner — the quiet path is forced to be its own `bar`-reflection (the machine-level retrace), whose middle is a `star` fixed point or an unproductive mouth crossing, both impossible |
| `read_back_productive` / `lone_write_no_mouth` | **a lone alternating cell cannot steer itself**: reading a cell's variation back costs a productive step in between, and a walk whose every productive write lands in its start cell can *never* reach that cell's mouth partner — for every machine, every run, every `N` |

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
outright (`absorb`).  The eventual cycle itself is no longer
hypothetical: `Periodicity.run_rho` proves every run enters one, with
explicit bounds, periodic registers, and conserved tokens on the tail.
On that cycle the single-mouth case is now dead:
`LoneWriter.rho_quiet_or_two_mouths` proves every cycle is quiet or
steered from ≥ 2 cells — a lone alternating cell freezes outright.
The pedigree/conservation theorems reduce B to a
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
