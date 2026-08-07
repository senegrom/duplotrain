# Formal proofs (Lean 4)

Four libraries, all self-contained (no Mathlib):

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
outright (`absorb`).  B and C are exhaustively verified across all
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
