# Formal proofs (Lean 4)

Three libraries, all self-contained (no Mathlib):

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
docs/lazy-point-theory.md): any wiring's trailing structure compiles to a
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

The remaining unproved core of the full cycle theorem is now two lemmas
about this machine (see docs/lazy-point-theory.md): **B** (every machine
cycle has Σ(σ−1) ≤ 2 — this is C\*) and **C** (O(1) transient
alternations).  Modulo B + C, the total state count obeys
f(N) ≤ N + O(1).  Both are exhaustively verified across all small
machines by `docs/echo_machine.py` (max actives 2, max transient
alternations 1, everywhere).

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
