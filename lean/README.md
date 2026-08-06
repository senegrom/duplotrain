# Formal proofs (Lean 4)

Two libraries, both self-contained (no Mathlib):

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

`dogbone_period` covers an infinite family of wirings (any interior cascade
length, any N) — the mechanism that caps every observed cycle at 4 vectors,
formalised.

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
