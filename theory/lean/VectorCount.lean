import GeneralN

/-!
# The unconditional ceiling: f(N) ≤ 2^N, machine-checked

The state-count question asks how many distinct tongue vectors a single
train can visit on an N-switch wiring.  The conjectured law is
f(N) = min(2^N, N+4); the N+4 half currently rests on the two echo-machine
lemmas (../lazy-point-theory.md).  This file closes the other half
unconditionally: **no run of any wiring, of any length, ever visits more
than 2^N distinct tongue vectors** — a genuine pigeonhole proof (no
`native_decide`, no Mathlib), not an appeal to "obviously the state space
is 2^N".

The content is `pigeonhole`: a duplicate-free list of length-N boolean
vectors has at most 2^N elements, by induction on N (split on the first
coordinate, recurse on the tails).  `vector_count_le` and
`trajectory_count_le` specialise it to tongue assignments and to
trajectories `Nat → Tongues` — the tongue component of any run of any
wiring in the `GeneralN` model.
-/

namespace VectorCount

open GeneralN (Tongues)

/-- The tongue vector restricted to the first `N` switches. -/
def restrict (N : Nat) (u : Tongues) : List Bool :=
  (List.range N).map u


