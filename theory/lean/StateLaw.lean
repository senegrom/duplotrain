import StateLawNAddFourSharp
import StateLawLowerBound
import StateLawSmallN

/-!
# THE STATE LAW: `f(N) = min(2^N, N + 4)`

The single theorem of this development.  `state_law` says the maximum
number of distinct switch settings a single train can visit on a layout
of `N` lazy-point switches is exactly `min(2^N, N + 4)`: no run ever
samples more pairwise-distinct restricted tongue vectors, and some layout,
start, and duplicate-free list of live sample times attains the value.
Every other file exists to support this statement.

## How to read the statement

* A **wiring** `w` is a track layout: switch `k` owns three ports —
  its stem `3*k`, its left branch `3*k+1`, its right branch `3*k+2` —
  and `w.link` records which port is track-connected to which.  It is
  symmetric because physical track is.
* The bound `p < 3 * N` says the layout uses only switches `0 … N-1`.
* A **state** is `(p, u)`: the train entering port `p` with tongue
  vector `u` (`u j` = the tongue of switch `j`).  One `step` applies
  the lazy-point rule, written in `GeneralN.arrive`:
  entering a stem, the train exits by the branch the tongue selects
  and no tongue moves; entering a branch, that switch's tongue is
  pushed to that branch and the train exits by the stem.  Then the
  exit port's track connection gives the next entry port (`none` = the
  train falls off an unconnected end).
* `stepN w k c0` is the state after `k` steps from `c0`; liveness says
  the train is still on the track at each counted time.
* `VectorCount.restrict N u` is the list `[u 0, …, u (N-1)]` — the
  positions of the `N` tongues; `Nodup` says the sampled vectors are
  pairwise distinct.

The upper half is `state_law_two_pow` (the finite-state ceiling) with
`state_law_N_add_four` (the sharp symbolic bound); the attainment half is
the empty layout at `N = 0`, the teardrop and dogbone witnesses at
`N = 1, 2`, and the symbolic extremal family from `N = 3` on.
-/

namespace GeneralN

/-- `count` is the exact state count for `N` switches: every run on every
`N`-switch layout samples at most `count` pairwise-distinct restricted
tongue vectors, and some layout, start, and duplicate-free live sample
list attains `count`. -/
def IsExactStateCount (N count : Nat) : Prop :=
  (∀ (w : Wiring),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (c0 : Nat × Tongues) (ks : List Nat),
      (∀ k ∈ ks, (stepN w k c0).isSome) →
      (ks.map fun k => VectorCount.restrict N (tonguesAt w c0 k)).Nodup →
      ks.length ≤ count) ∧
  (∃ w : Wiring,
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) ∧
    ∃ (c0 : Nat × Tongues) (ks : List Nat),
      (∀ k ∈ ks, (stepN w k c0).isSome) ∧
      (ks.map fun k => VectorCount.restrict N (tonguesAt w c0 k)).Nodup ∧
      ks.length = count)

/-- **THE STATE LAW.**  On `N` lazy-point switches the maximum number of
distinct switch settings a single train can visit is exactly
`min(2^N, N + 4)`. -/
theorem state_law (N : Nat) :
    IsExactStateCount N (min (2 ^ N) (N + 4)) := by
  constructor
  · intro w hN c0 ks hlive hnd
    exact Nat.le_min.mpr
      ⟨state_law_two_pow w N c0 ks hnd,
        state_law_N_add_four w N hN c0 ks hlive hnd⟩
  · match N with
    | 0 => exact (by decide : (2:Nat) ^ 0 = min (2 ^ 0) (0 + 4)) ▸
        state_law_lower_bound_zero
    | 1 => exact (by decide : (2:Nat) ^ 1 = min (2 ^ 1) (1 + 4)) ▸
        state_law_lower_bound_one
    | 2 => exact (by decide : (2:Nat) ^ 2 = min (2 ^ 2) (2 + 4)) ▸
        state_law_lower_bound_two
    | n + 3 =>
      exact (Nat.min_eq_right (add_four_le_two_pow (N := n + 3) (by omega))).symm ▸
        state_law_lower_bound (by omega)

end GeneralN
