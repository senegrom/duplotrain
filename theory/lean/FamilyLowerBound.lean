import DuplotrainProofs

/-!
# The `N+4` lower-bound family

The sharp-constant conjecture says `f(N) = min(2^N, N+4)`.  The upper
side is proved to `N+6` (`GeneralN.stateLaw`); this file pins the lower
side beyond the exhaustive `N ≤ 4` sweeps with an explicit parametric
family that realizes `N+4` at every tested size:

* switch `0` is a teardrop — its branches are tied together and its stem
  feeds the chain;
* switches `1 … N-3` form a stem-to-branch chain;
* switches `N-2, N-1` are doubly linked (branch→stem and
  branch→branch), the four-vector Gray oscillator.

A cold run explores the chain, minting one fresh vector per switch, and
the end pair sustains the four-corner oscillation: `N+4` distinct tongue
vectors.  Each instance below is a single-wiring `native_decide`
evaluation of the same `maxStates` used by the exhaustive sweeps.
(Discovered and cross-checked externally by `../tools/bstates.py`,
including a 60,000-wiring random probe at `N=5` in which no wiring
exceeded `9 = N+4`.)
-/

namespace Duplotrain

/-- Teardrop, stem-to-branch chain, doubly-linked end pair. -/
def familyEdges (n : Nat) : List (Nat × Nat) :=
  [(0, 3), (1, 2)] ++
  ((List.range (n - 3)).map fun k =>
    (3 * (k + 1) + 2, 3 * (k + 2))) ++
  [(3 * (n - 2) + 1, 3 * (n - 1)),
   (3 * (n - 2) + 2, 3 * (n - 1) + 2)]

/-- The family is connected at every tested size. -/
theorem family_connected :
    ((List.range 8).map fun i =>
      connected (i + 3) (familyEdges (i + 3))).all (· = true) := by
  native_decide

theorem family_states_three :
    maxStates 3 (familyEdges 3, []) = 7 := by native_decide

theorem family_states_four :
    maxStates 4 (familyEdges 4, []) = 8 := by native_decide

/-- `f(5) ≥ 9 = 5+4`: beyond the exhaustive range. -/
theorem family_states_five :
    maxStates 5 (familyEdges 5, []) = 9 := by native_decide

theorem family_states_six :
    maxStates 6 (familyEdges 6, []) = 10 := by native_decide

theorem family_states_seven :
    maxStates 7 (familyEdges 7, []) = 11 := by native_decide

theorem family_states_eight :
    maxStates 8 (familyEdges 8, []) = 12 := by native_decide

end Duplotrain
