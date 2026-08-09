import TrackTheta
import VectorCount

/-!
# The state law — the target theorem, in the language of tracks and switches

This file states the actual claim about trains, tracks and switches.
**`StateLaw` is OPEN — its specific `N + 6` bound is not proved.**
What is now proved is the unconditional general linear bound `17*N+5`
(`state_law_linear_seventeen` in `StateLawSeventeen.lean`, via the
novelty-aware overlap lasso over the `15*N+2` protected repair; it
supersedes the `18*N+3`, `24*N+5` and `26*N+3` predecessors), as well as
the elementary
`2 ^ N` bound (`state_law_two_pow` below).  The coefficient-one improvement
from `17*N+5` to `N+O(1)` is the remaining problem.

The direct physical-track route in `TrackTrace`, `TrackLobe`, `TrackNormalForm`,
`TrackTheta`, `TrackGlobalRepair`, `TrackQuantitative`, and
`TrackQuantitativeTight` close the global
two-component assembly, retains explicit lasso lengths, and proves the final
`26*N+3` tongue-vector count.  `StateLaw` stays explicitly open because it asks
for the much sharper `N+6` count.

## How to read the statement

* A **wiring** `w` is a track layout: switch `k` owns three ports —
  its stem `3*k`, its left branch `3*k+1`, its right branch `3*k+2` —
  and `w.link` records which port is track-connected to which.  It is
  symmetric because physical track is.
* `hN` says the layout uses only switches `0 … N-1`.
* A **state** is `(p, u)`: the train entering port `p` with tongue
  vector `u` (`u j` = the tongue of switch `j`).  One `step` applies
  the lazy-point rule, written in `GeneralN.arrive`:
  entering a stem, the train exits by the branch the tongue selects
  and no tongue moves; entering a branch, that switch's tongue is
  pushed to that branch and the train exits by the stem.  Then the
  exit port's track connection gives the next entry port (`none` = the
  train falls off an unconnected end).
* `stepN w k c0` is the state after `k` steps from `c0`; `hlive` says
  the train is still on the track at each counted time.
* `VectorCount.restrict N u` is the list `[u 0, …, u (N-1)]` — the
  positions of the `N` tongues.
* `Nodup` says the tongue vectors at the times `ks` are pairwise
  distinct.

So `StateLaw` reads: **a single train, on any lazy-point layout with
`N` switches, starting anywhere, ever sees at most `N + 6` distinct
switch settings.**  (Exhaustive checking suggests the sharp constant
is `N + 4`; any constant would settle the open problem.)
-/

namespace GeneralN

/-- The tongue vector at time `k` of the run from `c0`. -/
def tonguesAt (w : Wiring) (c0 : Nat × Tongues) (k : Nat) : Tongues :=
  ((stepN w k c0).getD c0).2

/-- **THE STATE LAW.  OPEN.**  A single train on any `N`-switch
lazy-point layout visits at most `N + 6` distinct tongue vectors. -/
def StateLaw : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (c0 : Nat × Tongues) (ks : List Nat),
      (∀ k ∈ ks, (stepN w k c0).isSome) →
      (ks.map fun k => VectorCount.restrict N (tonguesAt w c0 k)).Nodup →
      ks.length ≤ N + 6

/-- The elementary exponential bound on exactly the same statement, **proved**.
`GeneralN.state_law_linear_seventeen` supersedes it
asymptotically with `17*N+5`; the open gap is now `17*N+5` versus
`N+6`. -/
theorem state_law_two_pow (w : Wiring) (N : Nat)
    (_hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (c0 : Nat × Tongues) (ks : List Nat)
    (_hlive : ∀ k ∈ ks, (stepN w k c0).isSome)
    (hnd : (ks.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).Nodup) :
    ks.length ≤ 2 ^ N :=
  VectorCount.trajectory_count_le N (tonguesAt w c0) ks hnd

end GeneralN
