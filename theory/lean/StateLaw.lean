import TrackTheta
import VectorCount

/-!
# The state law — the target theorem, in the language of tracks and switches

This file states the actual claim about trains, tracks and switches.
**`StateLaw` is proved.**  The downstream theorem
`GeneralN.stateLaw` in `KnownEdgeNAddFiveAlt.lean` has exactly this type.
Its stronger known-incoming-edge core bounds the run by `N+5`; shifting an
arbitrary start past its first successful physical step costs at most the
time-zero vector, giving the raw `N+6` result.  The proof is entirely symbolic
in `N`, with no fixed-`N` enumeration.

The direct physical-track route in `TrackTrace`, `TrackLobe`, `TrackNormalForm`,
`TrackTheta`, `TrackGlobalRepair`, `TrackQuantitative`, and
`TrackQuantitativeTight` close the global two-component assembly, retain
explicit lasso lengths, and prove the older `26*N+3` tongue-vector count.  The
coefficient-one proof in `KnownEdgeNAddFiveAlt.lean` supersedes that bound.

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

/-- **THE STATE LAW.**  A single train on any `N`-switch
lazy-point layout visits at most `N + 6` distinct tongue vectors. -/
def StateLaw : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (c0 : Nat × Tongues) (ks : List Nat),
      (∀ k ∈ ks, (stepN w k c0).isSome) →
      (ks.map fun k => VectorCount.restrict N (tonguesAt w c0 k)).Nodup →
      ks.length ≤ N + 6

/-- The elementary exponential bound on exactly the same statement.  The
proved coefficient-one theorem `GeneralN.stateLaw` supersedes it with `N+6`. -/
theorem state_law_two_pow (w : Wiring) (N : Nat)
    (_hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (c0 : Nat × Tongues) (ks : List Nat)
    (_hlive : ∀ k ∈ ks, (stepN w k c0).isSome)
    (hnd : (ks.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).Nodup) :
    ks.length ≤ 2 ^ N :=
  VectorCount.trajectory_count_le N (tonguesAt w c0) ks hnd

end GeneralN
