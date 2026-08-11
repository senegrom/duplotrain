import KnownEdgeLift

/-! Boundary-sharp unconditional coefficient-3 linear bound. -/

namespace GeneralN

/-- **Improved unconditional linear state bound:** every live `N`-switch run
has at most `3*N+7` pairwise-distinct restricted tongue vectors. -/
theorem state_law_linear_three_sharp
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 3 * N + 7 := by
  apply arbitrary_start_distinct_le_succ_of_known_edge
    (cap := 3 * N + 6) hN (by omega)
  · intro e localStart finish hlong hentry localTimes
      hlocalLive hlocalNodup
    exact known_edge_long_run_distinct_le_three_sharp
      hN hlong hentry localTimes hlocalLive hlocalNodup
  · exact hlive
  · exact hnd

end GeneralN
