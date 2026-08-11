import KnownEdgeAllLift

/-! Unconditional coefficient-two linear state bound. -/

namespace GeneralN

/-- **Coefficient-two unconditional state bound:** every live `N`-switch run
visits at most `2*N+9` pairwise-distinct restricted tongue vectors. -/
theorem state_law_linear_two
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 9 := by
  apply arbitrary_start_distinct_le_succ_of_known_edge_all
    (cap := 2 * N + 8)
  · intro e localStart hentry localTimes hlocalLive hlocalNodup
    exact known_edge_all_run_distinct_le_two
      hN hentry localTimes hlocalLive hlocalNodup
  · exact hlive
  · exact hnd

end GeneralN
