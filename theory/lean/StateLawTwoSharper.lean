import KnownEdgeTwoSharper
import KnownEdgeAllLift

/-! Current sharp coefficient-two unconditional state bound. -/

namespace GeneralN

/-- **Unconditional `2*N+7` state bound.** -/
theorem state_law_linear_two_sharper
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 7 := by
  apply arbitrary_start_distinct_le_succ_of_known_edge_all
    (cap := 2 * N + 6)
  · intro e localStart hentry localTimes hlocalLive hlocalNodup
    exact known_edge_all_run_distinct_le_two_add_six
      hN hentry localTimes hlocalLive hlocalNodup
  · exact hlive
  · exact hnd

end GeneralN
