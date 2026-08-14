import ArbitraryStartDirectLift
import ProtectedRepairFour

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
  apply arbitrary_start_distinct_le_succ_of_all_known_edge
    (cap := 2 * N + 6)
  · intro e localStart hentry localTimes hlocalLive hlocalNodup
    have hc := known_edge_all_run_distinct_le_of_protected_cap
      hN (tailCap := 4) (by omega)
      (fun A B hA hB tailTimes htailLive htailNodup =>
        manufactured_pair_protected_repair_distinct_le_four
          A B hA hB tailTimes htailLive htailNodup)
      hentry localTimes hlocalLive hlocalNodup
    omega
  · exact hlive
  · exact hnd

end GeneralN
