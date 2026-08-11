import KnownEdgeTailCap
import ProtectedRepairFour

/-! Known-edge coefficient-two bound with four protected tail vectors. -/

namespace GeneralN

/-- **Known-edge `2*N+6` bound.** -/
theorem known_edge_all_run_distinct_le_two_add_six
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 6 := by
  have hc := known_edge_all_run_distinct_le_of_protected_cap
    hN (tailCap := 4) (by omega)
    (fun A B hA hB tailTimes htailLive htailNodup =>
      manufactured_pair_protected_repair_distinct_le_four
        A B hA hB tailTimes htailLive htailNodup)
    hentry times hlive hnd
  omega

end GeneralN
