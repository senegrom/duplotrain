import TrackQuantitativeRepairEighteen
import NoveltyAwareLassoTwenty

/-! Known-edge coefficient-20 linear bound. -/

namespace GeneralN

/-- Known-edge long-run form of the `20*N+2` bound. -/
theorem known_edge_long_run_distinct_le_twenty
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlong : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 20 * N + 2 := by
  rcases two_component_quantitative_outcome_exact hN hlong hentry with
    hperiodic | hpair
  · have hsmall := hperiodic.tongue_vector_count times hlive hnd
    omega
  · obtain ⟨A, B, stateA, stateB,
      _hfirstLe, _hsecondLe, hbaseA, hactivatedA,
      hreachA, hgroovesA, hbaseB, hactivatedB,
      hreachB, hgroovesB, _hpreservesB⟩ := hpair
    have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
      simpa [hbaseB] using hgroovesA
    have hBatActivated :
        PathGrooves B.toSupported.paths B.activatedState := by
      simpa [← hactivatedB] using hgroovesB
    have hlocal := manufactured_pair_protected_repair_within_eighteen
      hN A B hAatBase hBatActivated
    rw [← hactivatedB] at hlocal
    exact two_manufacturing_journeys_then_repair_distinct_le_twenty
      hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
      hbaseB hactivatedB hreachB hgroovesB hlocal times hlive hnd

end GeneralN
