import TwoJourneyTailCountSharp

/-! Known-edge coefficient-15 linear bound by direct tongue counting. -/

namespace GeneralN

/-- Protected repair exposes at most `13*N+3` distinct restricted tongue
vectors, even though its physical lasso may be longer. -/
theorem manufactured_pair_protected_repair_distinct_le_thirteen_succ_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 13 * N + 3 := by
  have hnd' : (times.map (fun k =>
      VectorCount.restrict N
        (tonguesAt w (g, B.activatedState) k))).Nodup := by
    exact hnd
  rcases manufactured_pair_protected_repair_quantitative_outcomes
      hN A B hA hB with hperiodic | hrest
  · have hc := hperiodic.tongue_vector_count times hlive hnd'
    omega
  · rcases hrest with hfacing | hrest
    · have hlocal := hfacing.within_twelve hN
      have hc := hlocal.tongue_vector_count times hlive hnd'
      omega
    · rcases hrest with hchanged | hcomplete
      · have hlocal := hchanged.within_thirteen_sharp hN
        have hc := hlocal.tongue_vector_count times hlive hnd'
        omega
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact A.completed_route_with_pair_support_distinct_le_thirteen_succ_three
          hN B B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal times hlive hnd

/-- Known-edge long-run coefficient-15 bound. -/
theorem known_edge_long_run_distinct_le_fifteen
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlong : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 15 * N + 6 := by
  rcases two_component_quantitative_outcome_exact hN hlong hentry with
    hperiodic | hpair
  · have hsmall := hperiodic.tongue_vector_count times hlive (by
      exact hnd)
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
    have htail : ∀ (tailTimes : List Nat),
        (∀ k ∈ tailTimes,
          (stepN w k (start.1, stateB)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (start.1, stateB))).Nodup →
        tailTimes.length ≤ 13 * N + 3 := by
      intro tailTimes htailLive htailNodup
      rw [hactivatedB]
      exact manufactured_pair_protected_repair_distinct_le_thirteen_succ_three
        hN A B hAatBase hBatActivated tailTimes
          (by simpa [hactivatedB] using htailLive)
          (by simpa [hactivatedB] using htailNodup)
    have hassembled :=
      two_manufacturing_journeys_then_direct_tail_distinct_le
        (tailCap := 13 * N + 3)
        hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
        hbaseB hactivatedB hreachB hgroovesB htail times hlive hnd
    omega

end GeneralN
