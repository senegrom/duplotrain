import KnownEdgeFive
import OneJourneyTailCount

/-!
# Known-edge coefficient-4 linear bound

The old coefficient-five proof prepended the first reflector's physical
`2*N+1` journey to a `3*N` periodic suffix.  The journey itself contains only
`N+2` distinct tongue vectors.  Counting it directly makes the second-periodic
branch `4*N+2`; the two-reflector branch remains `4*N+8`.
-/

namespace GeneralN

/-- **Known-edge coefficient-four bound.** -/
theorem known_edge_long_run_distinct_le_four
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlong : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 4 * N + 8 := by
  have hsplit :
      stepN w ((N + 1) + (2 * N + 1)) start = some finish := by
    have hlen : (N + 1) + (2 * N + 1) = 3 * N + 2 := by omega
    rw [hlen]
    exact hlong
  obtain ⟨firstFinish, hliveA, _⟩ := stepN_split_some hsplit
  rcases first_activated_quantitative_outcome_exact hN hliveA hentry with
    hperiodicA | hreflectorA
  · have hcount := hperiodicA.tongue_vector_count times hlive hnd
    omega
  · obtain ⟨A, stateA, hfirstLe, hgroovesA,
      hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
    let firstTravel := A.exploration.length + A.runway.length + 1
    obtain ⟨secondFinish, hliveB⟩ :=
      stepN_live_after_reached hreachA hlong (by
        dsimp [firstTravel]
        omega : firstTravel + (N + 1) ≤ 3 * N + 2)
    have hentryB : w.link start.1 = some e :=
      w.symm _ _ A.entryEdge
    rcases first_activated_quantitative_outcome_exact
        (w := w) (N := N) (e := start.1)
        hN hliveB hentryB with hperiodicB | hreflectorB
    · have htail : ∀ (tailTimes : List Nat),
          (∀ k ∈ tailTimes,
            (stepN w k (e, stateA)).isSome) →
          (tailTimes.map
            (restrictedTonguesAt w N (e, stateA))).Nodup →
          tailTimes.length ≤ 3 * N := by
        intro tailTimes htailLive htailNodup
        exact hperiodicB.tongue_vector_count
          tailTimes htailLive htailNodup
      have hcount :=
        one_manufacturing_journey_then_direct_tail_distinct_le
          (tailCap := 3 * N)
          hN A stateA hbaseA hactivatedA hreachA hgroovesA
          htail times hlive hnd
      omega
    · obtain ⟨B, stateB, hsecondLe, hgroovesB,
        hbaseB, hactivatedB, hreachB, _hpreservesB⟩ := hreflectorB
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
          tailTimes.length ≤ 2 * N + 5 := by
        intro tailTimes htailLive htailNodup
        have htailLive' : ∀ k ∈ tailTimes,
            (stepN w k (start.1, B.activatedState)).isSome := by
          simpa [← hactivatedB] using htailLive
        have htailNodup' :
            (tailTimes.map
              (restrictedTonguesAt w N
                (start.1, B.activatedState))).Nodup := by
          simpa [← hactivatedB] using htailNodup
        exact manufactured_pair_protected_repair_distinct_le_two_mul_add_five
          hN A B hAatBase hBatActivated tailTimes
            htailLive' htailNodup'
      have hcount :=
        two_manufacturing_journeys_then_direct_tail_distinct_le
          (tailCap := 2 * N + 5)
          hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
          hbaseB hactivatedB hreachB hgroovesB htail times hlive hnd
      omega

end GeneralN
