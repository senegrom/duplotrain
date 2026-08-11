import FirstCycleCountSharp
import ProtectedRepairConstant
import OneJourneyTailCount
import TwoJourneyBoundaryTailCount

/-!
# Known-edge coefficient-two linear bound

The first simple-cycle outcome costs `N+2`.  If one reflector is manufactured
and the opposite exploration settles on a simple cycle, the manufacturing
history plus that cycle costs at most `2*N+4`.  If both reflectors are
manufactured, their boundary-shared histories cost `2*N+2` and the protected
repair suffix costs six, giving the uniform `2*N+8` bound.
-/

namespace GeneralN

/-- **Known-edge coefficient-two bound:** every sufficiently long live run
with a known incoming edge visits at most `2*N+8` distinct restricted tongue
vectors. -/
theorem known_edge_long_run_distinct_le_two
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlong : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 8 := by
  have hsplit :
      stepN w ((N + 1) + (2 * N + 1)) start = some finish := by
    have hlen : (N + 1) + (2 * N + 1) = 3 * N + 2 := by omega
    rw [hlen]
    exact hlong
  obtain ⟨firstFinish, hliveA, _⟩ := stepN_split_some hsplit
  rcases first_activated_count_outcome_sharp hN hliveA hentry with
    hcycleA | hreflectorA
  · have hcount := hcycleA times hnd
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
    rcases first_activated_count_outcome_sharp
        (w := w) (N := N) (e := start.1)
        hN hliveB hentryB with hcycleB | hreflectorB
    · have htail : ∀ (tailTimes : List Nat),
          (∀ k ∈ tailTimes,
            (stepN w k (e, stateA)).isSome) →
          (tailTimes.map
            (restrictedTonguesAt w N (e, stateA))).Nodup →
          tailTimes.length ≤ N + 2 := by
        intro tailTimes _htailLive htailNodup
        exact hcycleB tailTimes htailNodup
      have hcount :=
        one_manufacturing_journey_then_direct_tail_distinct_le
          (tailCap := N + 2)
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
          tailTimes.length ≤ 6 := by
        intro tailTimes htailLive htailNodup
        have htailLive' : ∀ k ∈ tailTimes,
            (stepN w k (start.1, B.activatedState)).isSome := by
          simpa [← hactivatedB] using htailLive
        have htailNodup' :
            (tailTimes.map
              (restrictedTonguesAt w N
                (start.1, B.activatedState))).Nodup := by
          simpa [← hactivatedB] using htailNodup
        exact manufactured_pair_protected_repair_distinct_le_six
          A B hAatBase hBatActivated tailTimes
            htailLive' htailNodup'
      have hcount :=
        two_manufacturing_journeys_then_boundary_tail_distinct_le
          (tailCap := 6)
          hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
          hbaseB hactivatedB hreachB hgroovesB htail (by omega)
          times hlive hnd
      omega

end GeneralN
