import ProtectedRepairConstant
import FirstCycleCountSharp
import OneJourneyTailCount
import TwoJourneyBoundaryTailCount

/-!
# Known-edge coefficient-2 linear bound

The tongue-vector cost of a known-edge run is now dominated entirely by
its manufacturing histories: each first-activation attempt either settles
on a simple cycle (`N+2` vectors, `first_activated_count_outcome_sharp`)
or delivers a reflector via its `N+2` construction history, and once both
reflectors stand the protected repair costs a constant six.  Known-edge:
`2*N+8`.
-/

namespace GeneralN

private theorem ket_nodup_of_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

/-- **Robust known-edge coefficient-2 bound** — no long-run liveness
hypothesis.  Whenever the run dies, the samples up to that point are a
position window no larger than the structural counts it replaces. -/
theorem known_edge_distinct_le_two_robust
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 8 := by
  have htimesNodup : times.Nodup :=
    ket_nodup_of_map_nodup (restrictedTonguesAt w N start) hnd
  cases hliveA : stepN w (N + 1) start with
  | none =>
      have hlt : ∀ k ∈ times, k < N + 1 := by
        intro k hk
        by_cases hsmall : k < N + 1
        · exact hsmall
        · have hkEq : k = (N + 1) + (k - (N + 1)) := by omega
          have hnone : stepN w k start = none := by
            rw [hkEq, stepN_add, hliveA]
            simp
          have hkLive := hlive k hk
          simp [hnone] at hkLive
      have hshort := nodup_nat_lt_length htimesNodup hlt
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp hN hliveA hentry with
        hcycleA | hreflectorA
      · have hcount := hcycleA times hnd
        omega
      · obtain ⟨A, stateA, hfirstLe, hgroovesA,
          hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
        cases hliveB : stepN w (N + 1) (e, stateA) with
        | none =>
            have htail : ∀ (tailTimes : List Nat),
                (∀ k ∈ tailTimes,
                  (stepN w k (e, stateA)).isSome) →
                (tailTimes.map
                  (restrictedTonguesAt w N (e, stateA))).Nodup →
                tailTimes.length ≤ N + 1 := by
              intro tailTimes htailLive htailNodup
              have htailNodup' : tailTimes.Nodup :=
                ket_nodup_of_map_nodup
                  (restrictedTonguesAt w N (e, stateA)) htailNodup
              have hlt : ∀ k ∈ tailTimes, k < N + 1 := by
                intro k hk
                by_cases hsmall : k < N + 1
                · exact hsmall
                · have hkEq : k = (N + 1) + (k - (N + 1)) := by
                    omega
                  have hnone : stepN w k (e, stateA) = none := by
                    rw [hkEq, stepN_add, hliveB]
                    simp
                  have hkLive := htailLive k hk
                  simp [hnone] at hkLive
              exact nodup_nat_lt_length htailNodup' hlt
            have hcount :=
              one_manufacturing_journey_then_direct_tail_distinct_le
                (tailCap := N + 1)
                hN A stateA hbaseA hactivatedA hreachA hgroovesA
                htail times hlive hnd
            omega
        | some secondFinish =>
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
                hbaseB, hactivatedB, hreachB, _hpreservesB⟩ :=
                hreflectorB
              have hAatBase :
                  PathGrooves A.toSupported.paths B.baseState := by
                simpa [hbaseB] using hgroovesA
              have hBatActivated :
                  PathGrooves B.toSupported.paths B.activatedState := by
                simpa [← hactivatedB] using hgroovesB
              have htail : ∀ (tailTimes : List Nat),
                  (∀ k ∈ tailTimes,
                    (stepN w k (start.1, stateB)).isSome) →
                  (tailTimes.map
                    (restrictedTonguesAt w N
                      (start.1, stateB))).Nodup →
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
                  hN A B hAatBase hBatActivated tailTimes
                    htailLive' htailNodup'
              have hcount :=
                two_manufacturing_journeys_then_boundary_tail_distinct_le
                  (tailCap := 6)
                  hN A B stateA stateB hbaseA hactivatedA hreachA
                  hgroovesA hbaseB hactivatedB hreachB hgroovesB
                  htail (by omega) times hlive hnd
              omega

/-- Known-edge long-run coefficient-2 bound. -/
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
          hN A B hAatBase hBatActivated tailTimes
            htailLive' htailNodup'
      have hcount :=
        two_manufacturing_journeys_then_boundary_tail_distinct_le
          (tailCap := 6)
          hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
          hbaseB hactivatedB hreachB hgroovesB htail (by omega)
          times hlive hnd
      omega

end GeneralN
