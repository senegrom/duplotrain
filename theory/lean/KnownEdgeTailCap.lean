import KnownEdgeTwoAll
import ProtectedRepairFive

/-!
# All-run known-edge bound parameterized by the protected-repair cap

The two incomplete-construction and simple-cycle branches cost at most
`2*N+4`.  When both opposite reflectors are manufactured, boundary-shared
construction histories cost `2*N+2`, followed by the supplied protected
suffix cap.  Hence every cap of at least two gives `2*N+tailCap+2`.
-/

namespace GeneralN

private theorem ketc_nodup_of_map_nodup
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

private theorem ketc_live_distinct_le_of_stepN_none
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    {times : List Nat}
    (hnone : stepN w L start = none)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ L := by
  have htimesNodup : times.Nodup :=
    ketc_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  apply nodup_nat_lt_length htimesNodup
  intro k hk
  by_cases hlt : k < L
  · exact hlt
  · have hkEq : k = L + (k - L) := by omega
    have hnoneK : stepN w k start = none := by
      rw [hkEq, stepN_add, hnone]
      simp
    have hkLive := hlive k hk
    rw [hnoneK] at hkLive
    simp at hkLive

/-- General all-run known-edge assembly from a direct protected-repair cap. -/
theorem known_edge_all_run_distinct_le_of_protected_cap
    {w : Wiring} {N tailCap : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hcap : 2 ≤ tailCap)
    (hprotected : ∀ {g e : Nat}
      (A : ManufacturedReflector w g e)
      (B : ManufacturedReflector w e g),
      PathGrooves A.toSupported.paths B.baseState →
      PathGrooves B.toSupported.paths B.activatedState →
      ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (g, B.activatedState)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N
            (g, B.activatedState))).Nodup →
        tailTimes.length ≤ tailCap)
    {e : Nat} {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + tailCap + 2 := by
  cases hfirst : stepN w (N + 1) start with
  | none =>
      have hc := ketc_live_distinct_le_of_stepN_none
        (N := N) hfirst hlive hnd
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycleA | hreflectorA
      · have hc := hcycleA times hnd
        omega
      · obtain ⟨A, stateA, _hfirstLe, hgroovesA,
          hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
        have hentryB : w.link start.1 = some e :=
          w.symm _ _ A.entryEdge
        cases hsecond : stepN w (N + 1) (e, stateA) with
        | none =>
            have htail : ∀ (tailTimes : List Nat),
                (∀ k ∈ tailTimes,
                  (stepN w k (e, stateA)).isSome) →
                (tailTimes.map
                  (restrictedTonguesAt w N (e, stateA))).Nodup →
                tailTimes.length ≤ N + 1 := by
              intro tailTimes htailLive htailNodup
              exact ketc_live_distinct_le_of_stepN_none
                (N := N) hsecond htailLive htailNodup
            have hc := one_manufacturing_journey_then_direct_tail_distinct_le
              (tailCap := N + 1)
              hN A stateA hbaseA hactivatedA hreachA hgroovesA
              htail times hlive hnd
            omega
        | some secondFinish =>
            rcases first_activated_count_outcome_sharp
                (w := w) (N := N) (e := start.1)
                hN hsecond hentryB with hcycleB | hreflectorB
            · have htail : ∀ (tailTimes : List Nat),
                  (∀ k ∈ tailTimes,
                    (stepN w k (e, stateA)).isSome) →
                  (tailTimes.map
                    (restrictedTonguesAt w N (e, stateA))).Nodup →
                  tailTimes.length ≤ N + 2 := by
                intro tailTimes _htailLive htailNodup
                exact hcycleB tailTimes htailNodup
              have hc := one_manufacturing_journey_then_direct_tail_distinct_le
                (tailCap := N + 2)
                hN A stateA hbaseA hactivatedA hreachA hgroovesA
                htail times hlive hnd
              omega
            · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                  hbaseB, hactivatedB, hreachB,
                  _hpreservesB⟩ := hreflectorB
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
                  tailTimes.length ≤ tailCap := by
                intro tailTimes htailLive htailNodup
                have htailLive' : ∀ k ∈ tailTimes,
                    (stepN w k
                      (start.1, B.activatedState)).isSome := by
                  simpa [← hactivatedB] using htailLive
                have htailNodup' :
                    (tailTimes.map
                      (restrictedTonguesAt w N
                        (start.1, B.activatedState))).Nodup := by
                  simpa [← hactivatedB] using htailNodup
                exact hprotected A B hAatBase hBatActivated
                  tailTimes htailLive' htailNodup'
              have hc :=
                two_manufacturing_journeys_then_boundary_tail_distinct_le
                  hN A B stateA stateB hbaseA hactivatedA
                  hreachA hgroovesA hbaseB hactivatedB hreachB
                  hgroovesB htail (by omega) times hlive hnd
              omega

/-- Five protected vectors give the sharp known-edge coefficient-two
constant `2*N+7`. -/
theorem known_edge_all_run_distinct_le_two_add_seven
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 7 := by
  have hc := known_edge_all_run_distinct_le_of_protected_cap
    hN (tailCap := 5) (by omega)
    (fun A B hA hB tailTimes htailLive htailNodup =>
      manufactured_pair_protected_repair_distinct_le_five
        A B hA hB tailTimes htailLive htailNodup)
    hentry times hlive hnd
  omega

end GeneralN
