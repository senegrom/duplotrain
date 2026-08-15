import KnownEdgeThreeSharp

/-!
# Generic lift from a known incoming edge

A successful first step exposes the physical edge just crossed.  Positive
sample times can therefore be shifted by one and handed to any known-edge
counting theorem.  Time zero costs at most one further vector.
-/

namespace GeneralN

theorem kel_zero_positive_partition :
    ∀ xs : List Nat,
      (xs.filter (fun k => decide (k = 0))).length +
        (xs.filter (fun k => decide (0 < k))).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons k rest ih =>
      by_cases hk : k = 0
      · subst k
        simp
        omega
      · have hkPos : 0 < k := by omega
        simp [hk, hkPos]
        omega

theorem kel_zero_filter_length_le_one
    {xs : List Nat} (hnd : xs.Nodup) :
    (xs.filter (fun k => decide (k = 0))).length ≤ 1 := by
  have hfilterNodup :
      (xs.filter (fun k => decide (k = 0))).Nodup :=
    nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

/-- Lift any known-edge long-run cap `cap` to an arbitrary-start cap `cap+1`.
The short-run hypothesis is the only arithmetic side condition. -/
theorem arbitrary_start_distinct_le_succ_of_known_edge
    {w : Wiring} {N cap : Nat}
    (hshort : 3 * N + 3 ≤ cap + 1)
    (hknown : ∀ {e : Nat} {localStart finish : Nat × Tongues},
      stepN w (3 * N + 2) localStart = some finish →
      w.link e = some localStart.1 →
      ∀ localTimes : List Nat,
        (∀ k ∈ localTimes, (stepN w k localStart).isSome) →
        (localTimes.map
          (restrictedTonguesAt w N localStart)).Nodup →
        localTimes.length ≤ cap)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ cap + 1 := by
  have htimesNodup : times.Nodup :=
    tailsharp_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  cases hlong : stepN w (3 * N + 3) start with
  | none =>
      have hlt : ∀ k ∈ times, k < 3 * N + 3 := by
        intro k hk
        by_cases hsmall : k < 3 * N + 3
        · exact hsmall
        · have hkge : 3 * N + 3 ≤ k := by omega
          have hkEq : k = (3 * N + 3) + (k - (3 * N + 3)) := by
            omega
          have hnone : stepN w k start = none := by
            rw [hkEq, stepN_add, hlong]
            simp
          have hkLive := hlive k hk
          simp [hnone] at hkLive
      have hsmall := nodup_nat_lt_length htimesNodup hlt
      omega
  | some finish =>
      have hsplit : 3 * N + 3 = 1 + (3 * N + 2) := by omega
      have hlong' := hlong
      rw [hsplit, stepN_add] at hlong'
      cases hone : stepN w 1 start with
      | none =>
          rw [hone] at hlong'
          contradiction
      | some middle =>
          rw [hone] at hlong'
          simp only [Option.bind_some] at hlong'
          rcases start with ⟨startPort, startState⟩
          have honeStep : stepN w 1 (startPort, startState) =
              some middle := hone
          simp only [stepN, step] at hone
          let localStep := arrive startState startPort
          cases hlink : w.link localStep.1 with
          | none =>
              simp [localStep, hlink] at hone
          | some entry =>
              have hmiddle : middle = (entry, localStep.2) := by
                simpa [localStep, hlink] using hone.symm
              subst middle
              let positive := times.filter (fun k => decide (0 < k))
              let shifted := positive.map (fun k => k - 1)
              have hshiftVector : shifted.map
                  (restrictedTonguesAt w N (entry, localStep.2)) =
                  positive.map
                    (restrictedTonguesAt w N (startPort, startState)) := by
                dsimp [shifted]
                rw [List.map_map]
                apply List.map_congr_left
                intro k hk
                have hkPos : 0 < k :=
                  of_decide_eq_true (List.mem_filter.mp hk).2
                have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
                have hkEq : k = 1 + (k - 1) := by omega
                have hrun : stepN w k (startPort, startState) =
                    stepN w (k - 1) (entry, localStep.2) := by
                  rw [hkEq, stepN_add, honeStep]
                  simp
                have hkLive := hlive k hkTimes
                cases htail : stepN w (k - 1) (entry, localStep.2) with
                | none =>
                    rw [hrun, htail] at hkLive
                    simp at hkLive
                | some localFinish =>
                    have hglobal : stepN w k (startPort, startState) =
                        some localFinish := by rw [hrun, htail]
                    simp [Function.comp_apply, restrictedTonguesAt,
                      tonguesAt, hglobal, htail]
              have hpositiveNodup :
                  (positive.map (restrictedTonguesAt w N
                    (startPort, startState))).Nodup := by
                dsimp [positive]
                exact tailsharp_nodup_map_filter _ hnd
              have hshiftedNodup :
                  (shifted.map (restrictedTonguesAt w N
                    (entry, localStep.2))).Nodup := by
                rw [hshiftVector]
                exact hpositiveNodup
              have hshiftedLive : ∀ d ∈ shifted,
                  (stepN w d (entry, localStep.2)).isSome := by
                intro d hd
                obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
                have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
                have hkPos : 0 < k :=
                  of_decide_eq_true (List.mem_filter.mp hk).2
                have hkEq : k = 1 + (k - 1) := by omega
                have hkLive := hlive k hkTimes
                rw [hkEq, stepN_add, honeStep] at hkLive
                exact hkLive
              have hshiftedBound : shifted.length ≤ cap :=
                hknown hlong' hlink shifted hshiftedLive hshiftedNodup
              have hpositiveLength : positive.length = shifted.length := by
                simp [shifted]
              have hzeroBound :
                  (times.filter (fun k => decide (k = 0))).length ≤ 1 :=
                kel_zero_filter_length_le_one htimesNodup
              have hpartition := kel_zero_positive_partition times
              dsimp [positive] at hpositiveLength
              omega

end GeneralN
