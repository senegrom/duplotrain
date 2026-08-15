import KnownEdgeLift

/-!
# Arbitrary-start lift without a long-run hypothesis

A successful first step exposes the physical edge just crossed.  Therefore an
all-runs bound for starts with a known incoming edge applies immediately to all
positive sample times after shifting them down by one.  Time zero contributes
at most one additional restricted tongue vector.

Unlike `arbitrary_start_distinct_le_succ_of_known_edge`, this lift has no
`3 * N + 3` survival split and no arithmetic side condition: its known-edge
hypothesis already covers runs of every length.
-/

namespace GeneralN

/-- If every run whose starting entry has a known incoming physical edge has
at most `cap` distinct restricted tongue vectors, then a run starting at an
arbitrary entry has at most `cap + 1`.  No long-run or short-run hypothesis is
needed: after one successful step the edge just traversed witnesses the
known-edge premise, and only the time-zero vector lies outside the shifted
tail. -/
theorem arbitrary_start_distinct_le_succ_of_all_known_edge
    {w : Wiring} {N cap : Nat}
    (hknown : ∀ {e : Nat} {localStart : Nat × Tongues},
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
  cases hone : stepN w 1 start with
  | none =>
      have hzero : ∀ k ∈ times, k = 0 := by
        intro k hk
        by_cases hk0 : k = 0
        · exact hk0
        · have hkPos : 0 < k := by omega
          have hkEq : k = 1 + (k - 1) := by omega
          have hnone : stepN w k start = none := by
            rw [hkEq, stepN_add, hone]
            simp
          have hkLive := hlive k hk
          simp [hnone] at hkLive
      have hlen : times.length ≤ 1 :=
        nodup_nat_lt_length htimesNodup (by
          intro k hk
          have := hzero k hk
          omega)
      omega
  | some middle =>
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
            hknown hlink shifted hshiftedLive hshiftedNodup
          have hpositiveLength : positive.length = shifted.length := by
            simp [shifted]
          have hzeroBound :
              (times.filter (fun k => decide (k = 0))).length ≤ 1 :=
            kel_zero_filter_length_le_one htimesNodup
          have hpartition := kel_zero_positive_partition times
          dsimp [positive] at hpositiveLength
          omega

end GeneralN
