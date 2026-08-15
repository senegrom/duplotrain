import TwoJourneyTailCountSharp

/-!
# One manufacturing journey followed by a directly counted tail

A manufactured activation is charged by its actual tongue-vector history
(`N+2`), not by its physical travel (`2*N+1`).  This is the one-component
analogue of `two_manufacturing_journeys_then_direct_tail_distinct_le`.
-/

namespace GeneralN

/-- A complete manufactured journey followed by a suffix with direct vector
cap `tailCap` exposes at most `N+2+tailCap` distinct restricted vectors. -/
theorem one_manufacturing_journey_then_direct_tail_distinct_le
    {w : Wiring} {N e tailCap : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (A : ManufacturedReflector w start.1 e)
    (stateA : Tongues)
    (hbaseA : A.baseState = start.2)
    (hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hgroovesA : PathGrooves A.toSupported.paths stateA)
    (htail : ∀ (tailTimes : List Nat),
      (∀ k ∈ tailTimes,
        (stepN w k (e, stateA)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (e, stateA))).Nodup →
      tailTimes.length ≤ tailCap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 2 + tailCap := by
  let travel := A.exploration.length + A.runway.length + 1
  have hreach : stepN w travel start = some (e, stateA) := by
    simpa [travel] using hreachA
  have hgroovesActivated :
      PathGrooves A.toSupported.paths A.activatedState := by
    rw [← hactivatedA]
    exact hgroovesA
  let preTimes := times.filter (fun k => decide (k < travel))
  let postTimes := times.filter (fun k => decide (travel ≤ k))
  let shifted := postTimes.map (fun k => k - travel)
  have hpreNodup :
      (preTimes.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [preTimes]
    exact tailsharp_nodup_map_filter _ hnd
  have hpreRange : ∀ k ∈ preTimes,
      k ≤ A.exploration.length + A.runway.length + 1 := by
    intro k hk
    have hklt : k < travel :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    dsimp [travel] at hklt
    omega
  have hpreBound : preTimes.length ≤ N + 2 := by
    have hlocal := A.manufacturing_journey_distinct_le_N_add_two
      hN hgroovesActivated preTimes hpreRange
        (by simpa [hbaseA] using hpreNodup)
    exact hlocal
  have hpostNodup :
      (postTimes.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [postTimes]
    exact tailsharp_nodup_map_filter _ hnd
  have hshiftVector : shifted.map
      (restrictedTonguesAt w N (e, stateA)) =
      postTimes.map (restrictedTonguesAt w N start) := by
    dsimp [shifted]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkGe : travel ≤ k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkEq : k = travel + (k - travel) := by omega
    have hkLive := hlive k hkTimes
    have hrun : stepN w k start =
        stepN w (k - travel) (e, stateA) := by
      rw [hkEq, stepN_add, hreach]
      simp
    cases htailRun : stepN w (k - travel) (e, stateA) with
    | none =>
        rw [hrun, htailRun] at hkLive
        simp at hkLive
    | some finish =>
        have hglobal : stepN w k start = some finish := by
          rw [hrun, htailRun]
        simp [Function.comp_apply, restrictedTonguesAt, tonguesAt,
          hglobal, htailRun]
  have hshiftNodup :
      (shifted.map
        (restrictedTonguesAt w N (e, stateA))).Nodup := by
    rw [hshiftVector]
    exact hpostNodup
  have hshiftLive : ∀ d ∈ shifted,
      (stepN w d (e, stateA)).isSome := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkGe : travel ≤ k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkEq : k = travel + (k - travel) := by omega
    have hkLive := hlive k hkTimes
    rw [hkEq, stepN_add, hreach] at hkLive
    exact hkLive
  have hshiftBound : shifted.length ≤ tailCap :=
    htail shifted hshiftLive hshiftNodup
  have hpostLength : postTimes.length = shifted.length := by
    simp [shifted]
  have hpartition := tailsharp_lt_ge_partition travel times
  dsimp [preTimes, postTimes] at hpartition hpreBound hpostLength
  omega

end GeneralN
