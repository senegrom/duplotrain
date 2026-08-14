import ManufacturedPairNovelty
import NoveltyAwareLasso

/-!
# Tongue-count sharpening for reflector pairs

Physical travel is a poor proxy for tongue-vector novelty.  A complete
manufactured-reflector traversal has exactly two tongue phases, regardless
of its geometric length.  If the endpoint starts a bounded lasso, the second
phase is already time zero of that lasso.  Thus the complete prefix costs
only one additional vector above the lasso history.
-/

namespace GeneralN

private theorem pairsharp_zero_novelty_cover_of_mem
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (times : List Nat) (history : List (List Bool))
    (hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history) :
    NoveltyCoverOn w N start times history 0 := by
  refine ⟨[], by simp, ?_⟩
  intro k hk
  simpa using hmem k hk

/-- A complete manufactured-reflector traversal followed by a `cap`-lasso
exposes at most `cap+1` distinct restricted tongue vectors.  The entire
reflector traversal contributes only its incoming vector beyond the suffix
history, because its outgoing action-state is exactly suffix time zero. -/
theorem ManufacturedReflector.traversal_then_lasso_distinct_le_succ
    {w : Wiring} {N g e cap : Nat}
    (A : ManufacturedReflector w g e)
    (state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    (hlocal : EventuallyPeriodicWithin w
      (e, A.toSupported.action.apply state) cap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k (g, state)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ cap + 1 := by
  let travel := A.toSupported.travel
  let outgoing := A.toSupported.action.apply state
  let incomingVector := VectorCount.restrict N state
  let outgoingVector := VectorCount.restrict N outgoing
  let tailHistory := hlocal.tongueHistory N
  let tailReduced := tailHistory.erase outgoingVector
  let history := [incomingVector, outgoingVector] ++ tailReduced
  have hrun : stepN w travel (g, state) = some (e, outgoing) := by
    dsimp [travel, outgoing]
    exact (A.toSupported.run state hpaths).1
  have houtTail : outgoingVector ∈ tailHistory := by
    have hm := hlocal.mem_tongueHistory (N := N) (k := 0)
    have hzero : restrictedTonguesAt w N (e, outgoing) 0 =
        outgoingVector := by
      dsimp [outgoingVector]
      simp [restrictedTonguesAt, tonguesAt, stepN]
    rw [← hzero]
    simpa [tailHistory, outgoing] using hm
  have hmem : ∀ k ∈ times,
      restrictedTonguesAt w N (g, state) k ∈ history := by
    intro k hk
    by_cases hprefix : k ≤ travel
    · have hphase := A.travel_two_phase_tongues state hpaths hprefix
      rcases hphase with hin | hout
      · dsimp [history]
        simp [restrictedTonguesAt, hin, incomingVector]
      · dsimp [history]
        simp [restrictedTonguesAt, hout, outgoingVector, outgoing]
    · let d := k - travel
      have hkEq : k = travel + d := by
        dsimp [d]
        omega
      have hkLive := hlive k hk
      have hlocalLive : ∃ finish,
          stepN w d (e, outgoing) = some finish := by
        cases hd : stepN w d (e, outgoing) with
        | none =>
            have hnone : stepN w k (g, state) = none := by
              rw [hkEq, stepN_add, hrun]
              simp [hd]
            rw [hnone] at hkLive
            simp at hkLive
        | some finish => exact ⟨finish, rfl⟩
      have hshift := tonguesAt_add_of_reaches hrun hlocalLive
      have hm := hlocal.mem_tongueHistory (N := N) (k := d)
      have hm' : restrictedTonguesAt w N (e, outgoing) d ∈
          tailHistory := by
        simpa [tailHistory, outgoing] using hm
      have heq : restrictedTonguesAt w N (g, state) k =
          restrictedTonguesAt w N (e, outgoing) d := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      by_cases houtEq :
          restrictedTonguesAt w N (e, outgoing) d = outgoingVector
      · dsimp [history]
        simp [houtEq]
      · apply List.mem_append_right [incomingVector, outgoingVector]
        dsimp [tailReduced]
        exact (List.mem_erase_of_ne houtEq).mpr hm'
  have hcover := pairsharp_zero_novelty_cover_of_mem times history hmem
  have hcountRaw := noveltyCoverOn_distinct_count hcover hnd
  have hcount : times.length ≤ history.length := by
    simpa using hcountRaw
  have htailLen : tailHistory.length = cap := by
    simp [tailHistory, EventuallyPeriodicWithin.tongueHistory]
  have htailReducedLen : tailReduced.length = tailHistory.length - 1 := by
    dsimp [tailReduced]
    exact List.length_erase_of_mem houtTail
  have hcapPos : 0 < cap := by
    obtain ⟨lead, period, settled, hperiodPos, hcap,
      _hlead, _hperiod⟩ := hlocal
    omega
  have hhistoryExact : history.length = 2 + tailReduced.length := by
    dsimp [history]
    omega
  have hhistoryLen : history.length ≤ cap + 1 := by
    rw [hhistoryExact, htailReducedLen, htailLen]
    omega
  exact Nat.le_trans hcount hhistoryLen

end GeneralN
