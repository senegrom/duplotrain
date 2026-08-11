import CompleteRepairConstant
import PairActionCorners
import SingleCoordinateFlip

/-!
# Four-vector complete protected repair

A complete repair prefix changes only the protected reflector's final return
coordinate.  For a flip reflector its initial phase is therefore either the
repaired state or exactly the protected action applied to that state.  For a
stay reflector both states groove the core passage, so even that coordinate
cannot differ.  Both prefix phases are consequently among the restored pair's
four explicit action corners, and the complete branch costs four vectors
rather than five.
-/

namespace GeneralN

/-- The protected initial state is the repaired state or the protected local
action applied to it. -/
theorem ManufacturedReflector.completed_repair_initial_action_relation
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState))
    (hBfinal : PathGrooves B.toSupported.paths finalState) :
    B.activatedState = finalState ∨
      B.activatedState = B.toSupported.action.apply finalState := by
  have hsimple := A.orientedRoute_simple B.activatedState
  have hroute : ∀ passage ∈ A.orientedRoute B.activatedState,
      passage ∈ A.orientedRoute B.activatedState := by
    intro passage hp
    exact hp
  have hchanges := A.repair_prefix_changes_only_protected_return
    B hA hB hrepair hsimple hroute hBfinal
  cases B with
  | stay R =>
      have hchanges' : ∀ j, finalState j ≠ R.returnState j →
          j = R.arm / 3 := by
        intro j hj
        have h := hchanges j (by simpa using hj)
        change j = R.arm / 3 at h
        exact h
      have hrelation :
          R.returnState = finalState ∨
            R.returnState = flipAt finalState (R.arm / 3) :=
        tongues_eq_or_eq_flipAt_of_changes_only
          (u := R.returnState) (v := finalState)
          (k := R.arm / 3) hchanges'
      rcases hrelation with heq | hflip
      · exact Or.inl (by simpa using heq)
      · have hcoreStart : arrive R.returnState R.arm =
            (R.mouth, R.returnState) :=
          passagesGrooved_singleton.mp (pathGrooves_pair.mp hB).2
        have hcoreFinal : arrive finalState R.arm =
            (R.mouth, finalState) :=
          passagesGrooved_singleton.mp (pathGrooves_pair.mp hBfinal).2
        have hkeyAgree :
            R.returnState (R.arm / 3) = finalState (R.arm / 3) :=
          grooved_states_agree_on_passage hcoreStart hcoreFinal
        have hk := congrFun hflip (R.arm / 3)
        rw [hkeyAgree] at hk
        cases hval : finalState (R.arm / 3) <;>
          simp [flipAt, hval] at hk
  | flip R =>
      have hchanges' : ∀ j, finalState j ≠ R.afterReturn j →
          j = R.actionSwitch := by
        intro j hj
        have h := hchanges j (by simpa using hj)
        change j = R.secondArm / 3 at h
        exact h.trans R.secondArm_switch
      have hrelation :
          R.afterReturn = finalState ∨
            R.afterReturn = flipAt finalState R.actionSwitch :=
        tongues_eq_or_eq_flipAt_of_changes_only
          (u := R.afterReturn) (v := finalState)
          (k := R.actionSwitch) hchanges'
      rcases hrelation with heq | hflip
      · exact Or.inl (by simpa using heq)
      · exact Or.inr (by
          simpa [ManufacturedReflector.toSupported,
            ManufacturedFlipReflector.toSupported,
            LocalAction.apply] using hflip)

/-- **Complete protected repair count:** at most four distinct restricted
tongue vectors. -/
theorem ManufacturedReflector.completed_protected_route_with_pair_distinct_le_four
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 4 := by
  obtain ⟨reference, _hreferencePaths, hrouteEq, hfinishEq,
      hreferenceGrooved, _hguard⟩ :=
    A.current_route_reference B.baseState B.activatedState hA
  have hfinalGrooved :
      PassagesGrooved finalState (A.orientedRoute B.activatedState) :=
    hrepair.grooved_of_switchSimple
      (A.orientedRoute_simple B.activatedState)
  have hfinalReferenceGrooved :
      PassagesGrooved finalState (A.orientedRoute reference) := by
    rw [hrouteEq]
    exact hfinalGrooved
  have hreferenceGrooved' :
      PassagesGrooved reference (A.orientedRoute reference) := by
    rw [hrouteEq]
    exact hreferenceGrooved
  have horiented := A.oriented_data_eq_of_route_grooved
    reference finalState hreferenceGrooved' hfinalReferenceGrooved
  have hrouteFinal := A.orientedRoute_trace finalState hAfinal
  have hrouteFinal' : PhysicalTrace w (g, finalState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState) := by
    rw [horiented.1, horiented.2, hrouteEq, hfinishEq] at hrouteFinal
    exact hrouteFinal
  let L := (A.orientedRoute B.activatedState).length
  let endpoint : Nat × Tongues :=
    (A.orientedFinish B.activatedState, finalState)
  have hrepairReach : stepN w L (g, B.activatedState) =
      some endpoint := by
    simpa [L, endpoint] using hrepair.sound
  have hpairReach : stepN w L (g, finalState) = some endpoint := by
    simpa [L, endpoint] using hrouteFinal'.sound
  have hprefixPhase := A.repair_prefix_two_phase B hA hB
    hrepair (A.orientedRoute_simple B.activatedState)
    (by intro passage hp; exact hp) hBfinal
  have hrelation := A.completed_repair_initial_action_relation
    B hA hB hrepair hBfinal
  let corners := manufacturedPairActionCorners A B finalState
  have hfinalMem : finalState ∈ corners := by
    simp [corners, manufacturedPairActionCorners]
  have hinitialMem : B.activatedState ∈ corners := by
    rcases hrelation with heq | haction
    · simpa [heq] using hfinalMem
    · dsimp [corners]
      simp [manufacturedPairActionCorners, haction]
  have hcover : NoveltyCoverOn w N
      (g, B.activatedState) times [] 4 := by
    refine ⟨corners.map (VectorCount.restrict N), ?_, ?_⟩
    · simp [corners, manufacturedPairActionCorners]
    · intro k hk
      simp only [List.nil_append]
      by_cases hkpre : k ≤ L
      · obtain ⟨port, phase, hrun, hphase⟩ :=
          hprefixPhase k hkpre
        have hvec : restrictedTonguesAt w N
            (g, B.activatedState) k =
              VectorCount.restrict N phase := by
          simp [restrictedTonguesAt, tonguesAt, hrun]
        rw [hvec]
        apply List.mem_map.mpr
        rcases hphase with h | h
        · exact ⟨phase, by simpa [h] using hinitialMem, rfl⟩
        · exact ⟨phase, by simpa [h] using hfinalMem, rfl⟩
      · let d := k - L
        have hkEq : k = L + d := by
          dsimp [d]
          omega
        have hkLive := hlive k hk
        have htailLive : ∃ finish, stepN w d endpoint = some finish := by
          rw [hkEq, stepN_add, hrepairReach] at hkLive
          cases htail : stepN w d endpoint with
          | none =>
              rw [htail] at hkLive
              simp at hkLive
          | some finish => exact ⟨finish, htail⟩
        have hmem := manufactured_pair_reached_action_corners_tongues
          A B finalState hAfinal hBfinal hpairReach htailLive
        have hshift := tonguesAt_add_of_reaches hrepairReach htailLive
        apply List.mem_map.mpr
        refine ⟨tonguesAt w endpoint d, ?_, ?_⟩
        · simpa [corners] using hmem
        · unfold restrictedTonguesAt
          rw [hkEq]
          exact congrArg (VectorCount.restrict N) hshift
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

end GeneralN
