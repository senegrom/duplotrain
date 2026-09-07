import PartialSecondRunSharp

/-!
# The protected pre-return facts of a completed opposite pair

The three facts about a completed opposite pair that the sharp
protected-pair closure consumes: the pre-return state equals the
action-applied activated
state, it is already inside the preserved two-history core, and a
completed protected route beyond it costs at most two novelties.
-/

namespace GeneralN

/-- The state immediately before a manufactured reflector's final return is
the reflector action applied to its activated state.  For a stay reflector
this is definitional.  For a flip reflector, the recorded candy traversal
leaves the first arm selected, so entering the opposite second arm performs
exactly the advertised flip. -/
theorem ManufacturedReflector.preReturn_eq_action_activated
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w g e) :
    B.preReturn.2 = B.toSupported.action.apply B.activatedState := by
  cases B with
  | stay R => rfl
  | flip R =>
      change R.returnState = flipAt R.afterReturn R.actionSwitch
      have hsimpleCandy :
          SwitchSimple ((R.mouth, R.firstArm) :: R.candy) := by
        have hs := R.simple
        unfold SwitchSimple at hs ⊢
        simp only [List.map_append] at hs
        exact (List.nodup_append.mp hs).2.1
      have hgrooved := R.candyTrace.grooved_of_switchSimple hsimpleCandy
      have hfirst : arrive R.returnState R.firstArm =
          (R.mouth, R.returnState) :=
        hgrooved (R.mouth, R.firstArm) List.mem_cons_self
      have hpinFirst : pin R.returnState R.firstArm = R.returnState := by
        have hsnd := congrArg Prod.snd hfirst
        simpa [arrive, R.firstArm_branch] using hsnd
      have hselected :
          R.returnState R.actionSwitch = bval R.firstArm := by
        have hbit := congrFun hpinFirst R.actionSwitch
        simpa [pin, R.firstArm_switch] using hbit.symm
      have hopposite :
          bval R.secondArm = !(R.returnState R.actionSwitch) := by
        rw [hselected]
        exact branch_values_opposite R.firstArm_branch
          R.secondArm_branch
          (R.firstArm_switch.trans R.secondArm_switch.symm)
          R.arms_ne
      have hpin : pin R.returnState R.secondArm =
          flipAt R.returnState R.actionSwitch :=
        pin_eq_flipAt R.secondArm_switch hopposite
      have hcross : R.afterReturn =
          flipAt R.returnState R.actionSwitch := by
        have hsnd := congrArg Prod.snd R.crossed
        have hpinAfter : pin R.returnState R.secondArm = R.afterReturn := by
          simpa [arrive, R.secondArm_branch] using hsnd
        exact hpinAfter.symm.trans hpin
      rw [hcross, flipAt_flipAt]


/-- **Shared core of the completed protected repair.**  After the repair the
run stays on the four action corners of the restored pair.  Two corners
(the final vector and its `B`-action) are always historical; whenever the
other two lie in `history ++ fresh`, so does every sampled vector. -/
theorem ManufacturedReflector.completed_protected_route_cover
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
    (history fresh : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (hAcovered : VectorCount.restrict N
      (A.toSupported.action.apply finalState) ∈ history ++ fresh)
    (hBAcovered : VectorCount.restrict N
      (B.toSupported.action.apply
        (A.toSupported.action.apply finalState)) ∈ history ++ fresh)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    ∀ k ∈ times,
      restrictedTonguesAt w N (g, B.activatedState) k ∈ history ++ fresh := by
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
  have hpreAction :
      B.preReturn.2 = B.toSupported.action.apply B.activatedState :=
    B.preReturn_eq_action_activated
  have hfinalHistorical :
      VectorCount.restrict N finalState ∈ history := by
    rcases hrelation with heq | haction
    · simpa [heq] using hinitialHistorical
    · have hpreFinal : B.preReturn.2 = finalState := by
        calc
          B.preReturn.2 =
              B.toSupported.action.apply B.activatedState := hpreAction
          _ = finalState := by
            rw [haction, B.toSupported.action.involutive]
      simpa [hpreFinal] using hpreHistorical
  have hBfinalHistorical : VectorCount.restrict N
      (B.toSupported.action.apply finalState) ∈ history := by
    rcases hrelation with heq | haction
    · have hpreB : B.preReturn.2 =
          B.toSupported.action.apply finalState := by
        rw [hpreAction, heq]
      simpa [hpreB] using hpreHistorical
    · simpa [haction] using hinitialHistorical
  have hcornerCover : ∀ phase ∈ manufacturedPairActionCorners A B finalState,
      VectorCount.restrict N phase ∈ history ++ fresh := by
    intro phase hp
    simp only [manufacturedPairActionCorners, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ hfinalHistorical
    · exact hAcovered
    · exact List.mem_append_left _ hBfinalHistorical
    · exact hBAcovered
  refine cover_of_phase_orbit hrepairReach (fun d hd => by
    rw [← tonguesAt_add_of_reaches hpairReach (Option.isSome_iff_exists.mp hd)]
    exact manufactured_pair_all_time_action_corners_tongues A B finalState hAfinal hBfinal _)
    hcornerCover hlive ?_
  intro k hk hkpre
  obtain ⟨port, phase, hrun, hphase⟩ := hprefixPhase k (Nat.le_of_lt hkpre)
  rw [show restrictedTonguesAt w N (g, B.activatedState) k =
    VectorCount.restrict N phase by simp [restrictedTonguesAt, tonguesAt, hrun]]
  rcases hphase with rfl | rfl
  · exact hinitialHistorical
  · exact hfinalHistorical

end GeneralN
