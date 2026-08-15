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
      change R.returnState = finalState ∨ R.returnState = finalState
      have hchanges' : ∀ j, finalState j ≠ R.returnState j →
          j = R.arm / 3 := by
        intro j hj
        have h := hchanges j (by
          change finalState j ≠ R.returnState j
          exact hj)
        change j = R.arm / 3 at h
        exact h
      have hrelation :
          R.returnState = finalState ∨
            R.returnState = flipAt finalState (R.arm / 3) :=
        tongues_eq_or_eq_flipAt_of_changes_only
          (u := R.returnState) (v := finalState)
          (k := R.arm / 3) hchanges'
      rcases hrelation with heq | hflip
      · exact Or.inl heq
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
      change R.afterReturn = finalState ∨
        R.afterReturn = flipAt finalState R.actionSwitch
      have hchanges' : ∀ j, finalState j ≠ R.afterReturn j →
          j = R.actionSwitch := by
        intro j hj
        have h := hchanges j (by
          change finalState j ≠ R.afterReturn j
          exact hj)
        change j = R.secondArm / 3 at h
        exact h.trans R.secondArm_switch
      exact tongues_eq_or_eq_flipAt_of_changes_only
        (u := R.afterReturn) (v := finalState)
        (k := R.actionSwitch) hchanges'

