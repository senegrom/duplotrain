import BoundaryDoubleDuplicate
import ProtectedPairNAddFour
import BoundaryNAddFourSaturation

/-!
# The canonical productive-boundary overlap

At the canonical unchanged occurrence the initially written switch is the
flip reflector's action switch.  The arbitrary-start vector is therefore
the action mate of the reflector's *base* vector.  This file records that
exact overlap and audits the tempting stronger claim that it is also the
reflector's activated vector.

The stronger claim is not a bare manufactured-reflector law.  The advertised
local action describes a re-run after the support has been grooved; the first
construction may additionally write switches on that support.  In fact a
saturated boundary residual forces at least one such foreign coordinate to
differ.  The final theorem below still extracts the useful exact consequence:
if a protected repair's second pre-return vector has returned to the first
base vector (on the counted coordinates), then the arbitrary-start vector is
one of the nominal repair corners and the completed repair costs only one
fresh vector.
-/

namespace GeneralN

/-- At the canonical occurrence, applying the old reflector action to the
arbitrary-start vector gives exactly the first reflector's base state. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_original_action_mate_eq_base
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    flipAt S.source.original R.actionSwitch =
      (ManufacturedReflector.flip R).baseState := by
  have hk0 : S.source.k0 = R.actionSwitch :=
    O.switch_eq_action_of_before_length_eq_runway hcanonical
  calc
    flipAt S.source.original R.actionSwitch =
        flipAt S.source.original S.source.k0 := by rw [hk0]
    _ = S.source.base := S.source.base_flip.symm
    _ = S.A.baseState := S.reflector_base.symm
    _ = (ManufacturedReflector.flip R).baseState := by rw [hAeq]

/-- Equivalently, the arbitrary-start vector is the action mate of the
historical base vector. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_original_eq_action_base
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    S.source.original =
      flipAt (ManufacturedReflector.flip R).baseState R.actionSwitch := by
  have hmate := S.canonical_original_action_mate_eq_base
    R hAeq O hcanonical
  calc
    S.source.original =
        flipAt (flipAt S.source.original R.actionSwitch)
          R.actionSwitch := (flipAt_flipAt _ _).symm
    _ = flipAt (ManufacturedReflector.flip R).baseState
          R.actionSwitch := by rw [hmate]

/-- The action mate of `original`, rather than `original` itself, is already
in the compressed first construction history. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_original_action_mate_mem_first_core
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    VectorCount.restrict N
        (flipAt S.source.original R.actionSwitch) ∈
      (ManufacturedReflector.flip R).sharpHistoryCore N := by
  rw [S.canonical_original_action_mate_eq_base R hAeq O hcanonical]
  exact (ManufacturedReflector.flip R).base_mem_sharpHistoryCore

/-- A manufactured flip restores the opposite branch at its action switch.
This is only a coordinate statement: support switches may also have changed
during the first construction. -/
theorem ManufacturedFlipReflector.activated_action_eq_not_base
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e) :
    (ManufacturedReflector.flip R).activatedState R.actionSwitch =
      !((ManufacturedReflector.flip R).baseState R.actionSwitch) := by
  have hmouthSelected :
      R.mouthState R.actionSwitch = bval R.firstArm := by
    obtain ⟨after, hhead⟩ := R.candyTrace.head_arrive.2
    have hm : R.mouth % 3 = 0 := R.mouth_is_stem
    unfold arrive at hhead
    rw [if_pos hm] at hhead
    have hbranch :
        branchPort R.actionSwitch (R.mouthState R.actionSwitch) =
          R.firstArm := by
      simpa [ManufacturedFlipReflector.actionSwitch] using
        congrArg Prod.fst hhead
    have hrecovered :
        branchPort R.actionSwitch (bval R.firstArm) = R.firstArm := by
      simpa [R.firstArm_switch] using
        (branchPort_bval R.firstArm_branch)
    have hsame :
        branchPort R.actionSwitch (R.mouthState R.actionSwitch) =
          branchPort R.actionSwitch (bval R.firstArm) :=
      hbranch.trans hrecovered.symm
    cases hs : R.mouthState R.actionSwitch <;>
      cases hf : bval R.firstArm <;>
      simp [branchPort, hs, hf] at hsame ⊢ <;> omega
  have hrunwayForeign : forall passage, passage ∈ R.runway ->
      passageSwitch passage ≠ R.actionSwitch := by
    exact R.support_foreign R.runway (by simp)
  have hbaseSelected :
      R.base R.actionSwitch = bval R.firstArm := by
    calc
      R.base R.actionSwitch = R.mouthState R.actionSwitch :=
        (R.runwayTrace.preserves R.actionSwitch hrunwayForeign).symm
      _ = bval R.firstArm := hmouthSelected
  have hpinAfter : pin R.returnState R.secondArm = R.afterReturn := by
    have hsnd := congrArg Prod.snd R.crossed
    simpa [arrive, R.secondArm_branch] using hsnd
  have hafterSelected :
      R.afterReturn R.actionSwitch = bval R.secondArm := by
    rw [← hpinAfter]
    simp [pin, R.secondArm_switch]
  have hopposite : bval R.secondArm = !(bval R.firstArm) :=
    branch_values_opposite R.firstArm_branch R.secondArm_branch
      (R.firstArm_switch.trans R.secondArm_switch.symm) R.arms_ne
  change R.afterReturn R.actionSwitch = !(R.base R.actionSwitch)
  calc
    R.afterReturn R.actionSwitch = bval R.secondArm := hafterSelected
    _ = !(bval R.firstArm) := hopposite
    _ = !(R.base R.actionSwitch) := by rw [hbaseSelected]

/-- In the canonical boundary case the old action coordinate really is
restored to its arbitrary-start value.  This is the valid coordinate-level
part of the suspected full-vector identity. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_action_restored
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    (ManufacturedReflector.flip R).activatedState R.actionSwitch =
      S.source.original R.actionSwitch := by
  have hmate := S.canonical_original_action_mate_eq_base
    R hAeq O hcanonical
  have hbit := R.activated_action_eq_not_base
  change R.afterReturn R.actionSwitch = !(R.base R.actionSwitch) at hbit
  change flipAt S.source.original R.actionSwitch = R.base at hmate
  change R.afterReturn R.actionSwitch = S.source.original R.actionSwitch
  rw [hbit]
  have hmateBit := congrFun hmate R.actionSwitch
  simp [flipAt] at hmateBit
  cases ho : S.source.original R.actionSwitch <;>
    cases hb : R.base R.actionSwitch <;> simp_all

/-- Saturation forces a foreign changed coordinate at the canonical
activated endpoint.  Thus restoring the action bit does *not* restore the
whole arbitrary-start vector. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_foreign_change
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    Exists fun C : Nat =>
      C < N /\ C ≠ R.actionSwitch /\
        (ManufacturedReflector.flip R).activatedState C ≠
          S.source.original C := by
  let d := S.A.exploration.length + S.A.runway.length + 1
  have hlive : (stepN w d (S.source.g, S.source.base)).isSome := by
    dsimp [d]
    rw [S.reached]
    simp
  have hend :
      tonguesAt w (S.source.g, S.source.base) d = S.stateA := by
    simp [tonguesAt, d, S.reached]
  have hk0 : S.source.k0 = R.actionSwitch :=
    O.switch_eq_action_of_before_length_eq_runway hcanonical
  have hrestored :
      tonguesAt w (S.source.g, S.source.base) d S.source.k0 =
        S.source.original S.source.k0 := by
    calc
      tonguesAt w (S.source.g, S.source.base) d S.source.k0 =
          S.stateA S.source.k0 := congrFun hend _
      _ = S.A.activatedState S.source.k0 := by rw [S.activated]
      _ = (ManufacturedReflector.flip R).activatedState
          S.source.k0 := by rw [hAeq]
      _ = (ManufacturedReflector.flip R).activatedState
          R.actionSwitch := by rw [hk0]
      _ = S.source.original R.actionSwitch :=
        S.canonical_action_restored R hAeq O hcanonical
      _ = S.source.original S.source.k0 := by rw [hk0]
  obtain ⟨C, hClt, hCne, hchange⟩ :=
    S.source.restored_has_foreign_difference d hlive hrestored
  refine ⟨C, hClt, ?_, ?_⟩
  · intro hEq
    apply hCne
    rw [hk0, hEq]
  · rw [hend, S.activated, hAeq] at hchange
    exact hchange

/-- Consequently the proposed full identity `original = activatedState` is
false in a saturated canonical residual. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_original_ne_activated
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    S.source.original ≠
      (ManufacturedReflector.flip R).activatedState := by
  obtain ⟨C, _hClt, _hCne, hchange⟩ :=
    S.canonical_foreign_change R hAeq O hcanonical
  intro hEq
  apply hchange
  rw [← hEq]

/-- If the support had already been grooved in the construction base state,
the reflector re-run law would imply the suspected full identity.  This
precisely identifies the missing premise in that argument. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_original_eq_activated_of_base_grooved
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length)
    (hbaseGrooved : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).baseState) :
    S.source.original =
      (ManufacturedReflector.flip R).activatedState := by
  have hnormalRaw :=
    ((ManufacturedReflector.flip R).toSupported.run
      (ManufacturedReflector.flip R).baseState hbaseGrooved).1
  change stepN w (2 * R.runway.length + R.candy.length + 2)
      (S.source.g, R.base) =
        some (S.source.e, flipAt R.base R.actionSwitch) at hnormalRaw
  have htravel :
      2 * R.runway.length + R.candy.length + 2 =
        R.runway.length + (R.candy.length + 1) +
          R.runway.length + 1 := by
    omega
  rw [htravel] at hnormalRaw
  have hnormal :
      stepN w
          ((ManufacturedReflector.flip R).exploration.length +
            (ManufacturedReflector.flip R).runway.length + 1)
          (S.source.g, (ManufacturedReflector.flip R).baseState) =
        some (S.source.e,
          flipAt (ManufacturedReflector.flip R).baseState
            R.actionSwitch) := by
    simpa only [ManufacturedReflector.exploration,
      ManufacturedReflector.runway, ManufacturedReflector.baseState,
      List.length_append, List.length_cons] using hnormalRaw
  have hreached := S.reached
  rw [← S.reflector_base, S.activated, hAeq] at hreached
  have hpairs :
      (S.source.e,
          flipAt (ManufacturedReflector.flip R).baseState
            R.actionSwitch) =
        (S.source.e, (ManufacturedReflector.flip R).activatedState) :=
    Option.some.inj (hnormal.symm.trans hreached)
  have hactivated :
      flipAt (ManufacturedReflector.flip R).baseState R.actionSwitch =
        (ManufacturedReflector.flip R).activatedState :=
    congrArg Prod.snd hpairs
  exact (S.canonical_original_eq_action_base R hAeq O hcanonical).trans
    hactivated

/-- The missing base-groove premise is actually impossible in the saturated
canonical residual. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_base_not_grooved
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length) :
    Not (PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).baseState) := by
  intro hgrooved
  exact S.canonical_original_ne_activated R hAeq O hcanonical
    (S.canonical_original_eq_activated_of_base_grooved
      R hAeq O hcanonical hgrooved)

/-- Exact repair-corner characterization.  At a canonical boundary, the
old action applied to the second pre-return vector equals `original` on the
counted coordinates iff that pre-return vector equals the first base vector
on those coordinates. -/
theorem ProductiveBoundaryNAddFourSavingResidual.canonical_action_preReturn_eq_original_iff
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length)
    (B : ManufacturedReflector w S.source.e S.source.g) :
    VectorCount.restrict N
        ((ManufacturedReflector.flip R).toSupported.action.apply
          B.preReturn.2) =
        VectorCount.restrict N S.source.original <->
      VectorCount.restrict N B.preReturn.2 =
        VectorCount.restrict N
          (ManufacturedReflector.flip R).baseState := by
  have hmate := S.canonical_original_action_mate_eq_base
    R hAeq O hcanonical
  have horiginal := S.canonical_original_eq_action_base
    R hAeq O hcanonical
  constructor
  · intro hcorner
    have hflipped := restrict_flipAt_congr
      (C := R.actionSwitch) hcorner
    simpa [ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported, LocalAction.apply,
      flipAt_flipAt, hmate] using hflipped
  · intro hpre
    have hflipped := restrict_flipAt_congr
      (C := R.actionSwitch) hpre
    simpa [ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported, LocalAction.apply,
      horiginal] using hflipped

/-- Under the exact pre-return/base overlap above, `original` supplies the
historical action-pre-return corner required by the one-novelty protected
repair theorem. -/
theorem ProductiveBoundaryNAddFourSavingResidual.completed_protected_route_one_novelty_of_canonical_overlap
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hcanonical : O.before.length = R.runway.length)
    (B : ManufacturedReflector w S.source.e S.source.g)
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w
      (S.source.g, B.activatedState)
      ((ManufacturedReflector.flip R).orientedRoute B.activatedState)
      ((ManufacturedReflector.flip R).orientedFinish B.activatedState,
        finalState))
    (hAfinal : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    (history : List (List Bool))
    (hinitialHistorical :
      VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical :
      VectorCount.restrict N B.preReturn.2 ∈ history)
    (horiginalHistorical :
      VectorCount.restrict N S.source.original ∈ history)
    (hpreBase :
      VectorCount.restrict N B.preReturn.2 =
        VectorCount.restrict N
          (ManufacturedReflector.flip R).baseState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (S.source.g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (S.source.g, B.activatedState)
      times history 1 := by
  have haPreHistorical :
      VectorCount.restrict N
          ((ManufacturedReflector.flip R).toSupported.action.apply
            B.preReturn.2) ∈ history := by
    rw [(S.canonical_action_preReturn_eq_original_iff
      R hAeq O hcanonical B).2 hpreBase]
    exact horiginalHistorical
  exact
    ManufacturedReflector.completed_protected_route_one_novelty_of_action_preReturn
      (ManufacturedReflector.flip R) B hA hB hrepair hAfinal hBfinal
        history hinitialHistorical hpreHistorical haPreHistorical times hlive

end GeneralN
