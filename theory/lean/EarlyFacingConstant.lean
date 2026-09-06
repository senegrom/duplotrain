import RepairLeadTwoPhase
import TwoPhasePrefixTailCount
import TrackStayContactAllTime

/-!
# Constant count for the protected final-mouth facing exit

At the final mouth of a flip reflector, capture and replay alternate between
exactly two tongue phases.  Starting the tail at the mouth/contact endpoint
makes this a direct two-vector tail.  The protected repair approach ending at
that endpoint is itself two-phase, so boundary overlap gives three vectors in
total.
-/

namespace GeneralN

/-- From a flip reflector's final mouth/contact state, every future tongue
vector is either the contact phase or its action-switch flip. -/
theorem ManufacturedFlipReflector.facing_mouth_tail_two_phase
    {w : Wiring} {g e : Nat}
    (B : ManufacturedFlipReflector w e g)
    {contact : Tongues} {approach : List Passage}
    (happroachContact : PhysicalTrace w
      (g, contact) approach (B.mouth, contact))
    (hgrooved : PassagesGrooved contact approach)
    (hpaths : PathGrooves [B.runway, B.candy] contact) :
    ∀ d, ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
      (phase = flipAt contact B.actionSwitch ∨ phase = contact) := by
  have hreturn : ∀ current, (current = contact ∨ current = flipAt contact B.actionSwitch) →
      ∃ travel final, 0 < travel ∧
        stepN w travel (B.mouth, current) = some (g, final) ∧
        (final = contact ∨ final = flipAt contact B.actionSwitch) ∧
        ∀ d, d ≤ travel → ∃ port phase,
          stepN w d (B.mouth, current) = some (port, phase) ∧
          (phase = contact ∨ phase = flipAt contact B.actionSwitch) := by
    intro current hs
    have hc : PathGrooves [B.runway, B.candy] current := by
      rcases hs with rfl | rfl
      · exact hpaths
      · exact hpaths.after_avoiding_action (action := LocalAction.flip B.actionSwitch) B.support_foreign
    have hf := hc.after_avoiding_action (action := LocalAction.flip B.actionSwitch) B.support_foreign
    refine ⟨B.candy.length + 2 + B.runway.length, flipAt current B.actionSwitch,
      by omega, ?_, ?_, ?_⟩
    · simpa only [flipAt_flipAt] using B.capture_from_mouth
        (flipAt current B.actionSwitch) (pathGrooves_pair.mp hf).1 (pathGrooves_pair.mp hf).2
    · rcases hs with rfl | rfl <;> simp [flipAt_flipAt]
    · intro d hd
      obtain ⟨port, phase, hr, hp⟩ := B.capture_from_mouth_two_phase
        (flipAt current B.actionSwitch) (pathGrooves_pair.mp hf).1 (pathGrooves_pair.mp hf).2 hd
      simp only [flipAt_flipAt] at hr hp
      refine ⟨port, phase, hr, ?_⟩
      rcases hs with rfl | rfl
      · exact hp
      · simpa only [flipAt_flipAt, or_comm] using hp
  intro d
  obtain ⟨port, phase, hr, hp⟩ := B.grooved_return_two_phase contact hpaths
    happroachContact hgrooved hreturn (Or.inr rfl) (Or.inl rfl) d
  exact ⟨port, phase, hr, hp.symm⟩

end GeneralN
