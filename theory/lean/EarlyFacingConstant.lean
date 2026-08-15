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
    (happroachSimple : SwitchSimple approach)
    (hforeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ B.actionSwitch)
    (hpaths : PathGrooves [B.runway, B.candy] contact) :
    ∀ d, ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
      (phase = flipAt contact B.actionSwitch ∨ phase = contact) := by
  let alternate := flipAt contact B.actionSwitch
  have happroachGrooved : PassagesGrooved contact approach :=
    happroachContact.grooved_of_switchSimple happroachSimple
  have happroachAlternate : PhysicalTrace w
      (g, alternate) approach (B.mouth, alternate) := by
    dsimp [alternate]
    exact happroachContact.flip_unvisited hforeign
  have happroachAlternateGrooved : PassagesGrooved alternate approach := by
    dsimp [alternate]
    exact grooved_after_flip_other happroachGrooved hforeign
  have hpathsAlternate : PathGrooves [B.runway, B.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [B.runway, B.candy]
      ((LocalAction.flip B.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action B.support_foreign
  let cap := B.candy.length + 2 + B.runway.length
  have hcapContact : stepN w cap (B.mouth, contact) =
      some (g, alternate) := by
    have hcapture := B.capture_from_mouth alternate
      (pathGrooves_pair.mp hpathsAlternate).1
      (pathGrooves_pair.mp hpathsAlternate).2
    simpa [cap, alternate, flipAt_flipAt] using hcapture
  have hcapAlternate : stepN w cap (B.mouth, alternate) =
      some (g, contact) := by
    dsimp [cap, alternate]
    exact B.capture_from_mouth contact
      (pathGrooves_pair.mp hpaths).1
      (pathGrooves_pair.mp hpaths).2
  have hcapContactPhase : ∀ d, d ≤ cap → ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      B.capture_from_mouth_two_phase alternate
        (pathGrooves_pair.mp hpathsAlternate).1
        (pathGrooves_pair.mp hpathsAlternate).2 (d := d) (by
          dsimp [cap] at hd
          omega)
    have hstart : flipAt alternate B.actionSwitch = contact := by
      dsimp [alternate]
      exact flipAt_flipAt contact B.actionSwitch
    rw [hstart] at hrun hphase
    refine ⟨port, phase, hrun, ?_⟩
    rcases hphase with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hcapAlternatePhase : ∀ d, d ≤ cap → ∃ port phase,
      stepN w d (B.mouth, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      B.capture_from_mouth_two_phase contact
        (pathGrooves_pair.mp hpaths).1
        (pathGrooves_pair.mp hpaths).2 (d := d) (by
          dsimp [cap] at hd
          omega)
    refine ⟨port, phase, hrun, ?_⟩
    rcases hphase with h | h
    · exact Or.inl h
    · exact Or.inr h
  have happroachContactPhase : ∀ d, d ≤ approach.length →
      ∃ port phase, stepN w d (g, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, hrun⟩ :=
      happroachContact.grooved_prefix_tongues contact
        happroachGrooved hd
    exact ⟨port, contact, hrun, Or.inr rfl⟩
  have happroachAlternatePhase : ∀ d, d ≤ approach.length →
      ∃ port phase, stepN w d (g, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    obtain ⟨port, hrun⟩ :=
      happroachAlternate.grooved_prefix_tongues alternate
        happroachAlternateGrooved hd
    exact ⟨port, alternate, hrun, Or.inl rfl⟩
  let half := cap + approach.length
  have hhalfContact : stepN w half (B.mouth, contact) =
      some (B.mouth, alternate) := by
    dsimp [half]
    rw [stepN_add, hcapContact]
    exact happroachAlternate.sound
  have hhalfAlternate : stepN w half (B.mouth, alternate) =
      some (B.mouth, contact) := by
    dsimp [half]
    rw [stepN_add, hcapAlternate]
    exact happroachContact.sound
  have hhalfContactPhase : ∀ d, d ≤ half → ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    exact stay_twoPhase_concat hcapContact hcapContactPhase
      happroachAlternatePhase d (by simpa [half] using hd)
  have hhalfAlternatePhase : ∀ d, d ≤ half → ∃ port phase,
      stepN w d (B.mouth, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = contact) := by
    intro d hd
    exact stay_twoPhase_concat hcapAlternate hcapAlternatePhase
      happroachContactPhase d (by simpa [half] using hd)
  let period := half + half
  have hperiod : stepN w period (B.mouth, contact) =
      some (B.mouth, contact) := by
    dsimp [period]
    rw [stepN_add, hhalfContact]
    exact hhalfAlternate
  have hwindow : ∀ d, d ≤ period → ∃ port phase,
      stepN w d (B.mouth, contact) = some (port, phase) ∧
        (phase = contact ∨ phase = alternate) := by
    intro d hd
    obtain ⟨port, phase, hrun, hphase⟩ :=
      stay_twoPhase_concat hhalfContact hhalfContactPhase
        hhalfAlternatePhase d (by simpa [period] using hd)
    exact ⟨port, phase, hrun, hphase.symm⟩
  have hpositive : 0 < period := by
    dsimp [period, half, cap]
    omega
  intro d
  obtain ⟨port, phase, hrun, hphase⟩ :=
    periodic_two_phase_prefix_tongues hpositive hperiod hwindow d
  refine ⟨port, phase, hrun, ?_⟩
  have hphase' := hphase.symm
  simpa [alternate] using hphase'

