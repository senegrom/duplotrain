import BoundaryOverlapTailCount
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

/-! ## Two-phase prefix followed by a directly counted tail
The endpoint phase is shared by the prefix and suffix.  Therefore a two-phase
prefix adds at most one vector beyond the suffix's own direct count.
-/

/-- A prefix whose complete tongue vector is always its initial or endpoint
state, followed by a suffix with direct cap `cap`, has at most `cap+1`
distinct restricted vectors. -/
theorem two_phase_prefix_then_direct_tail_distinct_le_succ
    {w : Wiring} {N lead cap : Nat}
    {start endpoint : Nat × Tongues}
    (hreach : stepN w lead start = some endpoint)
    (hphase : ∀ d, d ≤ lead →
      ∃ port phase,
        stepN w d start = some (port, phase) ∧
        (phase = start.2 ∨ phase = endpoint.2))
    (htail : ∀ (tailTimes : List Nat),
      (∀ k ∈ tailTimes, (stepN w k endpoint).isSome) →
      (tailTimes.map (restrictedTonguesAt w N endpoint)).Nodup →
      tailTimes.length ≤ cap)
    (hcapPos : 0 < cap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ cap + 1 := by
  let initialVector := VectorCount.restrict N start.2
  let endpointVector := VectorCount.restrict N endpoint.2
  let history := [initialVector, endpointVector]
  have hprefixCover : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ history := by
    intro d hd
    obtain ⟨port, phase, hrun, hphaseEq⟩ := hphase d hd
    have hvector : restrictedTonguesAt w N start d =
        VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hrun]
    rw [hvector]
    rcases hphaseEq with rfl | rfl
    · simp [history, initialVector]
    · simp [history, endpointVector]
  have hboundary : VectorCount.restrict N endpoint.2 ∈ history := by
    simp [history, endpointVector]
  have hcount := noveltyCoverOn_distinct_count
    (boundary_history_then_direct_tail_cover hreach history hprefixCover hboundary
      htail hcapPos times hlive hnd) hnd
  have hhistory : history.length = 2 := by simp [history]
  rw [hhistory] at hcount
  omega

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
