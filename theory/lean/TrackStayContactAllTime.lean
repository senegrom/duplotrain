import TrackThetaPointwiseCore

/-!
# Absolute phase law for a flip reflector meeting a stay reflector

The intersecting stay/flip cases were the last reflector-pair geometries still
charged by physical travel.  They actually have only two tongue phases.  The
flip traversal creates one alternate vector; the disturbed stay traversal
either captures that flip or repairs it at the unique contacted passage, and
all remaining motion is grooved in the original vector.
-/

namespace GeneralN

theorem stay_twoPhase_concat
    {w : Wiring} {start middle : Nat × Tongues}
    {left right : Nat} {u v : Tongues}
    (hleft : stepN w left start = some middle)
    (hleftPhase : ∀ d, d ≤ left → ∃ port phase,
      stepN w d start = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (hrightPhase : ∀ d, d ≤ right → ∃ port phase,
      stepN w d middle = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (d : Nat) (hd : d ≤ left + right) :
    ∃ port phase, stepN w d start = some (port, phase) ∧
      (phase = u ∨ phase = v) :=
  stepN_cover_append hleft hleftPhase hrightPhase d hd

/-- A complete manufactured stay-reflector traversal carries its incoming
vector at every intermediate time. -/
theorem ManufacturedStayReflector.travel_state_stepN
    {w : Wiring} {g e : Nat}
    (B : ManufacturedStayReflector w g e)
    (state : Tongues)
    (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
    {d : Nat} (hd : d ≤ 2 * B.runway.length + 2) :
    ∃ port, stepN w d (g, state) = some (port, state) := by
  have hpaths : PathGrooves
      (ManufacturedReflector.stay B).toSupported.paths state := hB
  have hrun :=
    ((ManufacturedReflector.stay B).toSupported.run state hpaths).1
  have hd' : d ≤ (ManufacturedReflector.stay B).toSupported.travel := hd
  obtain ⟨middle, hmiddle⟩ := stepN_prefix_some hd' hrun
  rcases middle with ⟨port, phase⟩
  have hphase :=
    (ManufacturedReflector.stay B).travel_two_phase_tongues
      state hpaths hd'
  have hseen : tonguesAt w (g, state) d = phase := by
    simp [tonguesAt, hmiddle]
  have hphaseState : phase = state := by
    rcases hphase with h | h
    · exact hseen.symm.trans h
    · have h' : tonguesAt w (g, state) d = state := by
        simpa [ManufacturedReflector.toSupported,
          ManufacturedStayReflector.toSupported, LocalAction.apply] using h
      exact hseen.symm.trans h'
  exact ⟨port, by simpa [hphaseState] using hmiddle⟩


section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedFlipReflector w g e)
  (B : ManufacturedStayReflector w e g)
  (state : Tongues)
  (hA : PathGrooves [A.runway, A.candy] state)
  (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
  (hcontact : ∃ path ∈ [B.runway, [(B.mouth, B.arm)]],
    ∃ passage ∈ path,
      passageSwitch passage = A.actionSwitch)
include w g e A B state hA hB hcontact

/-- Pointwise disturbed-support dichotomy for a stay reflector. -/
theorem manufactured_stay_support_fault_dichotomy_pointwise :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) ∨
    (stepN w (2 * B.runway.length + 2)
        (e, flipAt state A.actionSwitch) = some (g, state) ∧
      ∀ d, d ≤ 2 * B.runway.length + 2 → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) := by
  simpa only [ManufacturedReflector.toSupported, ManufacturedStayReflector.toSupported,
    LocalAction.apply, or_self] using
    ManufacturedReflector.support_fault_dichotomy_pointwise A (.stay B) state hA hB hcontact

/-- A flip reflector followed by an intersecting stay reflector has exactly
its original and action-flipped tongue phases for all time. -/
theorem manufactured_flip_then_stay_all_time_two_phase :
    ∀ d, ∃ port phase,
      stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = flipAt state A.actionSwitch) := by
  let safe := fun phase => phase = state ∨ phase = flipAt state A.actionSwitch
  let boundary := fun c => c = (g, state) ∨ c = (e, flipAt state A.actionSwitch) ∨
    c = (e, state)
  have hprogress : ∀ start, boundary start → ∃ travel finish,
      0 < travel ∧ stepN w travel start = some finish ∧ boundary finish ∧
      ∀ t, t ≤ travel → ∃ port phase,
        stepN w t start = some (port, phase) ∧ safe phase := by
    intro start hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨A.toSupported.travel, (e, flipAt state A.actionSwitch),
        (ManufacturedReflector.flip A).travel_pos, (A.toSupported.run state hA).1,
        Or.inr (Or.inl rfl), fun _ ht => A.travel_two_phase_stepN state hA ht⟩
    · rcases manufactured_stay_support_fault_dichotomy_pointwise A B state hA hB hcontact with
        ⟨travel, hr, hp⟩ | ⟨hr, hp⟩
      · refine ⟨travel, (e, state), stepN_flip_restore_pos hr, hr, Or.inr (Or.inr rfl), ?_⟩
        intro t ht
        obtain ⟨port, phase, hr, hv⟩ := hp t ht
        exact ⟨port, phase, hr, hv.symm⟩
      · refine ⟨B.toSupported.travel, (g, state), (ManufacturedReflector.stay B).travel_pos,
          hr, Or.inl rfl, ?_⟩
        intro t ht
        obtain ⟨port, phase, hr, hv⟩ := hp t ht
        exact ⟨port, phase, hr, hv.symm⟩
    · refine ⟨B.toSupported.travel, (g, state), (ManufacturedReflector.stay B).travel_pos,
        (B.toSupported.run state hB).1, Or.inl rfl, ?_⟩
      intro t ht
      obtain ⟨port, hr⟩ := B.travel_state_stepN state hB ht
      exact ⟨port, state, hr, Or.inl rfl⟩
  exact fun d => stepN_covered_of_progress boundary safe hprogress (Or.inl rfl) d

end

/-- The opposite orientation, with the stay traversal first, has the same two
absolute phases. -/
theorem manufactured_stay_then_flip_contact_all_time_two_phase
    {w : Wiring} {g e : Nat}
    (A : ManufacturedStayReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, [(A.mouth, A.arm)]] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [A.runway, [(A.mouth, A.arm)]],
      ∃ passage ∈ path,
        passageSwitch passage = B.actionSwitch) :
    ∀ d, ∃ port phase,
      stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = flipAt state B.actionSwitch) := by
  have hArun := (A.toSupported.run state hA).1
  change stepN w (2 * A.runway.length + 2) (g, state) =
      some (e, state) at hArun
  have hAphase : ∀ d, d ≤ 2 * A.runway.length + 2 →
      ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = flipAt state B.actionSwitch) := by
    intro d hd
    obtain ⟨port, hrun⟩ := A.travel_state_stepN state hA hd
    exact ⟨port, state, hrun, Or.inl rfl⟩
  have htail := manufactured_flip_then_stay_all_time_two_phase
    B A state hB hA hcontact
  intro d
  by_cases hpre : d ≤ 2 * A.runway.length + 2
  · exact hAphase d hpre
  · let r := d - (2 * A.runway.length + 2)
    have hdecomp : d = (2 * A.runway.length + 2) + r := by
      dsimp [r]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := htail r
    refine ⟨port, phase, ?_, hphase⟩
    rw [hdecomp, stepN_add, hArun]
    exact hrun

end GeneralN
