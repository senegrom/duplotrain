import RunwaySpliceNovelty

/-!
# A support fault on the selected route

Normalize the reflector's outward route once. Before its unique contact
with the disturbed switch the flipped and undisturbed walks differ only
at that switch. A stem entry invokes the other reflector's capture; a
branch entry repairs the tongue and merges into the undisturbed walk.
The same argument handles runway, forward-candy, and reverse-candy contacts.
-/

namespace GeneralN

/-- Covered positive-length excursions suffice for an all-time cover.
The invariant is required only at excursion boundaries; intermediate states
need satisfy only `allowed`. Neither periodicity nor finite state is needed. -/
theorem stepN_covered_of_progress
    {w : Wiring} (invariant : Nat × Tongues → Prop) (allowed : Tongues → Prop)
    (progress : ∀ start, invariant start → ∃ travel finish,
      0 < travel ∧ stepN w travel start = some finish ∧ invariant finish ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d start = some (port, phase) ∧ allowed phase)
    {start : Nat × Tongues} (hstart : invariant start) (d : Nat) :
    ∃ port phase, stepN w d start = some (port, phase) ∧ allowed phase := by
  induction d using Nat.strongRecOn generalizing start with
  | ind d ih =>
      obtain ⟨travel, finish, hpos, hreach, hfinish, hcover⟩ := progress start hstart
      by_cases hpre : d ≤ travel
      · exact hcover d hpre
      · obtain ⟨port, phase, hr, hp⟩ := ih (d - travel) (by omega) hfinish
        refine ⟨port, phase, ?_, hp⟩
        have heq : d = travel + (d - travel) := by omega
        rw [heq, stepN_add, hreach]
        exact hr

/-- Restoring a genuinely flipped tongue cannot take zero steps. -/
theorem stepN_flip_restore_pos
    {w : Wiring} {p q j travel : Nat} {state : Tongues}
    (hr : stepN w travel (p, flipAt state j) = some (q, state)) :
    0 < travel := by
  cases travel with
  | zero =>
      have hv : flipAt state j = state := (Prod.mk.inj (Option.some.inj hr)).2
      have hbit := congrFun hv j
      simp [flipAt] at hbit
  | succ n => omega

/-- A manufactured traversal has only its incoming and outgoing vectors. -/
theorem ManufacturedReflector.travel_two_phase_stepN
    {w : Wiring} {g e : Nat} (B : ManufacturedReflector w g e)
    (state : Tongues) (hB : PathGrooves B.toSupported.paths state)
    {d : Nat} (hd : d ≤ B.toSupported.travel) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      (phase = state ∨ phase = B.toSupported.action.apply state) := by
  obtain ⟨⟨port, phase⟩, hrun⟩ := stepN_prefix_some hd (B.toSupported.run state hB).1
  have hphase := B.travel_two_phase_tongues state hB hd
  exact ⟨port, phase, hrun, by simpa [tonguesAt, hrun] using hphase⟩

/-- Compatibility interface for flip traversals. -/
theorem ManufacturedFlipReflector.travel_two_phase_stepN
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    {d : Nat} (hd : d ≤ 2 * A.runway.length + A.candy.length + 2) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      (phase = state ∨ phase = flipAt state A.actionSwitch) :=
  (ManufacturedReflector.flip A).travel_two_phase_stepN state hA hd

/-- The selected outward route is a prefix of a complete traversal. -/
theorem ManufacturedReflector.orientedRoute_length_le_travel
    {w : Wiring} {g e : Nat} (B : ManufacturedReflector w g e)
    (state : Tongues) : (B.orientedRoute state).length ≤ B.toSupported.travel := by
  rw [B.travel_eq_oriented_add state]
  omega

/-- Prepending a constant-tongue trace preserves a two-phase cover. -/
theorem PhysicalTrace.prepend_two_phase
    {w : Wiring} {s p q L : Nat} {u v : Tongues} {lead : List Passage}
    (hprefix : PhysicalTrace w (s, u) lead (p, u))
    (hgrooved : PassagesGrooved u lead)
    (hend : stepN w L (p, u) = some (q, v))
    (hphases : ∀ d, d ≤ L → ∃ port phase,
      stepN w d (p, u) = some (port, phase) ∧
        (phase = u ∨ phase = v)) :
    stepN w (lead.length + L) (s, u) = some (q, v) ∧
      ∀ d, d ≤ lead.length + L → ∃ port phase,
        stepN w d (s, u) = some (port, phase) ∧
          (phase = u ∨ phase = v) := by
  constructor
  · rw [stepN_add, hprefix.sound]
    exact hend
  · intro d hd
    by_cases hpre : d ≤ lead.length
    · obtain ⟨port, hp⟩ := hprefix.grooved_prefix_tongues u hgrooved hpre
      exact ⟨port, u, hp, Or.inl rfl⟩
    · have hle : d - lead.length ≤ L := by omega
      obtain ⟨port, phase, hr, hv⟩ := hphases _ hle
      refine ⟨port, phase, ?_, hv⟩
      have heq : d = lead.length + (d - lead.length) := by omega
      rw [heq, stepN_add, hprefix.sound]
      exact hr

/-- A trailing contact repairs a single fault and synchronizes the walks.
Before the repair only the disturbed state is seen; after it the two
configurations agree at every time, even beyond the reference trace. -/
theorem PhysicalTrace.trailing_fault_merges
    {w : Wiring} {s p x : Nat} {u : Tongues} {finish : Nat × Tongues}
    {route before after : List Passage}
    (htrace : PhysicalTrace w (s, u) route finish)
    (hgrooved : PassagesGrooved u route)
    (hsimple : SwitchSimple route)
    (hoccurs : route = before ++ (p, x) :: after)
    (hbranch : p % 3 ≠ 0) :
    (∀ d, d ≤ before.length → ∃ port,
      stepN w d (s, flipAt u (p / 3)) = some (port, flipAt u (p / 3))) ∧
    (∀ d, before.length + 1 ≤ d →
      stepN w d (s, flipAt u (p / 3)) = stepN w d (s, u)) := by
  obtain ⟨hprefix, hforeign⟩ := simple_grooved_trace_prefix_to_occurrence
    htrace hoccurs hgrooved hsimple
  have hpreGrooved : PassagesGrooved u before := by
    intro passage hp
    apply hgrooved passage
    rw [hoccurs]
    exact List.mem_append_left _ hp
  have hflip : PhysicalTrace w (s, flipAt u (p / 3)) before
      (p, flipAt u (p / 3)) := hprefix.flip_unvisited hforeign
  have hpreFlip := grooved_after_flip_other hpreGrooved hforeign
  have hgroove : arrive u x = (p, u) := by
    apply hgrooved (p, x)
    rw [hoccurs]
    exact List.mem_append_right _ List.mem_cons_self
  have hforward := groove_forward hgroove
  have hlocal := flipped_passage_forward_trailing hforward hbranch
  have hmerged : stepN w (before.length + 1) (s, flipAt u (p / 3)) =
      stepN w (before.length + 1) (s, u) := by
    rw [stepN_add w before.length 1, stepN_add w before.length 1,
      hprefix.sound, hflip.sound]
    simp [stepN, step, hlocal, hforward]
  constructor
  · intro d hd
    exact hflip.grooved_prefix_tongues _ hpreFlip hd
  · intro d hd
    have heq : d = (before.length + 1) + (d - (before.length + 1)) := by omega
    rw [heq, stepN_add w (before.length + 1),
      stepN_add w (before.length + 1), hmerged]

/-- The pointwise support-fault dichotomy is a stem/branch split on the
actual selected route, not a case split on where that route was stored. -/
theorem ManufacturedReflector.support_fault_dichotomy_pointwise
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g) (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves B.toSupported.paths state)
    (hcontact : ∃ path ∈ B.toSupported.paths,
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) ∨
    (stepN w B.toSupported.travel
        (e, flipAt state A.actionSwitch) =
          some (g, B.toSupported.action.apply state) ∧
      ∀ d, d ≤ B.toSupported.travel →
        ∃ port phase,
          stepN w d (e, flipAt state A.actionSwitch) =
            some (port, phase) ∧
          (phase = flipAt state A.actionSwitch ∨ phase = state ∨
            phase = B.toSupported.action.apply state)) := by
  have htrace := B.orientedRoute_trace state hB
  have hsimple := B.orientedRoute_simple state
  have hgrooved := htrace.grooved_of_switchSimple hsimple
  obtain ⟨path, hp, old, ho, hsw⟩ := hcontact
  obtain ⟨passage, hmem, horient⟩ := B.support_passage_on_orientedRoute state hp ho
  have holdGroove := hB path hp old ho
  have hswitch : passageSwitch passage = A.actionSwitch := by
    rcases horient with rfl | rfl
    · exact hsw
    · have hsame := arrive_exit_switch state old.2
      rw [holdGroove] at hsame
      exact hsame.symm.trans hsw
  rcases passage with ⟨p, x⟩
  obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
  change p / 3 = A.actionSwitch at hswitch
  by_cases hstem : p % 3 = 0
  · have hmouth : p = A.mouth := by
      have hm := A.mouth_is_stem
      unfold ManufacturedFlipReflector.actionSwitch at hswitch
      omega
    subst p
    obtain ⟨hprefix, hforeign⟩ := simple_grooved_trace_prefix_to_occurrence
      htrace hoccurs hgrooved hsimple
    have hpreGrooved : PassagesGrooved state before := by
      intro passage hp
      exact hgrooved passage (by rw [hoccurs]; exact List.mem_append_left _ hp)
    have hprefixFlip : PhysicalTrace w (e, flipAt state A.actionSwitch) before
        (A.mouth, flipAt state A.actionSwitch) := hprefix.flip_unvisited hforeign
    have hpreFlip := grooved_after_flip_other hpreGrooved hforeign
    have hcapture := A.capture_from_mouth state
      (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
    exact Or.inl ⟨before.length + (A.candy.length + 2 + A.runway.length),
      hprefixFlip.prepend_two_phase hpreFlip hcapture
        (fun _ hd => A.capture_from_mouth_two_phase state
          (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2 hd)⟩
  · have hmerge := htrace.trailing_fault_merges hgrooved hsimple hoccurs hstem
    rw [hswitch] at hmerge
    have hrouteLen := B.orientedRoute_length_le_travel state
    have hrepairLe : before.length + 1 ≤ B.toSupported.travel := by
      rw [hoccurs, List.length_append, List.length_cons] at hrouteLen
      omega
    right
    constructor
    · rw [hmerge.2 _ hrepairLe]
      exact (B.toSupported.run state hB).1
    · intro d hd
      by_cases hpre : d ≤ before.length
      · obtain ⟨port, hr⟩ := hmerge.1 d hpre
        exact ⟨port, flipAt state A.actionSwitch, hr, Or.inl rfl⟩
      · obtain ⟨port, phase, hr, hv⟩ := B.travel_two_phase_stepN state hB hd
        exact ⟨port, phase, (hmerge.2 d (by omega)).trans hr, Or.inr hv⟩

/-- Flip/flip specialization of the selected-route theorem. -/
theorem manufactured_support_fault_dichotomy_pointwise
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g) (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) ∨
    (stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) ∧
      ∀ d, d ≤ 2 * B.runway.length + B.candy.length + 2 →
        ∃ port phase,
          stepN w d (e, flipAt state A.actionSwitch) =
            some (port, phase) ∧
          (phase = flipAt state A.actionSwitch ∨ phase = state ∨
            phase = flipAt state B.actionSwitch)) :=
  ManufacturedReflector.support_fault_dichotomy_pointwise A (.flip B) state hA hB hcontact

end GeneralN
