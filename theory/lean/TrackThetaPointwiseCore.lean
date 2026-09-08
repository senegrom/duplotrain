import RunwaySpliceNovelty

/-!
# A support fault on the selected route

Normalize the reflector's outward route once. Before its first contact
with the disturbed switch the flipped and undisturbed walks differ only
at that switch. A stem entry invokes the other reflector's capture; a
branch entry repairs the tongue and merges into the undisturbed walk.
The shared first-contact law also handles arbitrary grooved lobes, without
requiring their routes to be switch-simple.
-/

namespace GeneralN

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
  rcases A.grooved_route_fault state hA htrace hgrooved
      ⟨passage, hmem, hswitch⟩ with hcapture | hrepair
  · exact Or.inl hcapture
  · obtain ⟨cutoff, hcutoff, hpre, hmerge⟩ := hrepair
    have hle : cutoff ≤ B.toSupported.travel := by
      rw [B.travel_eq_oriented_add state]; omega
    refine Or.inr ⟨(hmerge _ hle).trans (B.toSupported.run state hB).1, ?_⟩
    intro d hd
    by_cases hearly : d < cutoff
    · obtain ⟨port, hr⟩ := hpre d hearly
      exact ⟨port, _, hr, Or.inl rfl⟩
    · obtain ⟨port, phase, hr, hv⟩ := B.travel_two_phase_stepN state hB hd
      exact ⟨port, phase, (hmerge d (by omega)).trans hr, Or.inr hv⟩

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

/-- A grooved approach followed by a two-phase return closes a two-state
boundary invariant. The approach may meet the action switch: its first contact
either captures back to the boundary or repairs and synchronizes. Later visits
need not be excluded, and the return may have any positive duration. -/
theorem ManufacturedFlipReflector.grooved_return_two_phase
    {w : Wiring} {g e p : Nat} (R : ManufacturedFlipReflector w g e)
    (state : Tongues) (hR : PathGrooves R.toSupported.paths state)
    {route : List Passage}
    (htrace : PhysicalTrace w (e, state) route (p, state))
    (hgrooved : PassagesGrooved state route)
    (hreturn : ∀ current, (current = state ∨ current = flipAt state R.actionSwitch) →
      ∃ travel final, 0 < travel ∧
        stepN w travel (p, current) = some (e, final) ∧
        (final = state ∨ final = flipAt state R.actionSwitch) ∧
        ∀ d, d ≤ travel → ∃ port phase,
          stepN w d (p, current) = some (port, phase) ∧
          (phase = state ∨ phase = flipAt state R.actionSwitch))
    {startPort : Nat} (hport : startPort = e ∨ startPort = p)
    {initial : Tongues} (hinitial : initial = state ∨ initial = flipAt state R.actionSwitch)
    (d : Nat) :
    ∃ port phase, stepN w d (startPort, initial) = some (port, phase) ∧
      (phase = state ∨ phase = flipAt state R.actionSwitch) := by
  let safe := fun phase => phase = state ∨ phase = flipAt state R.actionSwitch
  have hfollow : ∀ current, safe current →
      PhysicalTrace w (e, current) route (p, current) → PassagesGrooved current route →
      ∃ travel final, route.length < travel ∧
        stepN w travel (e, current) = some (e, final) ∧ safe final ∧
        ∀ t, t ≤ travel → ∃ port phase,
          stepN w t (e, current) = some (port, phase) ∧ safe phase := by
    intro current hs ht hg
    obtain ⟨travel, final, hpos, hr, hf, hc⟩ := hreturn current hs
    refine ⟨route.length + travel, final, by omega, ?_, hf, ?_⟩
    · rw [stepN_add, ht.sound]; exact hr
    · apply stepN_cover_append ht.sound ?_ hc
      intro t ht'
      obtain ⟨port, hp⟩ := ht.grooved_prefix_tongues current hg ht'
      exact ⟨port, current, hp, hs⟩
  have hexcursion : ∀ current, safe current → ∃ travel final,
      0 < travel ∧ stepN w travel (e, current) = some (e, final) ∧ safe final ∧
      ∀ t, t ≤ travel → ∃ port phase,
        stepN w t (e, current) = some (port, phase) ∧ safe phase := by
    intro current hs
    rcases hs with hs | hs <;> subst current
    · obtain ⟨travel, final, hpos, hr, hf, hc⟩ := hfollow state (Or.inl rfl) htrace hgrooved
      exact ⟨travel, final, by omega, hr, hf, hc⟩
    · by_cases htouch : ∃ passage ∈ route, passageSwitch passage = R.actionSwitch
      · rcases R.grooved_route_fault state hR htrace hgrooved htouch with
          ⟨travel, hr, hc⟩ | ⟨cutoff, hbound, hpre, hmerge⟩
        · refine ⟨travel, state, stepN_flip_restore_pos hr, hr, Or.inl rfl, ?_⟩
          intro t ht
          obtain ⟨port, phase, hr, hp⟩ := hc t ht
          exact ⟨port, phase, hr, hp.symm⟩
        · obtain ⟨travel, final, hpos, hr, hf, hc⟩ :=
            hfollow state (Or.inl rfl) htrace hgrooved
          refine ⟨travel, final, by omega, (hmerge _ (by omega)).trans hr, hf, ?_⟩
          intro t ht
          by_cases hearly : t < cutoff
          · obtain ⟨port, hr⟩ := hpre t hearly
            exact ⟨port, _, hr, Or.inr rfl⟩
          · obtain ⟨port, phase, hr, hp⟩ := hc t ht
            exact ⟨port, phase, (hmerge _ (by omega)).trans hr, hp⟩
      · have hforeign : ∀ passage ∈ route, passageSwitch passage ≠ R.actionSwitch := by
          intro passage hp hs
          exact htouch ⟨passage, hp, hs⟩
        obtain ⟨travel, final, hpos, hr, hf, hc⟩ := hfollow _ (Or.inr rfl)
          (htrace.flip_unvisited hforeign) (grooved_after_flip_other hgrooved hforeign)
        exact ⟨travel, final, by omega, hr, hf, hc⟩
  let boundary := fun c : Nat × Tongues => (c.1 = e ∨ c.1 = p) ∧ safe c.2
  have hprogress : ∀ start, boundary start → ∃ travel finish,
      0 < travel ∧ stepN w travel start = some finish ∧ boundary finish ∧
      ∀ t, t ≤ travel → ∃ port phase,
        stepN w t start = some (port, phase) ∧ safe phase := by
    intro ⟨port, current⟩ ⟨hp, hs⟩
    change port = e ∨ port = p at hp
    rcases hp with hp | hp <;> subst port
    · obtain ⟨travel, final, hpos, hr, hf, hc⟩ := hexcursion current hs
      exact ⟨travel, (e, final), hpos, hr, ⟨Or.inl rfl, hf⟩, hc⟩
    · obtain ⟨travel, final, hpos, hr, hf, hc⟩ := hreturn current hs
      exact ⟨travel, (e, final), hpos, hr, ⟨Or.inl rfl, hf⟩, hc⟩
  exact stepN_covered_of_progress boundary safe hprogress ⟨hport, hinitial⟩ d

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
      (phase = contact ∨ phase = flipAt contact B.actionSwitch) := by
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
  exact ⟨port, phase, hr, hp⟩


end GeneralN
