import OneReflectorContinuation

/-!
# First damaging contact after a manufactured reflector

A switch-simple continuation that breaks the old support has a first
damaging passage. Its orientation determines a backward retrace or a
forward splice; both retain the same compressed continuation history.
-/

namespace GeneralN

namespace PartialSecondRunSharp

/-- The first passage of an arbitrary switch-simple continuation which
actually damages the completed reflector's reusable support. -/
structure ChangedContact
    {g e : Nat} (w : Wiring) (A : ManufacturedReflector w g e) : Type where
  full : List Passage
  finish : Nat × Tongues
  approach : List Passage
  p : Nat
  x : Nat
  suffix : List Passage
  contactState : Tongues
  nextState : Tongues
  oriented : Passage
  full_simple : SwitchSimple full
  split : full = approach ++ (p, x) :: suffix
  approach_trace :
    PhysicalTrace w (e, A.activatedState) approach (p, contactState)
  suffix_trace :
    PhysicalTrace w (p, contactState) ((p, x) :: suffix) finish
  old_grooves : PathGrooves A.toSupported.paths contactState
  arrive_eq : arrive contactState p = (x, nextState)
  changed : nextState (p / 3) ≠ contactState (p / 3)
  oriented_mem : oriented ∈ A.orientedRoute contactState
  oriented_groove :
    arrive contactState oriented.2 = (oriented.1, contactState)
  oriented_switch : passageSwitch oriented = p / 3
  direction : x = oriented.1 ∨ x = oriented.2

/-- Extract the first damaging support passage from a partial continuation;
no completed second reflector is assumed. -/
theorem ManufacturedReflector.changedContact_of_broken_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    (hbroken : ¬ PathGrooves A.toSupported.paths finish.2) :
    Nonempty (ChangedContact w A) := by
  obtain ⟨approach, p, x, suffix, u, v, path, old,
      hsplit, happroach, hgrooves, harrive,
      hpath, hold, hswitch, hchanged⟩ :=
    htrace.first_changed_support_passage hA hbroken
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    A.changed_contact_on_orientedRoute u v hgrooves hpath hold
      hswitch harrive
  have hafter := (hsplit ▸ htrace).after_prefix happroach
  exact ⟨{
    full := passages
    finish := finish
    approach := approach
    p := p
    x := x
    suffix := suffix
    contactState := u
    nextState := v
    oriented := oriented
    full_simple := hsimple
    split := hsplit
    approach_trace := happroach
    suffix_trace := hafter
    old_grooves := hgrooves
    arrive_eq := harrive
    changed := hchanged
    oriented_mem := horiented
    oriented_groove := horientedGroove
    oriented_switch := horientedSwitch
    direction := hdirection
  }⟩

theorem ChangedContact.approach_simple
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A) :
    SwitchSimple C.approach := by
  have hs := C.full_simple
  unfold SwitchSimple at hs ⊢
  rw [C.split] at hs
  simp only [List.map_append, List.map_cons] at hs
  exact (List.nodup_append.mp hs).1

theorem ChangedContact.post_reaches
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A) :
    ∃ q, stepN w (C.approach.length + 1)
      (e, A.activatedState) = some (q, C.nextState) := by
  cases C.suffix_trace with
  | @cons _ _ q _ next _ _ harrive hlink tail =>
      have hnext : next = C.nextState := by
        rw [C.arrive_eq] at harrive
        exact (Prod.mk.inj harrive).2.symm
      subst next
      refine ⟨q, ?_⟩
      rw [stepN_add, C.approach_trace.sound]
      simp [stepN, step, C.arrive_eq, hlink]

/-- Any reach equation at the post-contact time names the post-contact
state. -/
theorem ChangedContact.nextState_eq_of_post
    {w : Wiring} {g e : Nat} {A : ManufacturedReflector w g e}
    (C : ChangedContact w A) {port : Nat} {phase : Tongues}
    (h : stepN w (C.approach.length + 1) (e, A.activatedState) =
      some (port, phase)) : C.nextState = phase := by
  obtain ⟨q, hq⟩ := C.post_reaches
  rw [h] at hq
  exact (congrArg Prod.snd (Option.some.inj hq)).symm

/-- Exact two-phase tail after a changed forward contact with a stay
reflector, generalized to an arbitrary switch-simple partial route. -/
theorem ChangedContact.forward_stay_two_phase_tail
    {w : Wiring} {g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : ChangedContact w (ManufacturedReflector.stay R))
    (hforward : C.x = C.oriented.2) :
    ∃ outside mouth,
      stepN w (C.approach.length + 1)
        (e, (ManufacturedReflector.stay R).activatedState) =
          some (outside, flipAt C.contactState (mouth / 3)) ∧
      ∀ d, ∃ port phase,
        stepN w d
          (outside, flipAt C.contactState (mouth / 3)) =
            some (port, phase) ∧
        (phase = flipAt C.contactState (mouth / 3) ∨
          phase = C.contactState) := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, hentryOld, hrouteSplit, hOldTail,
      _hApproachReplay, hApproachGrooved,
      hApproachForeign, hentryBranch, hentryMouthSwitch,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach⟩ :=
    partial_first_forward_contact_active_lead
      (A := ManufacturedReflector.stay R)
      C.split C.full_simple C.approach_trace C.old_grooves
      C.arrive_eq C.changed C.oriented_mem C.oriented_groove
      hforward
  let L : SupportedReflector w mouth outside := {
    travel := candy.length + 2
    paths := [candy]
    action := .flip (mouth / 3)
    run := by simpa [IsReflector, PathGrooves, LocalAction.apply] using hLobe
  }
  let alternate := flipAt C.contactState (mouth / 3)
  have hLalt : PathGrooves L.paths alternate := by
    simpa [L, PathGrooves, alternate] using grooved_after_flip_other hCandy hCandyForeign
  have htwo : ∀ u, PathGrooves L.paths u → ∀ t, t ≤ L.travel →
      ∃ port phase, stepN w t (mouth, u) = some (port, phase) ∧
        (phase = u ∨ phase = L.action.apply u) := by
    intro u hu t ht
    exact explicit_lobe_two_phase_at hentryBranch hentryMouthSwitch hfullGrooved
      hfullTrace hcrossed hCandyForeign hmouthLink u (hu candy (by simp [L])) ht
  refine ⟨outside, mouth, hreach, ?_⟩
  change (entry, mouth) ∈ R.runway ++ [(R.mouth, R.arm)] at hentryOld
  rcases List.mem_append.mp hentryOld with hrunway | hcore
  · obtain ⟨before, after, hsplit⟩ := List.append_of_mem hrunway
    obtain ⟨D, hDpaths, hAvoid⟩ :=
      R.suffix_after_runway_passage C.contactState hRpaths hsplit hmouthLink
    have hAvoid' : L.action.Avoids D.toSupported.paths := by
      simpa only [hentryMouthSwitch] using hAvoid
    have hDalt := hDpaths.after_avoiding_action hAvoid'
    intro d
    have hcover := D.toSupported.pair_all_time_four_phase L
      (ManufacturedReflector.stay D).travel_pos (by dsimp [L]; omega)
      (fun u hu _ ht => (ManufacturedReflector.stay D).travel_two_phase_stepN u hu ht)
      htwo alternate hDalt hLalt (by trivial) hAvoid' d
    simpa [L, ManufacturedStayReflector.toSupported, LocalAction.apply,
      alternate, flipAt_flipAt] using hcover
  · have hmouthEq : mouth = R.arm := congrArg Prod.snd (List.mem_singleton.mp hcore)
    have houtsideEq : outside = mouth := by
      rw [hmouthEq, R.selfLink] at hmouthLink
      exact (Option.some.inj hmouthLink).symm.trans hmouthEq.symm
    subst outside
    have hAvoid : L.action.Avoids L.paths := by
      intro path hp passage hm
      have heq : path = candy := by simpa [L] using hp
      subst path
      exact hCandyForeign passage hm
    intro d
    have hcover := L.pair_all_time_four_phase L
      (by dsimp [L]; omega) (by dsimp [L]; omega)
      htwo htwo alternate hLalt hLalt hAvoid hAvoid d
    obtain ⟨port, phase, hr, hs⟩ := hcover
    refine ⟨port, phase, hr, ?_⟩
    simp only [L, LocalAction.apply, alternate, flipAt_flipAt,
      List.mem_cons, List.not_mem_nil, or_false] at hs
    grind


end PartialSecondRunSharp
end GeneralN
