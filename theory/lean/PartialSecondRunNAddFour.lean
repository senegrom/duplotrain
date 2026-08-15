import StateLawCoefficientOneTop

/-!
# The `N+4` partial-second-run frontier

This file sharpens the two non-pair outcomes of the second probe after one
manufactured reflector.  It deliberately does not alter the older `N+5`
interfaces.

The first result is stronger than the requested coefficient: a dead second
run cannot damage the old supported route at all.  Every possible first
damaging contact is already an infinite lasso or an eventually-periodic
forward splice.  Consequently the dead branch is support-preserving and has
the existing `N+2` bound.

The stable-cycle branch is treated below, retaining the exact runway residual
which is the only branch in the present APIs that can still spend both Gray
corners after an `N+3` coefficient-one contact history.
-/

namespace GeneralN

namespace PartialSecondRunNAddFour

open PartialSecondRunSharp

private theorem stepN_some_all_of_reach
    {w : Wiring} {start middle : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some middle)
    (htail : ∀ d, ∃ finish, stepN w d middle = some finish) :
    ∀ d, ∃ finish, stepN w d start = some finish := by
  intro d
  by_cases hd : d ≤ K
  · exact stepN_prefix_some hd hreach
  · let q := d - K
    have hdEq : d = K + q := by
      dsimp [q]
      omega
    obtain ⟨finish, hfinish⟩ := htail q
    refine ⟨finish, ?_⟩
    rw [hdEq, stepN_add, hreach]
    exact hfinish

/-- The backward damaging contact is already a literal all-time lasso. -/
theorem changedContact_backward_stepN_some_all
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A)
    (hbackward : C.x = C.oriented.1) :
    ∀ d, ∃ finish,
      stepN w d (e, A.activatedState) = some finish := by
  obtain ⟨recorded, _tail, hrouteSplit⟩ :=
    List.append_of_mem C.oriented_mem
  have hroute := A.orientedRoute_trace C.contactState C.old_grooves
  have hrouteSimple := A.orientedRoute_simple C.contactState
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hrouteSplit hrouteGrooved hrouteSimple
  have hrecorded := hprefixData.1
  have hrecordedSimple : SwitchSimple recorded := by
    unfold SwitchSimple at hrouteSimple ⊢
    rw [hrouteSplit] at hrouteSimple
    simp only [List.map_append, List.map_cons] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hrecordedGrooved : PassagesGrooved C.contactState recorded :=
    hrecorded.grooved_of_switchSimple hrecordedSimple
  have hrecordedForeign : ∀ passage ∈ recorded,
      passageSwitch passage ≠ C.p / 3 := by
    intro passage hp hEq
    apply hprefixData.2 passage hp
    exact hEq.trans C.oriented_switch.symm
  have happroachGrooved : PassagesGrooved C.contactState C.approach :=
    C.approach_trace.grooved_of_switchSimple C.approach_simple
  have happroachForeign : ∀ passage ∈ C.approach,
      passageSwitch passage ≠ C.p / 3 := by
    have hs := C.full_simple
    unfold SwitchSimple at hs
    rw [C.split] at hs
    simp only [List.map_append, List.map_cons] at hs
    have hparts := List.nodup_append.mp hs
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (C.p, C.x)) (by simp)
    exact hne (by simpa [passageSwitch] using hEq)
  have hnextForm :
      C.nextState = flipAt C.contactState (C.p / 3) :=
    changed_arrival_eq_flipAt C.arrive_eq C.changed
  have hrecordedNext : PassagesGrooved C.nextState recorded := by
    rw [hnextForm]
    exact grooved_after_flip_other hrecordedGrooved hrecordedForeign
  have happroachNext : PassagesGrooved C.nextState C.approach := by
    rw [hnextForm]
    exact grooved_after_flip_other happroachGrooved happroachForeign
  have happroachReplay :
      PhysicalTrace w (e, C.contactState) C.approach
        (C.p, C.contactState) :=
    C.approach_trace.replay_grooved
      C.contactState happroachGrooved
  have hcontact : arrive C.contactState C.p =
      (C.oriented.1, C.nextState) := by
    simpa [hbackward] using C.arrive_eq
  have hall := backward_contact_all_time_two_phase_two_history
    hrecorded hrecordedNext A.entryEdge hcontact
    happroachReplay happroachNext
  apply stepN_some_all_of_reach C.approach_trace.sound
  intro d
  obtain ⟨port, phase, hrun, _hphase⟩ := hall d
  exact ⟨(port, phase), hrun⟩

/-- A forward contact into a flip reflector reaches an explicitly periodic
runway or candy splice. -/
theorem changedContact_forward_flip_tail_eventuallyPeriodic
    {w : Wiring} {g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : ChangedContact w (ManufacturedReflector.flip R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 = (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 = (C.oriented.1, repaired)) :
    ∃ outside state,
      stepN w (C.approach.length + 1)
          (e, (ManufacturedReflector.flip R).activatedState) =
        some (outside, state) ∧
      EventuallyPeriodic w (outside, state) := by
  have hsimple := C.full_simple
  rw [C.split] at hsimple
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, _tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, _hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete⟩ :=
    partial_forward_contact_active_lead
      (A := ManufacturedReflector.flip R)
      hsimple C.approach_trace C.old_grooves C.arrive_eq C.changed
      C.oriented_mem C.oriented_groove C.oriented_switch
      hforward hrepair hrestored
  have hperiodic : EventuallyPeriodic w
      (outside, flipAt C.contactState (mouth / 3)) := by
    by_cases hrunway : (entry, mouth) ∈ R.runway
    · exact manufactured_flip_runway_splice_periodic
        R C.contactState hRpaths hrunway hmouthLink hentryBranch
        hfullGrooved hfullTrace hcrossed hCandy hCandyForeign hLobe
    · obtain ⟨old, hold, horientation⟩ :=
        R.nonrunway_oriented_branch_entry_is_candy
          C.contactState hentryOld hrunway hentryBranch
      have hentryGrooved :
          arrive C.contactState entry = (mouth, C.contactState) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      by_cases hcontact : ∃ passage ∈ C.approach,
          passageSwitch passage = R.actionSwitch
      · exact (manufactured_flip_candy_splice_periodic_of_approach_contact
          R C.contactState hRpaths hrouteSplit hOldTail hrunway
          hentryBranch hold horientation hentryGrooved hApproachReplay
          hApproachGrooved hApproachForeign hcrossed hmouthLink harms
          hcontact).1
      · have hApproachForeignOld : ∀ passage ∈ C.approach,
            passageSwitch passage ≠ R.actionSwitch := by
          intro passage hp hEq
          exact hcontact ⟨passage, hp, hEq⟩
        exact (manufactured_flip_candy_splice_periodic_of_approach_foreign
          R C.contactState hRpaths hrouteSplit hOldTail hrunway
          hentryBranch hold horientation hentryGrooved hApproachReplay
          hApproachForeign hApproachForeignOld hcrossed hmouthLink).1
  exact ⟨outside, flipAt C.contactState (mouth / 3), hreach, hperiodic⟩

/-- A forward contact into a flip reflector is live at every later time. -/
theorem changedContact_forward_flip_stepN_some_all
    {w : Wiring} {g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : ChangedContact w (ManufacturedReflector.flip R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 = (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 = (C.oriented.1, repaired)) :
    ∀ d, ∃ finish,
      stepN w d (e, (ManufacturedReflector.flip R).activatedState) =
        some finish := by
  obtain ⟨outside, state, hreach, hperiodic⟩ :=
    changedContact_forward_flip_tail_eventuallyPeriodic
      C hforward hrepair hrestored
  apply stepN_some_all_of_reach hreach
  exact hperiodic.stepN_some_all

/-- Every first damaging contact after one completed reflector is live
forever.  This is the key fact omitted by the old dead-run count. -/
theorem changedContact_stepN_some_all
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A) :
    ∀ d, ∃ finish,
      stepN w d (e, A.activatedState) = some finish := by
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · exact changedContact_backward_stepN_some_all C hbackward
  · cases A with
    | stay R =>
        obtain ⟨outside, _mouth, hreach, hall⟩ :=
          C.forward_stay_two_phase_tail hforward hrepair hrestored
        apply stepN_some_all_of_reach hreach
        intro d
        obtain ⟨port, phase, hrun, _hphase⟩ := hall d
        exact ⟨(port, phase), hrun⟩
    | flip R =>
        exact changedContact_forward_flip_stepN_some_all
          C hforward hrepair hrestored

/-- **Dead second run, sharp form.**  The damaged-support case would be live
forever by `ChangedContact.stepN_some_all`, contradicting the dead horizon.
Thus the old support is preserved and the existing `N+2` theorem applies. -/
theorem ManufacturedReflector.dead_second_run_distinct_le_N_add_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hdead : stepN w (N + 1) (e, A.activatedState) = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 2 := by
  obtain ⟨finish, passages, _hlength, htrace, hfall⟩ :=
    PartialSecondRunSharp.terminal_trace_of_dead hdead
  have hsimple : SwitchSimple passages :=
    ManufacturedReflector.dead_continuation_trace_simple
      A hA hdead htrace
  by_cases hend : PathGrooves A.toSupported.paths finish.2
  · exact preserved_simple_fall_distinct_le_N_add_two
      hN A hA htrace hsimple hend hfall times hlive hnd
  · obtain ⟨C⟩ :=
      ManufacturedReflector.changedContact_of_broken_simple
        A hA htrace hsimple hend
    obtain ⟨later, hlater⟩ :=
      changedContact_stepN_some_all C (N + 1)
    rw [hdead] at hlater
    cases hlater

/-! ## The retained one-vector-cycle branch -/

end PartialSecondRunNAddFour
end GeneralN
