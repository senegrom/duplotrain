import PartialSecondRunSharp

/-!
# Coefficient-one continuation bounds

Assemble cycle, changed-contact, and two-reflector continuation bounds.
The sharp known-edge frontier works on total wirings, on which every
probe is live, so no dead-continuation case arises.
-/

namespace GeneralN

/-- The partial-continuation contact record is definitionally the sharp
`PartialSecondRunSharp.ChangedContact` record; all its member lemmas live in
that namespace. -/
abbrev SimpleContinuationChangedContact
    {g e : Nat} (w : Wiring) (A : ManufacturedReflector w g e) :
    Type :=
  PartialSecondRunSharp.ChangedContact w A

/-- Coefficient-one history through the first damaging contact.  The first
reflector and all productive approach writers share the same `N`-coordinate
budget; the changed post-vector is the only extra singleton. -/
def PartialSecondRunSharp.ChangedContact.compressedLead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A) (N : Nat) :
    List (List Bool) :=
  A.sharpHistoryCore N ++
    ((rawFirstWriterHistory w N (e, A.activatedState)
      C.approach.length).erase
        (VectorCount.restrict N A.activatedState) ++
      [VectorCount.restrict N C.nextState])

theorem PartialSecondRunSharp.ChangedContact.compressedLead_length_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState) :
    (C.compressedLead N).length ≤ N + 3 := by
  have hboundary : VectorCount.restrict N A.activatedState ∈
      rawFirstWriterHistory w N (e, A.activatedState)
        C.approach.length := by
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN]
  have hcharge := A.reusable_add_continuation_first_writers_le
    hN C.approach_trace C.approach_simple hA C.old_grooves
  have houter := A.exploration_length_le_reusable_add_one
  unfold PartialSecondRunSharp.ChangedContact.compressedLead
  rw [List.length_append, List.length_append,
    List.length_erase_of_mem hboundary, A.sharpHistoryCore_length]
  simp [rawFirstWriterHistory]
  omega

section
variable {w : Wiring} {N g e : Nat}
  {A : ManufacturedReflector w g e}
  (C : SimpleContinuationChangedContact w A)
include w N g e A C

theorem PartialSecondRunSharp.ChangedContact.mem_compressedLead_of_approach
    {j : Nat} (hj : j ≤ C.approach.length) :
    restrictedTonguesAt w N (e, A.activatedState) j ∈
      C.compressedLead N := by
  have hm := C.approach_trace.restrictedTonguesAt_mem_rawFirstWriterHistory
    (N := N) C.approach_simple j hj
  by_cases hboundary : restrictedTonguesAt w N
      (e, A.activatedState) j =
      VectorCount.restrict N A.activatedState
  · apply List.mem_append_left
    rw [hboundary]
    exact A.activated_mem_sharpHistoryCore
  · apply List.mem_append_right
    apply List.mem_append_left
    exact (List.mem_erase_of_ne hboundary).mpr hm

theorem PartialSecondRunSharp.ChangedContact.contact_mem_compressedLead :
    VectorCount.restrict N C.contactState ∈ C.compressedLead N := by
  have hm := C.mem_compressedLead_of_approach
    (N := N) (j := C.approach.length) (Nat.le_refl _)
  simpa [restrictedTonguesAt, tonguesAt,
    C.approach_trace.sound] using hm

theorem PartialSecondRunSharp.ChangedContact.next_mem_compressedLead :
    VectorCount.restrict N C.nextState ∈ C.compressedLead N := by grind [PartialSecondRunSharp.ChangedContact.compressedLead, VectorCount.restrict]

/-- A backward first damaging contact closes immediately into the old
route-prefix lasso.  Every local vector, including the two contact phases,
is already in the coefficient-one compressed lead. -/
theorem PartialSecondRunSharp.ChangedContact.backward_all_time_zero_novelty
    (hbackward : C.x = C.oriented.1)
    (times : List Nat) :
    NoveltyCoverOn w N (e, A.activatedState)
      times (C.compressedLead N) 0 := by
  obtain ⟨recorded, tail, hrouteSplit⟩ :=
    List.append_of_mem C.oriented_mem
  have hroute :=
    A.orientedRoute_trace C.contactState C.old_grooves
  have hrouteSimple :=
    A.orientedRoute_simple C.contactState
  have hrouteGrooved :=
    hroute.grooved_of_switchSimple hrouteSimple
  have hprefixData :=
    simple_grooved_trace_prefix_to_occurrence
      hroute hrouteSplit hrouteGrooved hrouteSimple
  have hrecorded := hprefixData.1
  have hrecordedSimple : SwitchSimple recorded := by
    unfold SwitchSimple at hrouteSimple ⊢
    rw [hrouteSplit] at hrouteSimple
    simp only [List.map_append, List.map_cons] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hrecordedGrooved :
      PassagesGrooved C.contactState recorded :=
    hrecorded.grooved_of_switchSimple hrecordedSimple
  have hrecordedForeign : ∀ passage ∈ recorded,
      passageSwitch passage ≠ C.p / 3 := by
    intro passage hp hEq
    apply hprefixData.2 passage hp
    exact hEq.trans C.oriented_switch.symm
  have happroachGrooved :
      PassagesGrooved C.contactState C.approach :=
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
  have hrecordedNext :
      PassagesGrooved C.nextState recorded := by
    rw [hnextForm]
    exact grooved_after_flip_other
      hrecordedGrooved hrecordedForeign
  have happroachNext :
      PassagesGrooved C.nextState C.approach := by
    rw [hnextForm]
    exact grooved_after_flip_other
      happroachGrooved happroachForeign
  have happroachReplay :
      PhysicalTrace w (e, C.contactState) C.approach
        (C.p, C.contactState) :=
    C.approach_trace.replay_grooved
      C.contactState happroachGrooved
  have hcontact :
      arrive C.contactState C.p =
        (C.oriented.1, C.nextState) := by
    simpa [hbackward] using C.arrive_eq
  have hall :=
    backward_contact_all_time_two_phase
      hrecorded hrecordedNext A.entryEdge hcontact
      happroachReplay happroachNext
  have hstateHistorical := C.contact_mem_compressedLead (N := N)
  have hnextHistorical := C.next_mem_compressedLead (N := N)
  exact ⟨[], by simp, cover_of_live_phase_orbit
    (phases := [C.contactState, C.nextState]) C.approach_trace.sound
    (fun d => by
      obtain ⟨port, phase, hr, hp⟩ := hall d
      exact ⟨port, phase, hr, by simpa using hp⟩)
    (by simp [hstateHistorical, hnextHistorical])
    (fun j _ hjK => C.mem_compressedLead_of_approach (N := N) (by omega))⟩

end

/-- Lift a local novelty cover after the manufacturing journey to a count for
the complete run.  The only global cost is the compressed lead plus the local
novelty budget. -/
theorem PartialSecondRunSharp.ChangedContact.changed_all_run_distinct_le_compressedLead_add_budget
    {w : Wiring} {N g e budget : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup)
    (hlocal : NoveltyCoverOn w N (e, A.activatedState)
      (times.map (fun k => k -
        (A.exploration.length + A.runway.length + 1)))
      (C.compressedLead N) budget) :
    times.length <= (C.compressedLead N).length + budget := by
  apply noveltyCoverOn_distinct_count (hnd := hnd)
  apply hlocal.prepend (A.manufacturing_journey_reaches_activated hA) ?_ hlive
    (fun k hk _ => List.mem_map.mpr ⟨k, hk, rfl⟩)
  intro k hk
  exact List.mem_append_left _ (A.mem_sharpHistoryCore_of_mem
    (A.manufacturing_journey_mem_sharpHistory hA hk))

/-- Absolute coefficient-one bound for the entire original run once the
first damaging continuation contact points backward. -/
theorem PartialSecondRunSharp.ChangedContact.backward_all_run_distinct_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hbackward : C.x = C.oriented.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 3 := by
  have hcount := C.changed_all_run_distinct_le_compressedLead_add_budget hA times hlive hnd
    (C.backward_all_time_zero_novelty hbackward _)
  have hlength := C.compressedLead_length_le hN hA
  omega

/-- **Forward flip contact, the corner cover.**  After a forward
first-changing contact into a flip reflector every sampled vector lies in the
compressed contact history or is one of the two action corners of the
post-contact and contact states. -/
theorem PartialSecondRunSharp.ChangedContact.forward_flip_corner_cover
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hforward : C.x = C.oriented.2)
    (times : List Nat) :
    ∀ k ∈ times, restrictedTonguesAt w N
      (e, (ManufacturedReflector.flip R).activatedState) k ∈
      C.compressedLead N ++
        [VectorCount.restrict N (flipAt C.nextState R.actionSwitch),
         VectorCount.restrict N (flipAt C.contactState R.actionSwitch)] := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachGrooved,
      hApproachForeign, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach⟩ :=
    partial_first_forward_contact_active_lead
      (A := ManufacturedReflector.flip R) C.split C.full_simple
      C.approach_trace C.old_grooves C.arrive_eq C.changed
      C.oriented_mem C.oriented_groove hforward
  have hnextAlternate : C.nextState = flipAt C.contactState (mouth / 3) :=
    C.nextState_eq_of_post hreach
  have hentryHistorical :
      VectorCount.restrict N (flipAt C.contactState (mouth / 3)) ∈ C.compressedLead N := by
    simpa [hnextAlternate] using C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N C.contactState ∈ C.compressedLead N :=
    C.contact_mem_compressedLead
  have hleadHistorical : ∀ j ∈ times, j < C.approach.length + 1 →
      restrictedTonguesAt w N
        (e, (ManufacturedReflector.flip R).activatedState) j ∈
          C.compressedLead N :=
    fun j _ hjK => C.mem_compressedLead_of_approach (N := N) (by omega)
  rw [hnextAlternate]
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ := List.append_of_mem hrunway
    obtain ⟨D, hDAction, hEntryOldNe, hDpaths, hNewAvoidsDRaw⟩ :=
      R.suffix_after_runway_passage C.contactState hRpaths hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove : arrive C.contactState entry = (mouth, C.contactState) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch C.contactState entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe : mouth / 3 ≠ D.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsD :
        (LocalAction.flip (mouth / 3)).Avoids D.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsDRaw
    by_cases hcontact : ∃ passage ∈ candy, passageSwitch passage = D.actionSwitch
    · exact cover_of_live_phase_orbit
        (phases := [flipAt C.contactState (mouth / 3),
          flipAt (flipAt C.contactState (mouth / 3)) D.actionSwitch,
          C.contactState, flipAt C.contactState D.actionSwitch]) hreach
        (manufactured_flip_arbitrary_lobe_all_time_four_phase D C.contactState hDpaths
          hNewAvoidsD hentryBranch hentrySwitch hfullGrooved hfullTrace hcrossed
          hCandyForeignNew hLobe hmouthLink hcontact)
        (by simp [hDAction, hentryHistorical, hstateHistorical]) hleadHistorical
    · have hCandyForeignOld : ∀ passage ∈ candy, passageSwitch passage ≠ D.actionSwitch :=
        fun passage hp hEq => hcontact ⟨passage, hp, hEq⟩
      exact cover_of_live_phase_orbit
        (phases := [flipAt C.contactState (mouth / 3),
          flipAt (flipAt C.contactState (mouth / 3)) D.actionSwitch,
          flipAt C.contactState D.actionSwitch, C.contactState]) hreach
        (manufactured_suffix_explicit_lobe_all_time_four_phase D C.contactState hDpaths
          hNewAvoidsD hActionsNe hentryBranch hentrySwitch hfullGrooved hfullTrace
          hcrossed hCandyForeignNew hCandyForeignOld hLobe hmouthLink)
        (by simp [hDAction, hentryHistorical, hstateHistorical]) hleadHistorical
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy C.contactState hentryOld hrunway hentryBranch
    exact cover_of_live_phase_orbit
      (phases := [flipAt C.contactState (mouth / 3),
        flipAt (flipAt C.contactState (mouth / 3)) R.actionSwitch]) hreach
      (fun d => by
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using
          manufactured_flip_candy_splice_all_two_phases
            R C.contactState hRpaths hrouteSplit hOldTail hrunway hentryBranch
            hold horientation (hfullGrooved (mouth, entry) List.mem_cons_self)
            hApproachReplay hApproachGrooved hApproachForeign hcrossed hmouthLink harms d)
      (by simp [hentryHistorical]) hleadHistorical

/-- The stay-forward branch contributes no vector beyond the contact pre/post
vectors already stored in `compressedLead`. -/
theorem PartialSecondRunSharp.ChangedContact.forward_stay_zero_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.stay R))
    (hforward : C.x = C.oriented.2)
    (times : List Nat) :
    NoveltyCoverOn w N
      (e, (ManufacturedReflector.stay R).activatedState)
      times (C.compressedLead N) 0 := by
  obtain ⟨outside, mouth, hreach, hall⟩ :=
    C.forward_stay_two_phase_tail hforward
  have hnextHistorical := C.next_mem_compressedLead (N := N)
  rw [C.nextState_eq_of_post hreach] at hnextHistorical
  have hstateHistorical := C.contact_mem_compressedLead (N := N)
  exact ⟨[], by simp, cover_of_live_phase_orbit
    (phases := [flipAt C.contactState (mouth / 3), C.contactState]) hreach
    (fun d => by
      obtain ⟨port, phase, hr, hp⟩ := hall d
      exact ⟨port, phase, hr, by simpa using hp⟩)
    (by simp [hnextHistorical, hstateHistorical])
    (fun j _ hjK => C.mem_compressedLead_of_approach (N := N) (by omega))⟩

/-- Every first-changing contact of an arbitrary simple continuation has at
most two post-contact novelty vectors.  Backward contacts are exact retrace
lassos; forward contacts are the stay/flip splices above. -/
theorem PartialSecondRunSharp.ChangedContact.changed_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (times : List Nat) :
    NoveltyCoverOn w N (e, A.activatedState)
      times (C.compressedLead N) 2 := by
  rcases C.direction with hbackward | hforward
  · obtain ⟨fresh, hfresh, hmem⟩ :=
      C.backward_all_time_zero_novelty
        (N := N) hbackward times
    exact ⟨fresh, by omega, hmem⟩
  · cases A with
    | stay R =>
        obtain ⟨fresh, hfresh, hmem⟩ :=
          C.forward_stay_zero_novelty
            hforward times
        exact ⟨fresh, by omega, hmem⟩
    | flip R =>
        exact ⟨_, by simp, C.forward_flip_corner_cover hforward times⟩

end GeneralN
