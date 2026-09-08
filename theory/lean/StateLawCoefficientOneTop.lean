import PartialSecondRunSharp

/-!
# Coefficient-one continuation bounds

Assemble cycle, changed-contact, and two-reflector continuation bounds.
The sharp known-edge frontier works on total wirings, on which every
probe is live, so no dead-continuation case arises.
-/

namespace GeneralN

/-- Coefficient-one history through the first damaging contact.  The first
reflector and all productive approach writers share the same `N`-coordinate
budget; the changed post-vector is the only extra singleton. -/
def PartialSecondRunSharp.ChangedContact.compressedLead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w A) (N : Nat) :
    List (List Bool) :=
  A.continuationHistory N (e, A.activatedState) C.approach.length ++
    [VectorCount.restrict N C.nextState]

theorem PartialSecondRunSharp.ChangedContact.compressedLead_length_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState) :
    (C.compressedLead N).length ≤ N + 3 := by
  have hlength := A.continuationHistory_length_le hN rfl C.approach_trace
    C.approach_simple hA C.old_grooves
  simpa [PartialSecondRunSharp.ChangedContact.compressedLead] using Nat.add_le_add_right hlength 1

section
variable {w : Wiring} {N g e : Nat}
  {A : ManufacturedReflector w g e}
  (C : PartialSecondRunSharp.ChangedContact w A)
include w N g e A C

theorem PartialSecondRunSharp.ChangedContact.mem_compressedLead_of_approach
    {j : Nat} (hj : j ≤ C.approach.length) :
    restrictedTonguesAt w N (e, A.activatedState) j ∈
      C.compressedLead N := by
  exact List.mem_append_left _ (A.mem_continuationHistory C.approach_trace C.approach_simple hj)

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
  have hs := C.full_simple
  rw [C.split] at hs
  have hall := A.backward_contact_two_phase C.old_grooves C.oriented_mem C.approach_trace
    (by grind [SwitchSimple, passageSwitch]) (by simpa [hbackward] using C.arrive_eq)
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
    (C : PartialSecondRunSharp.ChangedContact w A)
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
  exact List.mem_append_left _ (List.mem_append_left _ (A.mem_sharpHistoryCore_of_mem
    (A.manufacturing_journey_mem_sharpHistory hA hk)))

/-- Absolute coefficient-one bound for the entire original run once the
first damaging continuation contact points backward. -/
theorem PartialSecondRunSharp.ChangedContact.backward_all_run_distinct_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w A)
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
    (C : PartialSecondRunSharp.ChangedContact w
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
      hApproachForeign, hentryBranch, hentrySwitch,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      _hCandy, hCandyForeignNew, hLobe, hreach⟩ :=
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
      R.suffix_after_runway_passage C.contactState C.old_grooves hrunwaySplit hmouthLink
    have hNewAvoidsD :
        (LocalAction.flip (mouth / 3)).Avoids D.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsDRaw
    exact cover_of_live_phase_orbit
      (phases := [flipAt C.contactState (mouth / 3),
        flipAt (flipAt C.contactState (mouth / 3)) D.actionSwitch,
        C.contactState, flipAt C.contactState D.actionSwitch]) hreach
      (manufactured_flip_arbitrary_lobe_all_time_four_phase D C.contactState hDpaths
        hNewAvoidsD hentryBranch hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hLobe hmouthLink)
      (by simp [hDAction, hentryHistorical, hstateHistorical]) hleadHistorical
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy C.contactState hentryOld hrunway hentryBranch
    exact cover_of_live_phase_orbit
      (phases := [flipAt C.contactState (mouth / 3),
        flipAt (flipAt C.contactState (mouth / 3)) R.actionSwitch]) hreach
      (fun d => by
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using
          manufactured_flip_candy_splice_all_two_phases
            R C.contactState C.old_grooves hrouteSplit hOldTail hrunway hentryBranch
            hold horientation (hfullGrooved (mouth, entry) List.mem_cons_self)
            hApproachReplay hApproachGrooved hApproachForeign hcrossed hmouthLink harms d)
      (by simp [hentryHistorical]) hleadHistorical

/-- The stay-forward branch contributes no vector beyond the contact pre/post
vectors already stored in `compressedLead`. -/
theorem PartialSecondRunSharp.ChangedContact.forward_stay_zero_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w
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
    (C : PartialSecondRunSharp.ChangedContact w A)
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
