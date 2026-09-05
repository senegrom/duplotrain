import BoundaryNAddFourSaturation
import PartialSecondRunSharp

/-!
# Coefficient-one top-level assembly

This file is deliberately separate from the shared construction files.  It
contains the final assembly work and, until the last two branches are closed,
states those branches explicitly rather than hiding them behind an assumed
result.

The first bridge below is useful independently: after one manufactured
reflector, any switch-simple continuation which leaves that reflector's
support grooved can be charged together with the first construction in a
single `N`-coordinate budget.
-/

namespace GeneralN

/-- The second run falls before the second sharp first-revisit horizon. -/
structure OneReflectorSecondDead
    (w : Wiring) (N e : Nat) (start : Nat × Tongues) : Type where
  A : ManufacturedReflector w start.1 e
  grooves : PathGrooves A.toSupported.paths A.activatedState
  base : A.baseState = start.2
  dead : stepN w (N + 1) (e, A.activatedState) = none


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
    VectorCount.restrict N C.nextState ∈ C.compressedLead N := by
  apply List.mem_append_right
  apply List.mem_append_right
  simp

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
    backward_contact_all_time_two_phase_two_history
      hrecorded hrecordedNext A.entryEdge hcontact
      happroachReplay happroachNext
  let K := C.approach.length
  have hreach :
      stepN w K (e, A.activatedState) =
        some (C.p, C.contactState) := by
    simpa [K] using C.approach_trace.sound
  refine ⟨[], by simp, ?_⟩
  intro j _hj
  simp only [List.append_nil]
  by_cases hjK : j < K
  · exact C.mem_compressedLead_of_approach (N := N) (by
      dsimp [K] at hjK
      omega)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hall d
    have hglobal :
        stepN w j (e, A.activatedState) = some (port, phase) := by
      rw [hjEq, stepN_add, hreach]
      exact hrun
    have hvector :
        restrictedTonguesAt w N (e, A.activatedState) j =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [h] using C.contact_mem_compressedLead (N := N)
    · simpa [h] using C.next_mem_compressedLead (N := N)

end

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
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  obtain ⟨fresh, hfresh, hlocal⟩ :=
    C.backward_all_time_zero_novelty
      (N := N) hbackward localTimes
  have hfreshNil : fresh = [] := by
    cases fresh with
    | nil => rfl
    | cons head tail => simp at hfresh
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.compressedLead N) 0 := by
    refine ⟨[], by simp, ?_⟩
    intro k hk
    simp only [List.append_nil]
    by_cases hfirst : k ≤ firstTravel
    · apply List.mem_append_left
      apply A.mem_sharpHistoryCore_of_mem
      exact A.manufacturing_journey_mem_sharpHistory hA (by
        simpa [firstTravel] using hfirst)
    · let d := k - firstTravel
      have hdMem : d ∈ localTimes := by
        dsimp [d, localTimes]
        exact List.mem_map.mpr ⟨k, hk, rfl⟩
      have hm := hlocal d hdMem
      rw [hfreshNil, List.append_nil] at hm
      have hshift := restrictedTonguesAt_sub_of_reach
        (N := N) hreach (by omega) (hlive k hk)
      rw [hshift]
      exact hm
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength := C.compressedLead_length_le hN hA
  omega

/-- A physical prefix of the doomed second run cannot repeat a switch.
The cycle alternative is non-falling.  The reflector alternative completes
an opposite pair, whose protected-repair theorem is also non-falling. -/
theorem OneReflectorSecondDead.trace_simple
    {w : Wiring} {N e : Nat} {start : Nat × Tongues}
    (D : OneReflectorSecondDead w N e start)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, D.A.activatedState) passages finish) :
    SwitchSimple passages := by
  apply Classical.byContradiction
  intro hnonsimple
  have hentry : w.link start.1 = some e :=
    w.symm _ _ D.A.entryEdge
  obtain ⟨atRepeat, visited, hvisited, hcycle | hreflector⟩ :=
    htrace.first_revisit_trace_or_activated_reflector
      hnonsimple hentry
  · obtain ⟨cycle, settled, hnonempty, htransient,
        hstable⟩ := hcycle
    have hpositive : 0 < cycle.length := by
      cases cycle with
      | nil => exact (hnonempty rfl).elim
      | cons _ _ => simp
    have hsettles : SettlesOnSimpleCycle w atRepeat :=
      ⟨cycle.length, settled, hpositive,
        htransient.sound, hstable.sound⟩
    have hperiodic : EventuallyPeriodic w
        (e, D.A.activatedState) :=
      eventuallyPeriodic_of_reaches_simple_cycle hvisited hsettles
    obtain ⟨later, hlater⟩ :=
      hperiodic.stepN_some_all (N + 1)
    rw [D.dead] at hlater
    cases hlater
  · obtain ⟨B, state, backSteps, hB, hbase,
        hactivated, hback⟩ := hreflector
    subst state
    have hAatBase :
        PathGrooves D.A.toSupported.paths B.baseState := by
      rw [hbase]
      exact D.grooves
    have htail : EventuallyPeriodic w
        (start.1, B.activatedState) :=
      manufactured_pair_protected_repair_eventuallyPeriodic
        D.A B hAatBase hB
    have hreachPair : stepN w (visited + backSteps)
        (e, D.A.activatedState) =
          some (start.1, B.activatedState) := by
      rw [stepN_add, hvisited]
      exact hback
    have hperiodic : EventuallyPeriodic w
        (e, D.A.activatedState) :=
      EventuallyPeriodic.prepend hreachPair htail
    obtain ⟨later, hlater⟩ :=
      hperiodic.stepN_some_all (N + 1)
    rw [D.dead] at hlater
    cases hlater

/-- The one exact forward-contact certificate shared by both unfinished
second-run outcomes.  No completed second reflector is assumed. -/
structure OneReflectorForwardContact
    (w : Wiring) (N e : Nat) (start : Nat × Tongues) : Type where
  A : ManufacturedReflector w start.1 e
  grooves : PathGrooves A.toSupported.paths A.activatedState
  base : A.baseState = start.2
  contact : SimpleContinuationChangedContact w A

/-- The early-death branch is coefficient one unless its terminal simple
trace contains the same exact forward self-repairing contact.  Preserved
support costs `N+2`; a backward first damage costs `N+3`. -/
theorem OneReflectorSecondDead.N_add_three_or_forward
    {w : Wiring} {N e : Nat} {start : Nat × Tongues}
    (D : OneReflectorSecondDead w N e start)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 3 ∨
      Nonempty (OneReflectorForwardContact w N e start) := by
  obtain ⟨finish, passages, htrace, hfall⟩ :=
    PartialSecondRunSharp.terminal_trace_of_dead D.dead
  have hsimple : SwitchSimple passages := D.trace_simple htrace
  have hliveA : ∀ k ∈ times,
      (stepN w k (start.1, D.A.baseState)).isSome := by
    simpa [D.base] using hlive
  have hndA : (times.map
      (restrictedTonguesAt w N
        (start.1, D.A.baseState))).Nodup := by
    simpa [D.base] using hnd
  by_cases hend : PathGrooves D.A.toSupported.paths finish.2
  · left
    have htwo := preserved_simple_fall_distinct_le_N_add_two
      hN D.A D.grooves htrace hsimple hend hfall
        times hliveA hndA
    omega
  · obtain ⟨C⟩ :=
      PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple
        D.A D.grooves htrace hsimple hend
    rcases C.direction with hbackward |
        ⟨_hforward, _repaired, _hrepair, _hrestored⟩
    · left
      exact C.backward_all_run_distinct_le_N_add_three
        hN D.grooves hbackward times hliveA hndA
    · right
      exact ⟨{
        A := D.A
        grooves := D.grooves
        base := D.base
        contact := C
      }⟩


/-- A forward first-changing contact into a flip reflector has at most two
new restricted vectors after the coefficient-one contact history.  This is
the partial-continuation analogue of the completed-second-reflector theorem.
-/
theorem PartialSecondRunSharp.ChangedContact.forward_flip_two_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair : arrive C.nextState C.oriented.1 =
      (C.oriented.2, repaired))
    (hrestored : arrive repaired C.oriented.2 =
      (C.oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N
      (e, (ManufacturedReflector.flip R).activatedState)
      times (C.compressedLead N) 2 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachGrooved,
      hApproachForeign, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach⟩ :=
    partial_first_forward_contact_active_lead
      (A := ManufacturedReflector.flip R) C.split C.full_simple
      C.approach_trace C.old_grooves C.arrive_eq C.changed
      C.oriented_mem C.oriented_groove C.oriented_switch
      hforward hrepair hrestored
  let K := C.approach.length + 1
  let state := C.contactState
  let alternate := flipAt state (mouth / 3)
  have hreach' :
      stepN w K
        (e, (ManufacturedReflector.flip R).activatedState) =
        some (outside, alternate) := by
    simpa [K, state, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.compressedLead N := by
    simpa [hnextAlternate] using C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N state ∈ C.compressedLead N := by
    simpa [state] using C.contact_mem_compressedLead (N := N)
  have hleadHistorical : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N
        (e, (ManufacturedReflector.flip R).activatedState) j ∈
          C.compressedLead N := by
    intro j _hj hjK
    exact C.mem_compressedLead_of_approach (N := N) (by
      dsimp [K] at hjK
      omega)
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ := List.append_of_mem hrunway
    obtain ⟨D, _hDAction, hEntryOldNe, hDpaths,
        hNewAvoidsDRaw⟩ :=
      R.suffix_after_runway_passage state hRpaths
        hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch state entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe : mouth / 3 ≠ D.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsD :
        (LocalAction.flip (mouth / 3)).Avoids D.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsDRaw
    by_cases hcontact : ∃ passage ∈ candy,
        passageSwitch passage = D.actionSwitch
    · apply manufactured_flip_arbitrary_lobe_absolute_two_novelty
        D state hDpaths hNewAvoidsD hentryBranch hentrySwitch
        hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
        hmouthLink hcontact hreach' times (C.compressedLead N)
        hentryHistorical hstateHistorical
      exact hleadHistorical
    · have hCandyForeignOld : ∀ passage ∈ candy,
          passageSwitch passage ≠ D.actionSwitch := by
        intro passage hp hEq
        exact hcontact ⟨passage, hp, hEq⟩
      apply manufactured_suffix_explicit_lobe_absolute_two_novelty
        D state hDpaths hNewAvoidsD hActionsNe hentryBranch
        hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hCandyForeignOld hLobe hmouthLink
        hreach' times (C.compressedLead N) hentryHistorical
        hstateHistorical
      exact hleadHistorical
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        hentryOld hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved hApproachReplay
      hApproachGrooved hApproachForeign hcrossed hmouthLink harms
      hreach' N (C.compressedLead N) hentryHistorical times
      hleadHistorical
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

/-- The stay-forward branch contributes no vector beyond the contact pre/post
vectors already stored in `compressedLead`. -/
theorem PartialSecondRunSharp.ChangedContact.forward_stay_zero_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.stay R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair : arrive C.nextState C.oriented.1 =
      (C.oriented.2, repaired))
    (hrestored : arrive repaired C.oriented.2 =
      (C.oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N
      (e, (ManufacturedReflector.stay R).activatedState)
      times (C.compressedLead N) 0 := by
  obtain ⟨outside, mouth, hreach, hall⟩ :=
    C.forward_stay_two_phase_tail hforward hrepair hrestored
  let K := C.approach.length + 1
  let alternate := flipAt C.contactState (mouth / 3)
  have hreach' : stepN w K
      (e, (ManufacturedReflector.stay R).activatedState) =
        some (outside, alternate) := by
    simpa [K, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.compressedLead N := by
    simpa [hnextAlternate] using C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N C.contactState ∈ C.compressedLead N :=
    C.contact_mem_compressedLead
  refine ⟨[], by simp, ?_⟩
  intro j _hj
  simp only [List.append_nil]
  by_cases hjK : j < K
  · exact C.mem_compressedLead_of_approach (N := N) (by
      dsimp [K] at hjK
      omega)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hall d
    have hglobal : stepN w j
        (e, (ManufacturedReflector.stay R).activatedState) =
          some (port, phase) := by
      rw [hjEq, stepN_add, hreach']
      exact hrun
    have hvector : restrictedTonguesAt w N
        (e, (ManufacturedReflector.stay R).activatedState) j =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [alternate, h] using hentryHistorical
    · simpa [h] using hstateHistorical

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
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · obtain ⟨fresh, hfresh, hmem⟩ :=
      C.backward_all_time_zero_novelty
        (N := N) hbackward times
    exact ⟨fresh, by omega, hmem⟩
  · cases A with
    | stay R =>
        obtain ⟨fresh, hfresh, hmem⟩ :=
          C.forward_stay_zero_novelty
            hforward hrepair hrestored times
        exact ⟨fresh, by omega, hmem⟩
    | flip R =>
        exact C.forward_flip_two_novelty
          hforward hrepair hrestored times

end GeneralN
