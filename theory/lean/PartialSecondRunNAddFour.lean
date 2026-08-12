import PartialSecondRunSharp
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

private theorem terminal_trace_of_dead_local
    {w : Wiring} {start : Nat × Tongues} :
    ∀ {L : Nat}, stepN w L start = none →
      ∃ finish passages,
        passages.length < L ∧
        PhysicalTrace w start passages finish ∧
        step w finish = none := by
  intro L
  induction L with
  | zero =>
      intro hdead
      simp [stepN] at hdead
  | succ n ih =>
      intro hdead
      cases hprev : stepN w n start with
      | none =>
          obtain ⟨finish, passages, hlength, htrace, hfall⟩ := ih hprev
          exact ⟨finish, passages,
            Nat.lt_trans hlength (Nat.lt_succ_self n), htrace, hfall⟩
      | some finish =>
          obtain ⟨passages, hlength, htrace⟩ :=
            physicalTrace_of_stepN w hprev
          refine ⟨finish, passages, ?_, htrace, ?_⟩
          · rw [hlength]
            exact Nat.lt_succ_self n
          · change stepN w (n + 1) start = none at hdead
            rw [stepN_add, hprev] at hdead
            simpa [stepN] using hdead

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
    terminal_trace_of_dead_local hdead
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

/-- Extraction of the first damaging contact with the source continuation
and endpoint retained definitionally.  The older existential interface drops
these two equalities, which are useful when naming the exact cycle residual. -/
private theorem changedContact_of_broken_simple_exact
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    (hbroken : ¬ PathGrooves A.toSupported.paths finish.2) :
    ∃ C : ChangedContact w A,
      C.full = passages ∧ C.finish = finish := by
  obtain ⟨approach, p, x, suffix, u, v, path, old,
      hsplit, happroach, hgrooves, harrive,
      hpath, hold, hswitch, hchanged, _hexit⟩ :=
    htrace.first_changed_support_passage hA hbroken
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    A.changed_contact_on_orientedRoute u v hgrooves hpath hold
      hswitch harrive hchanged
  have hfull := htrace
  rw [hsplit] at hfull
  obtain ⟨middle, hbefore, hafter⟩ := hfull.split_append
  have hmiddle : middle = (p, u) := by
    have hactual := hbefore.sound
    have hgiven := happroach.sound
    rw [hgiven] at hactual
    exact (Option.some.inj hactual).symm
  subst middle
  refine ⟨{
    full := passages
    finish := finish
    approach := approach
    p := p
    x := x
    suffix := suffix
    contactState := u
    nextState := v
    path := path
    old := old
    oriented := oriented
    full_trace := htrace
    full_simple := hsimple
    split := hsplit
    approach_trace := happroach
    suffix_trace := hafter
    old_grooves := hgrooves
    arrive_eq := harrive
    path_mem := hpath
    old_mem := hold
    old_switch := hswitch
    changed := hchanged
    oriented_mem := horiented
    oriented_groove := horientedGroove
    oriented_switch := horientedSwitch
    direction := hdirection
  }, rfl, rfl⟩

/-- Lift a local novelty cover after the first manufacturing journey to the
complete run.  This is the counting interface used below with budgets zero
and one. -/
theorem changedContact_all_run_distinct_le_of_local_novelty
    {w : Wiring} {N g e budget : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup)
    (hlocal : NoveltyCoverOn w N (e, A.activatedState)
      (times.map (fun k => k -
        (A.exploration.length + A.runway.length + 1)))
      (C.history N) budget) :
    times.length ≤ N + 3 + budget := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hlocal' : NoveltyCoverOn w N (e, A.activatedState)
      localTimes (C.history N) budget := by
    simpa [localTimes, firstTravel] using hlocal
  obtain ⟨fresh, hfresh, hlocalMem⟩ := hlocal'
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.history N) budget := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hfirst : k ≤ firstTravel
    · apply List.mem_append_left
      unfold ChangedContact.history
      apply List.mem_append_left
      unfold ManufacturedReflector.continuationHistory
      apply List.mem_append_left
      apply A.mem_sharpHistoryCore_of_mem
      exact A.manufacturing_journey_mem_sharpHistory hA (by
        simpa [firstTravel] using hfirst)
    · let d := k - firstTravel
      have hdMem : d ∈ localTimes := by
        dsimp [d, localTimes]
        exact List.mem_map.mpr ⟨k, hk, rfl⟩
      have hm := hlocalMem d hdMem
      have hshift := restrictedTonguesAt_sub_of_reach
        (N := N) hreach (by omega) (hlive k hk)
      rw [hshift]
      exact hm
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory := C.history_length_le_N_add_three hN hA
  omega

/-- A live tail with a genuine positive period and a witnessed tongue change
inside that period.  Unlike a mere four-corner upper cover, this record keeps
the non-constancy needed to contradict a one-vector settled tail. -/
structure NonconstantPeriodicTail
    (w : Wiring) (start : Nat × Tongues) : Type where
  period : Nat
  period_positive : 0 < period
  period_run : stepN w period start = some start
  phase : Nat
  phasePort : Nat
  phaseState : Tongues
  phase_run : stepN w phase start = some (phasePort, phaseState)
  phase_changes : Not (phaseState = start.2)

private theorem flipAt_ne_self (u : Tongues) (C : Nat) :
    Not (flipAt u C = u) := by
  intro h
  have hbit : !(u C) = u C := by
    simpa [flipAt] using congrFun h C
  cases hvalue : u C <;> simp [hvalue] at hbit

/-- Once a run has reached a tail which is settled at every positive later
time, it cannot also contain a nonconstant periodic orbit.  Multiplying the
period moves both the period base and its changed phase strictly beyond the
settling point. -/
private theorem nonconstantPeriodicTail_false_of_positive_settled
    {w : Wiring} {N : Nat} {start tailStart : Nat × Tongues}
    (C : PartialSecondCycleOutcome w start N)
    {offset : Nat}
    (hreach : stepN w offset tailStart = some C.atRepeat)
    (P : NonconstantPeriodicTail w tailStart) : False := by
  let repeats := offset + 1
  let baseTime := repeats * P.period
  have hperiodOne : 1 <= P.period := P.period_positive
  have hmul := Nat.mul_le_mul_left repeats hperiodOne
  have hbaseAfter : offset < baseTime := by
    dsimp [repeats, baseTime] at hmul ⊢
    simp only [Nat.mul_one] at hmul
    omega
  have hperiodBase : stepN w baseTime tailStart = some tailStart := by
    dsimp [baseTime, repeats]
    exact stepN_mul_period_pair_novelty P.period_run (offset + 1)
  have hsettledAfter : forall t, offset < t ->
      exists port, stepN w t tailStart = some (port, C.settled) := by
    intro t ht
    let d := t - offset
    have hdPositive : 0 < d := by
      dsimp [d]
      omega
    obtain ⟨port, hpositive⟩ := C.positive_settled d hdPositive
    refine ⟨port, ?_⟩
    have hsplit : t = offset + d := by
      dsimp [d]
      omega
    rw [hsplit, stepN_add, hreach]
    exact hpositive
  obtain ⟨basePort, hbaseSettled⟩ :=
    hsettledAfter baseTime hbaseAfter
  have hstartSettled : tailStart.2 = C.settled := by
    rw [hperiodBase] at hbaseSettled
    exact congrArg Prod.snd (Option.some.inj hbaseSettled)
  let phaseTime := baseTime + P.phase
  have hphaseAfter : offset < phaseTime := by
    dsimp [phaseTime]
    omega
  have hphaseRun : stepN w phaseTime tailStart =
      some (P.phasePort, P.phaseState) := by
    dsimp [phaseTime]
    rw [stepN_add, hperiodBase]
    exact P.phase_run
  obtain ⟨settledPort, hphaseSettled⟩ :=
    hsettledAfter phaseTime hphaseAfter
  have hphaseStateSettled : P.phaseState = C.settled := by
    rw [hphaseRun] at hphaseSettled
    exact congrArg Prod.snd (Option.some.inj hphaseSettled)
  exact P.phase_changes (hphaseStateSettled.trans hstartSettled.symm)

/-- In the flip-forward case, a selected candy entry costs only one new
vector.  The runway alternative retains both the exact selected entry and a
positive periodic tail with a witnessed nonconstant phase. -/
theorem changedContact_forward_flip_one_novelty_or_runway
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : ChangedContact w (ManufacturedReflector.flip R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 = (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 = (C.oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N
        (e, (ManufacturedReflector.flip R).activatedState)
        times (C.history N) 1 ∨
      ∃ entry mouth, ∃ tailStart : Nat × Tongues,
        (entry, mouth) ∈
          (ManufacturedReflector.flip R).orientedRoute C.contactState ∧
        (entry, mouth) ∈ R.runway ∧
        stepN w (C.approach.length + 1)
          (e, (ManufacturedReflector.flip R).activatedState) =
            some tailStart ∧
        Nonempty (NonconstantPeriodicTail w tailStart) := by
  have hsimple := C.full_simple
  rw [C.split] at hsimple
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, _tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, _hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete⟩ :=
    partial_forward_contact_active_lead
      (A := ManufacturedReflector.flip R)
      hsimple C.approach_trace C.old_grooves C.arrive_eq C.changed
      C.oriented_mem C.oriented_groove C.oriented_switch
      hforward hrepair hrestored
  let K := C.approach.length + 1
  have hreach' : stepN w K
      (e, (ManufacturedReflector.flip R).activatedState) =
        some (outside, flipAt C.contactState (mouth / 3)) := by
    simpa [K] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate :
      C.nextState = flipAt C.contactState (mouth / 3) := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical : VectorCount.restrict N
      (flipAt C.contactState (mouth / 3)) ∈ C.history N := by
    simpa [hnextAlternate] using C.next_mem_history (N := N)
  have hleadHistorical : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N
        (e, (ManufacturedReflector.flip R).activatedState) j ∈
          C.history N := by
    intro j _hj hjK
    exact C.approach_mem_history (N := N) (by
      dsimp [K] at hjK
      omega)
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨D, _hDAction, _hEntryOldNe, hDpaths,
        hNewAvoidsDRaw, _htravel⟩ :=
      R.suffix_after_runway_passage_with_travel C.contactState hRpaths
        hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove :
          arrive C.contactState entry = (mouth, C.contactState) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch C.contactState entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hNewAvoidsD :
        (LocalAction.flip (mouth / 3)).Avoids D.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsDRaw
    let newState := flipAt C.contactState (mouth / 3)
    have hDNew : PathGrooves D.toSupported.paths newState := by
      dsimp [newState]
      exact hDpaths.after_avoiding_action hNewAvoidsD
    have hphaseRun : stepN w D.toSupported.travel
        (outside, newState) =
          some (mouth, flipAt newState D.actionSwitch) := by
      have hrun := (D.toSupported.run newState hDNew).1
      change stepN w D.toSupported.travel (outside, newState) =
        some (mouth, flipAt newState D.actionSwitch) at hrun
      exact hrun
    have hperiodData : exists period,
        0 < period ∧
        stepN w period (outside, newState) =
          some (outside, newState) := by
      by_cases hcontact : exists passage,
          And (passage ∈ candy)
            (passageSwitch passage = D.actionSwitch)
      · obtain ⟨period, hpositive, hperiod, _hwindow⟩ :=
          manufactured_flip_arbitrary_lobe_four_phase_period
            D C.contactState hDpaths hNewAvoidsD hentryBranch
            hentrySwitch hfullGrooved hfullTrace hcrossed
            hCandyForeign hLobe hmouthLink hcontact
        exact ⟨period, hpositive, by simpa [newState] using hperiod⟩
      · have hCandyForeignOld : forall passage,
            passage ∈ candy ->
            passageSwitch passage ≠ D.actionSwitch := by
          intro passage hp hEq
          exact hcontact ⟨passage, hp, hEq⟩
        let L : SupportedReflector w mouth outside := {
          travel := candy.length + 2
          paths := [candy]
          action := .flip (mouth / 3)
          run := by
            intro current hpaths
            have hCandyCurrent : PassagesGrooved current candy :=
              hpaths candy (by simp)
            obtain ⟨hstep, hnext⟩ := hLobe current hCandyCurrent
            constructor
            · exact hstep
            · intro path hp
              simp only [List.mem_singleton] at hp
              subst path
              exact hnext
        }
        have hOldAvoidsL : D.toSupported.action.Avoids L.paths := by
          change (LocalAction.flip D.actionSwitch).Avoids [candy]
          intro path hp passage hpassage
          simp only [List.mem_singleton] at hp
          subst path
          exact hCandyForeignOld passage hpassage
        have hCandy : PassagesGrooved C.contactState candy := by
          intro passage hp
          exact hfullGrooved passage (List.mem_cons_of_mem _ hp)
        have hCandyNew : PassagesGrooved newState candy := by
          dsimp [newState]
          exact grooved_after_flip_other hCandy hCandyForeign
        have hLNew : PathGrooves L.paths newState := by
          intro path hp
          simp only [L, List.mem_singleton] at hp
          subst path
          exact hCandyNew
        let period := 2 * (D.toSupported.travel + L.travel)
        have hpositive : 0 < period := by
          have hDpos := (ManufacturedReflector.flip D).travel_pos
          dsimp [period, L]
          omega
        have hperiod : stepN w period (outside, newState) =
            some (outside, newState) := by
          dsimp [period]
          exact D.toSupported.paired_period L hOldAvoidsL hNewAvoidsD
            newState hDNew hLNew
        exact ⟨period, hpositive, hperiod⟩
    obtain ⟨period, hpositive, hperiod⟩ := hperiodData
    refine Or.inr ⟨entry, mouth, (outside, newState),
      hentryOld, hrunway, ?_, ?_⟩
    · simpa [K, newState] using hreach'
    · exact ⟨{
        period := period
        period_positive := hpositive
        period_run := hperiod
        phase := D.toSupported.travel
        phasePort := mouth
        phaseState := flipAt newState D.actionSwitch
        phase_run := hphaseRun
        phase_changes := flipAt_ne_self newState D.actionSwitch
      }⟩
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy
        C.contactState hentryOld hrunway hentryBranch
    have hentryGrooved :
        arrive C.contactState entry = (mouth, C.contactState) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    left
    exact manufactured_flip_candy_splice_absolute_one_novelty
      R C.contactState hRpaths hrouteSplit hOldTail hrunway
      hentryBranch hold horientation hentryGrooved hApproachReplay
      hApproachGrooved hApproachForeign hcrossed hmouthLink harms
      hreach' N (C.history N) hentryHistorical times hleadHistorical

/-- The sole residual left by the present `N+4` cycle count: the canonical
first damaging passage is forward into a flip reflector and the selected old
entry belongs to that reflector's runway. -/
structure PartialSecondCycleRunwayResidual
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (C : PartialSecondCycleOutcome w (e, A.activatedState) N) : Type where
  contact : ChangedContact w A
  full_eq : contact.full = C.lead
  finish_eq : contact.finish = C.atRepeat
  reflector : ManufacturedFlipReflector w g e
  reflector_eq : A = ManufacturedReflector.flip reflector
  repaired : Tongues
  forward : contact.x = contact.oriented.2
  repair : arrive contact.nextState contact.oriented.1 =
    (contact.oriented.2, repaired)
  restored : arrive repaired contact.oriented.2 =
    (contact.oriented.1, repaired)
  entry : Nat
  mouth : Nat
  selected : (entry, mouth) ∈
    (ManufacturedReflector.flip reflector).orientedRoute
      contact.contactState
  runway : (entry, mouth) ∈ reflector.runway
  tailStart : Nat × Tongues
  post_reach : stepN w (contact.approach.length + 1)
      (e, A.activatedState) =
        some tailStart
  nonconstant : NonconstantPeriodicTail w tailStart

/-- **Partial second cycle, `N+4` reduction.**  Every retained one-vector
cycle has at most `N+4` distinct vectors unless its canonical first damaging
contact is the exact flip-runway residual above.  Backward and stay contacts
cost zero novelty; flip-candy contacts cost one. -/
theorem PartialSecondCycleOutcome.all_run_distinct_le_N_add_four_or_runway
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (C : PartialSecondCycleOutcome w (e, A.activatedState) N)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 4 ∨
      Nonempty (PartialSecondCycleRunwayResidual A C) := by
  by_cases hend : PathGrooves A.toSupported.paths C.atRepeat.2
  · left
    have hthree := simple_lead_one_vector_tail_distinct_le_N_add_three
      hN A hA C.lead_trace C.lead_simple hend C.positive_settled
      times hlive hnd
    omega
  · obtain ⟨D, hfull, hfinish⟩ :=
      changedContact_of_broken_simple_exact
        A hA C.lead_trace C.lead_simple hend
    rcases D.direction with hbackward |
        ⟨hforward, repaired, hrepair, hrestored⟩
    · left
      have hlocal := D.backward_all_time_zero_novelty
        (N := N) hbackward
        (times.map (fun k => k -
          (A.exploration.length + A.runway.length + 1)))
      have hbound := changedContact_all_run_distinct_le_of_local_novelty
        hN D hA times hlive hnd hlocal
      omega
    · cases A with
      | stay R =>
          left
          have hlocal := D.forward_stay_all_time_zero_novelty
            (N := N) hforward hrepair hrestored
            (times.map (fun k => k -
              ((ManufacturedReflector.stay R).exploration.length +
                (ManufacturedReflector.stay R).runway.length + 1)))
          have hbound := changedContact_all_run_distinct_le_of_local_novelty
            hN D hA times hlive hnd hlocal
          omega
      | flip R =>
          rcases changedContact_forward_flip_one_novelty_or_runway
              D hforward hrepair hrestored
              (times.map (fun k => k -
                ((ManufacturedReflector.flip R).exploration.length +
                  (ManufacturedReflector.flip R).runway.length + 1))) with
            hone | hrunway
          · left
            have hbound := changedContact_all_run_distinct_le_of_local_novelty
              hN D hA times hlive hnd hone
            omega
          · right
            obtain ⟨entry, mouth, tailStart, hselected, hentryRunway,
              hpostReach, ⟨hnonconstant⟩⟩ := hrunway
            exact ⟨{
              contact := D
              full_eq := hfull
              finish_eq := hfinish
              reflector := R
              reflector_eq := rfl
              repaired := repaired
              forward := hforward
              repair := hrepair
              restored := hrestored
              entry := entry
              mouth := mouth
              selected := hselected
              runway := hentryRunway
              tailStart := tailStart
              post_reach := hpostReach
              nonconstant := hnonconstant
            }⟩

/-- **Stable partial second cycle, sharp form.**  The flip-runway alternative
above cannot occur on the retained one-vector cycle.  Its post-contact tail
has a positive period with a genuinely changed phase; after the tail reaches
`atRepeat`, `positive_settled` says that both sufficiently late phases have
the same settled tongue vector.  Determinism therefore contradicts the
witnessed change. -/
theorem PartialSecondCycleOutcome.all_run_distinct_le_N_add_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (C : PartialSecondCycleOutcome w (e, A.activatedState) N)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 4 := by
  rcases
      _root_.GeneralN.PartialSecondRunNAddFour.PartialSecondCycleOutcome.all_run_distinct_le_N_add_four_or_runway
        hN A hA C times hlive hnd with hsmall | hresidual
  · exact hsmall
  · obtain ⟨F⟩ := hresidual
    have hlength : F.contact.full.length =
        (F.contact.approach.length + 1) + F.contact.suffix.length := by
      rw [F.contact.split]
      simp only [List.length_append, List.length_cons]
      omega
    have hfullRun := F.contact.full_trace.sound
    rw [hlength, stepN_add, F.post_reach] at hfullRun
    have htailReach : stepN w F.contact.suffix.length F.tailStart =
        some C.atRepeat := by
      rw [F.finish_eq] at hfullRun
      exact hfullRun
    exact (nonconstantPeriodicTail_false_of_positive_settled
      C htailReach F.nonconstant).elim

end PartialSecondRunNAddFour

end GeneralN
