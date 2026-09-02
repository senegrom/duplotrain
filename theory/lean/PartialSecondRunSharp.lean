import OneReflectorContinuation
import TraceRetainingFirstRevisit

/-!
# Sharp partial second-run accounting

After one completed manufactured reflector, the second `N+1`-step probe has
three outcomes: death, a tongue-stable simple-cycle capture, or a second
manufactured reflector.  The last case is already bounded by
`ManufacturedReflector.two_reflector_all_run_distinct_le_N_add_six`.

This file treats the other two outcomes without adding the first reflector's
`N+2` history to a fresh `N+2` history.  All continuation writers are charged
against the same ambient switch list as the first reflector's reusable
support; only the genuinely dynamical cycle/contact corners are paid as a
constant.
-/


/-!
## Eventual periodicity supplies raw prefixes of every length

Extracted from the removed Mellit support-interaction module: the one
liveness fact its downstream consumers actually kept using.
-/

namespace GeneralN

/-- Eventual periodicity supplies successful raw prefixes of every length. -/
theorem EventuallyPeriodic.stepN_some_all
    {w : Wiring} {start : Nat × Tongues}
    (H : EventuallyPeriodic w start) (d : Nat) :
    ∃ finish, stepN w d start = some finish := by
  obtain ⟨lead, period, settled, hpositive, hsettled, hperiod⟩ := H
  have hcycles :
      stepN w ((d + 1) * period) settled = some settled :=
    stepN_mul_period_pair_novelty hperiod (d + 1)
  have hfar :
      stepN w (lead + (d + 1) * period) start = some settled := by
    rw [stepN_add, hsettled]
    exact hcycles
  have hone : 1 ≤ period := by omega
  have hmul := Nat.mul_le_mul_left (d + 1) hone
  simp only [Nat.mul_one] at hmul
  have hbound : d ≤ lead + (d + 1) * period := by omega
  exact stepN_prefix_some hbound hfar


/-- Trace-retaining form of the simple-cycle branch of
`first_activated_count_outcome_sharp`. -/
structure PartialSecondCycleOutcome
    (w : Wiring) (start : Nat × Tongues) (N : Nat) : Type where
  lead : List Passage
  atRepeat : Nat × Tongues
  settled : Tongues
  lead_trace : PhysicalTrace w start lead atRepeat
  lead_simple : SwitchSimple lead
  positive_settled : ∀ d, 0 < d → ∃ port,
    stepN w d atRepeat = some (port, settled)

/-- The sharp first-activation fork with its physical cycle witness retained.
The reflector alternative is definitionally the same payload as the existing
count-only theorem. -/
theorem first_activated_trace_outcome_sharp_partial
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    Nonempty (PartialSecondCycleOutcome w start N) ∨
      ∃ (A : ManufacturedReflector w start.1 e) (state : Tongues),
        PathGrooves A.toSupported.paths state ∧
        A.baseState = start.2 ∧
        state = A.activatedState := by
  obtain ⟨before, old, repeated, after, middle,
      hbeforeTrace, hafterTrace, hbeforeSimple, hold, hsameSwitch⟩ :=
    first_revisit_of_long_run hN hlive
  obtain ⟨runway, path, hsplit⟩ := List.append_of_mem hold
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  subst before
  obtain ⟨atOld, hrunway, hexcursion⟩ := hbeforeTrace.split_append
  have hatOldPort : atOld.1 = p := hexcursion.head_arrive.1
  rcases atOld with ⟨oldPort, u₀⟩
  simp only at hatOldPort
  subst oldPort
  obtain ⟨v, hrepeat⟩ := hafterTrace.head_arrive.2
  have hmiddlePort : middle.1 = q := hafterTrace.head_arrive.1
  rcases middle with ⟨middlePort, u⟩
  simp only at hmiddlePort
  subst middlePort
  have hsw : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  have hfork := first_revisit_cycle_traces_or_activated_reflector w
    hrunway hexcursion hbeforeSimple hsw hrepeat hentry
  have hleadTrace : PhysicalTrace w start
      (runway ++ (p, x) :: path) (q, u) := hbeforeTrace
  rcases hfork with hcycle | hreflector
  · obtain ⟨_cycle, settled, _hne, _ht, _hs,
      _hsimple, _hphase, hpositive⟩ := hcycle
    exact Or.inl ⟨{
      lead := runway ++ (p, x) :: path
      atRepeat := (q, u)
      settled := settled
      lead_trace := hleadTrace
      lead_simple := hbeforeSimple
      positive_settled := hpositive
    }⟩
  · obtain ⟨A, state, hgrooves, hbase, hactivated,
      _hback, _hpreserves⟩ := hreflector
    exact Or.inr ⟨A, state, hgrooves, hbase, hactivated⟩

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
  direction :
    x = oriented.1 ∨
      (x = oriented.2 ∧
        ∃ repaired,
          arrive nextState oriented.1 = (oriented.2, repaired) ∧
          arrive repaired oriented.2 = (oriented.1, repaired))

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

/-- Coefficient-one history through the contact, including the one changed
post-contact vector. -/
def ChangedContact.history
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A) (N : Nat) : List (List Bool) :=
  A.continuationHistory N (e, A.activatedState) C.approach.length ++
    [VectorCount.restrict N C.nextState]

theorem ChangedContact.history_length_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState) :
    (C.history N).length ≤ N + 3 := by
  have hlead := A.continuationHistory_length_le
    hN (start := (e, A.activatedState))
      (finish := (C.p, C.contactState))
      (passages := C.approach) rfl C.approach_trace
      C.approach_simple hA C.old_grooves
  simp [ChangedContact.history]
  omega

theorem ChangedContact.approach_mem_history
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A)
    {d : Nat} (hd : d ≤ C.approach.length) :
    restrictedTonguesAt w N (e, A.activatedState) d ∈ C.history N := by
  apply List.mem_append_left
  exact A.mem_continuationHistory C.approach_trace
    C.approach_simple hd

theorem ChangedContact.contact_mem_history
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A) :
    VectorCount.restrict N C.contactState ∈ C.history N := by
  have hm := C.approach_mem_history
    (N := N) (d := C.approach.length) (Nat.le_refl _)
  simpa [restrictedTonguesAt, tonguesAt,
    C.approach_trace.sound] using hm

theorem ChangedContact.next_mem_history
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A) :
    VectorCount.restrict N C.nextState ∈ C.history N := by grind [PartialSecondRunSharp.ChangedContact.history, VectorCount.restrict]

/-- Exact two-phase tail after a changed forward contact with a stay
reflector, generalized to an arbitrary switch-simple partial route. -/
theorem ChangedContact.forward_stay_two_phase_tail
    {w : Wiring} {g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : ChangedContact w (ManufacturedReflector.stay R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 = (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 = (C.oriented.1, repaired)) :
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
      hApproachForeign, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach⟩ :=
    partial_first_forward_contact_active_lead
      (A := ManufacturedReflector.stay R)
      C.split C.full_simple C.approach_trace C.old_grooves
      C.arrive_eq C.changed C.oriented_mem C.oriented_groove
      C.oriented_switch hforward hrepair hrestored
  let k := mouth / 3
  let alternate := flipAt C.contactState k
  have hCandyFlip : PassagesGrooved alternate candy := by
    dsimp [alternate, k]
    exact grooved_after_flip_other hCandy hCandyForeign
  have hOldRoute :=
    (ManufacturedReflector.stay R).orientedRoute_trace
      C.contactState hRpaths
  have hOldSimple :=
    (ManufacturedReflector.stay R).orientedRoute_simple C.contactState
  have hOldGrooved := hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward : arrive C.contactState entry =
      (mouth, C.contactState) :=
    groove_forward (hOldGrooved (entry, mouth) hentryOld)
  have hentryMouthSwitch : entry / 3 = mouth / 3 := by
    have hswitch := arrive_exit_switch C.contactState entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  have hallAfter : ∀ d, ∃ port phase,
      stepN w d (outside, alternate) = some (port, phase) ∧
      (phase = alternate ∨ phase = C.contactState) := by
    change (entry, mouth) ∈ R.runway ++ [(R.mouth, R.arm)] at hentryOld
    rcases List.mem_append.mp hentryOld with hrunway | hcore
    · obtain ⟨before, after, hsplit⟩ := List.append_of_mem hrunway
      obtain ⟨D, hDpaths, hAvoid⟩ :=
        R.suffix_after_runway_passage
          C.contactState hRpaths hsplit hmouthLink
      have hAvoid' :
          (LocalAction.flip k).Avoids D.toSupported.paths := by
        dsimp [k]
        simpa [hentryMouthSwitch] using hAvoid
      have hDalt : PathGrooves D.toSupported.paths alternate := by
        dsimp [alternate]
        exact hDpaths.after_avoiding_action hAvoid'
      let dTravel := D.toSupported.travel
      let lTravel := candy.length + 2
      have hDaltEnd : stepN w dTravel (outside, alternate) =
          some (mouth, alternate) := by
        dsimp [dTravel]
        exact (D.toSupported.run alternate hDalt).1
      have hDstateEnd : stepN w dTravel (outside, C.contactState) =
          some (mouth, C.contactState) := by
        dsimp [dTravel]
        exact (D.toSupported.run C.contactState hDpaths).1
      have hDaltPhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          D.travel_state_stepN alternate hDalt (by
            simpa [dTravel, ManufacturedReflector.toSupported,
              ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, alternate, hrun, Or.inl rfl⟩
      have hDstatePhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (outside, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          D.travel_state_stepN C.contactState hDpaths (by
            simpa [dTravel, ManufacturedReflector.toSupported,
              ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, C.contactState, hrun, Or.inr rfl⟩
      have hReverseEnd : stepN w lTravel (mouth, alternate) =
          some (outside, C.contactState) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (mouth, alternate) =
          some (outside, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd : stepN w lTravel (mouth, C.contactState) =
          some (outside, alternate) := by
        have h := (hLobe C.contactState hCandy).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase
            hfullGrooved hfullTrace hcrossed hmouthLink
            (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let half := dTravel + lTravel
      have hHalfAlt : stepN w half (outside, alternate) =
          some (outside, C.contactState) := by
        dsimp [half]
        rw [stepN_add, hDaltEnd]
        exact hReverseEnd
      have hHalfState : stepN w half (outside, C.contactState) =
          some (outside, alternate) := by
        dsimp [half]
        rw [stepN_add, hDstateEnd]
        exact hForwardEnd
      have hHalfAltPhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact GeneralN.stay_twoPhase_concat
          hDaltEnd hDaltPhase hReversePhase d
          (by simpa [half] using hd)
      have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact GeneralN.stay_twoPhase_concat
          hDstateEnd hDstatePhase hForwardPhase d
          (by simpa [half] using hd)
      let period := half + half
      have hperiod : stepN w period (outside, alternate) =
          some (outside, alternate) := by
        dsimp [period]
        rw [stepN_add, hHalfAlt]
        exact hHalfState
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact GeneralN.stay_twoPhase_concat
          hHalfAlt hHalfAltPhase hHalfStatePhase d
          (by simpa [period] using hd)
      have hpositive : 0 < period := by
        dsimp [period, half, dTravel, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow
    · simp only [List.mem_singleton] at hcore
      have hentryEq : entry = R.mouth := congrArg Prod.fst hcore
      have hmouthEq : mouth = R.arm := congrArg Prod.snd hcore
      subst entry
      subst mouth
      have houtsideEq : outside = R.arm := by
        rw [R.selfLink] at hmouthLink
        exact (Option.some.inj hmouthLink).symm
      subst outside
      let lTravel := candy.length + 2
      have hReverseEnd : stepN w lTravel (R.arm, alternate) =
          some (R.arm, C.contactState) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (R.arm, alternate) =
          some (R.arm, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd : stepN w lTravel (R.arm, C.contactState) =
          some (R.arm, alternate) := by
        have h := (hLobe C.contactState hCandy).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase
            hfullGrooved hfullTrace hcrossed hmouthLink
            (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let period := lTravel + lTravel
      have hperiod : stepN w period (R.arm, alternate) =
          some (R.arm, alternate) := by
        dsimp [period]
        rw [stepN_add, hReverseEnd]
        exact hForwardEnd
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (R.arm, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact GeneralN.stay_twoPhase_concat
          hReverseEnd hReversePhase hForwardPhase d
          (by simpa [period] using hd)
      have hpositive : 0 < period := by
        dsimp [period, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow
  refine ⟨outside, mouth, ?_, ?_⟩
  · simpa [alternate, k] using hreach
  · simpa [alternate] using hallAfter

/-- Both all-time phases in the stay-forward case are already the contact
pre-vector and the explicitly stored post-vector. -/
theorem ChangedContact.forward_stay_all_time_zero_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : ChangedContact w (ManufacturedReflector.stay R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 = (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 = (C.oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N (e, (ManufacturedReflector.stay R).activatedState)
      times (C.history N) 0 := by
  obtain ⟨outside, mouth, hreach, hall⟩ :=
    C.forward_stay_two_phase_tail hforward hrepair hrestored
  let K := C.approach.length + 1
  let alternate := flipAt C.contactState (mouth / 3)
  have hreach' :
      stepN w K (e, (ManufacturedReflector.stay R).activatedState) =
        some (outside, alternate) := by
    simpa [K, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.history N := by
    simpa [hnextAlternate] using C.next_mem_history (N := N)
  have hstateHistorical :
      VectorCount.restrict N C.contactState ∈ C.history N :=
    C.contact_mem_history
  refine ⟨[], by simp, ?_⟩
  intro j _hj
  simp only [List.append_nil]
  by_cases hjK : j < K
  · exact C.approach_mem_history (N := N) (by
      dsimp [K] at hjK
      omega)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hall d
    have hglobal :
        stepN w j (e, (ManufacturedReflector.stay R).activatedState) =
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

/-- Every finite dead run has a literal final live physical trace. -/
theorem terminal_trace_of_dead
    {w : Wiring} {start : Nat × Tongues} :
    ∀ {L : Nat}, stepN w L start = none →
      ∃ finish passages,
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
      | none => exact ih hprev
      | some finish =>
          obtain ⟨passages, _hlength, htrace⟩ :=
            physicalTrace_of_stepN w hprev
          refine ⟨finish, passages, htrace, ?_⟩
          change stepN w (n + 1) start = none at hdead
          rw [stepN_add, hprev] at hdead
          simpa [stepN] using hdead

/-- A doomed continuation after a completed reflector cannot repeat a
switch: either first-revisit outcome would make the run live forever. -/
theorem ManufacturedReflector.dead_continuation_trace_simple
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hdead : stepN w (N + 1) (e, A.activatedState) = none)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish) :
    SwitchSimple passages := by
  apply Classical.byContradiction
  intro hnonsimple
  have hentry : w.link g = some e := w.symm _ _ A.entryEdge
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
    have hperiodic : EventuallyPeriodic w (e, A.activatedState) :=
      eventuallyPeriodic_of_reaches_simple_cycle hvisited hsettles
    obtain ⟨later, hlater⟩ := hperiodic.stepN_some_all (N + 1)
    rw [hdead] at hlater
    cases hlater
  · obtain ⟨B, state, backSteps, hB, hbase,
        hactivated, hback⟩ := hreflector
    subst state
    have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
      rw [hbase]
      exact hA
    have htail : EventuallyPeriodic w (g, B.activatedState) :=
      manufactured_pair_protected_repair_eventuallyPeriodic
        A B hAatBase hB
    have hreachPair : stepN w (visited + backSteps)
        (e, A.activatedState) = some (g, B.activatedState) := by
      rw [stepN_add, hvisited]
      exact hback
    have hperiodic : EventuallyPeriodic w (e, A.activatedState) :=
      EventuallyPeriodic.prepend hreachPair htail
    obtain ⟨later, hlater⟩ := hperiodic.stepN_some_all (N + 1)
    rw [hdead] at hlater
    cases hlater

end PartialSecondRunSharp
end GeneralN
