import EventuallyPeriodicPrefixes
import JourneyReachesActivated
import FirstCycleCountSharp
import OneReflectorContinuation
import PointwiseSimpleCycleTail
import TraceRetainingFirstRevisit
import TwoHistoryUnionCharge

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

namespace GeneralN

/-- Trace-retaining form of the simple-cycle branch of
`first_activated_count_outcome_sharp`. -/
structure PartialSecondCycleOutcome
    (w : Wiring) (start : Nat × Tongues) (N : Nat) : Type where
  lead : List Passage
  atRepeat : Nat × Tongues
  cycle : List Passage
  settled : Tongues
  lead_trace : PhysicalTrace w start lead atRepeat
  lead_simple : SwitchSimple lead
  lead_length_le : lead.length ≤ N
  cycle_nonempty : cycle ≠ []
  transient : PhysicalTrace w atRepeat cycle (atRepeat.1, settled)
  stable : PhysicalTrace w (atRepeat.1, settled) cycle
    (atRepeat.1, settled)
  cycle_simple : SwitchSimple cycle
  transient_phase : ∀ d, d ≤ cycle.length → ∃ port phase,
    stepN w d atRepeat = some (port, phase) ∧
      (phase = atRepeat.2 ∨ phase = settled)
  positive_settled : ∀ d, 0 < d → ∃ port,
    stepN w d atRepeat = some (port, settled)

/-- First-revisit fork retaining the pointwise fact that the cycle branch
has its settled tongue vector at every strictly positive local time.  The
two cycle-producing geometric cases are the already-stable same-entry case
and the same-exit case handled by `simple_same_exit_cycle_all_positive`. -/
private theorem first_revisit_one_vector_cycle_or_activated_reflector
    (w : Wiring) {start : Prod Nat Tongues}
    {runway path : List Passage}
    {p x q y e : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hsw : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v))
    (hentry : w.link e = some start.1) :
    (∃ cycle settled,
      cycle ≠ [] ∧
      PhysicalTrace w (q, u) cycle (q, settled) ∧
      PhysicalTrace w (q, settled) cycle (q, settled) ∧
      SwitchSimple cycle ∧
      (∀ d, d ≤ cycle.length → ∃ port phase,
        stepN w d (q, u) = some (port, phase) ∧
          (phase = u ∨ phase = settled)) ∧
      (∀ d, 0 < d → ∃ port,
        stepN w d (q, u) = some (port, settled))) ∨
    (∃ (A : ManufacturedReflector w start.1 e) (state : Tongues),
      PathGrooves A.toSupported.paths state ∧
      A.baseState = start.2 ∧
      state = A.activatedState ∧
      stepN w (runway.length + 1) (q, u) = some (e, state) ∧
      (∀ j, j ∉ A.exploration.map passageSwitch →
        state j = start.2 j)) := by
  have hsimpleExcursion : SwitchSimple ((p, x) :: path) := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).2.1
  have holdStem :
      p = 3 * passageSwitch (p, x) ∨
        x = 3 * passageSwitch (p, x) :=
    hexcursion.passage_stem_endpoint (p, x) List.mem_cons_self
  have hrepeatStem :
      q = 3 * passageSwitch (q, y) ∨
        y = 3 * passageSwitch (q, y) := by
    have hs := arrive_stem_endpoint u q
    rw [hrepeat] at hs
    exact hs
  have hsw' : passageSwitch (p, x) = passageSwitch (q, y) := by
    simpa [passageSwitch] using hsw
  have hshare : p = q ∨ p = y ∨ x = q ∨ x = y :=
    recorded_passages_share_port holdStem hrepeatStem hsw'
  have hfar : w.link start.1 = some e := w.symm _ _ hentry
  have hsupport := crossed_revisit_support_grooved
    hrunway hexcursion hsimple hsw hrepeat
  have hpreserves :
      ∀ j, j ∉ (runway ++ (p, x) :: path).map passageSwitch →
        v j = start.2 j := by
    intro j hforeign
    have hu := (hrunway.append hexcursion).preserves j (by
      intro passage hp hEq
      apply hforeign
      exact List.mem_map.mpr ⟨passage, hp, hEq⟩)
    have hjq : j ≠ q / 3 := by
      intro hEq
      apply hforeign
      apply List.mem_map.mpr
      refine ⟨(p, x), List.mem_append_right runway List.mem_cons_self, ?_⟩
      simp only [passageSwitch]
      omega
    exact (arrive_preserves_other hrepeat hjq).trans hu
  rcases hshare with hpq | hpy | hxq | hxy
  · subst q
    left
    have hgrooved := hexcursion.grooved_of_switchSimple hsimpleExcursion
    have hstable : PhysicalTrace w (p, u) ((p, x) :: path) (p, u) :=
      physicalTrace_grooved_passages w u p x p path
        hexcursion.linked hgrooved hexcursion.last_link
    have hphase : ∀ d, d ≤ ((p, x) :: path).length → ∃ port phase,
        stepN w d (p, u) = some (port, phase) ∧
          (phase = u ∨ phase = u) := by
      intro d hd
      obtain ⟨port, hrun⟩ :=
        hstable.grooved_prefix_tongues u hgrooved hd
      exact ⟨port, u, hrun, Or.inl rfl⟩
    have hall : ∀ d, ∃ port,
        stepN w d (p, u) = some (port, u) :=
      hstable.stable_simple_cycle_all_time (by simp) hsimpleExcursion
    exact ⟨(p, x) :: path, u, by simp,
      hstable, hstable, hsimpleExcursion, hphase,
      fun d _ => hall d⟩
  · subst y
    have hback := hrunway.simple_cross_exit_retraces_prefix
      hexcursion hsimple hrepeat
    rw [hfar] at hback
    by_cases hxq : x = q
    · subst q
      have hpathNil := same_exit_excursion_path_nil
        hexcursion hsimpleExcursion
      subst path
      have hfullGrooved :=
        (hrunway.append hexcursion).grooved_of_switchSimple hsimple
      have hold : arrive u x = (p, u) :=
        hfullGrooved (p, x)
          (List.mem_append_right runway List.mem_cons_self)
      have holdGroove := hold
      rw [hrepeat] at hold
      injection hold with _ huv
      subst v
      have hself : w.link x = some x := by
        simpa [lastPassageExit] using hexcursion.last_link
      let A : ManufacturedStayReflector w start.1 e := {
        base := start.2
        mouthState := u₀
        returnState := u
        runway := runway
        mouth := p
        arm := x
        runwayTrace := by simpa using hrunway
        coreTrace := by simpa using hexcursion
        simple := hsimple
        stemEndpoint := hexcursion.passage_stem_endpoint
          (p, x) List.mem_cons_self
        selfLink := hself
        entryEdge := hentry
      }
      refine Or.inr ⟨.stay A, u, ?_, rfl, rfl, hback, ?_⟩
      · change PathGrooves [runway, [(p, x)]] u
        apply pathGrooves_pair.mpr
        exact ⟨(pathGrooves_pair.mp hsupport).1,
          passagesGrooved_singleton.mpr holdGroove⟩
      · simpa [ManufacturedReflector.exploration] using hpreserves
    · let A : ManufacturedFlipReflector w start.1 e := {
        base := start.2
        mouthState := u₀
        returnState := u
        afterReturn := v
        runway := runway
        candy := path
        mouth := p
        firstArm := x
        secondArm := q
        runwayTrace := by simpa using hrunway
        candyTrace := hexcursion
        simple := hsimple
        crossed := hrepeat
        arms_ne := hxq
        entryEdge := hentry
      }
      refine Or.inr ⟨.flip A, v, ?_, rfl, rfl, hback, ?_⟩
      · change PathGrooves [runway, path] v
        exact hsupport
      · simpa [ManufacturedReflector.exploration] using hpreserves
  · subst q
    have hfull := hrunway.append hexcursion
    have hgrooved := hfull.grooved_of_switchSimple hsimple
    have hold : arrive u x = (p, u) :=
      hgrooved (p, x)
        (List.mem_append_right runway List.mem_cons_self)
    have holdGroove := hold
    rw [hrepeat] at hold
    injection hold with hyp huv
    subst y
    subst v
    have hback := hrunway.simple_cross_exit_retraces_prefix
      hexcursion hsimple (by simpa using hrepeat)
    rw [hfar] at hback
    have hpathNil := same_exit_excursion_path_nil
      hexcursion hsimpleExcursion
    subst path
    have hself : w.link x = some x := by
      simpa [lastPassageExit] using hexcursion.last_link
    let A : ManufacturedStayReflector w start.1 e := {
      base := start.2
      mouthState := u₀
      returnState := u
      runway := runway
      mouth := p
      arm := x
      runwayTrace := by simpa using hrunway
      coreTrace := by simpa using hexcursion
      simple := hsimple
      stemEndpoint := hexcursion.passage_stem_endpoint
        (p, x) List.mem_cons_self
      selfLink := hself
      entryEdge := hentry
    }
    refine Or.inr ⟨.stay A, u, ?_, rfl, rfl, hback, ?_⟩
    · change PathGrooves [runway, [(p, x)]] u
      apply pathGrooves_pair.mpr
      exact ⟨(pathGrooves_pair.mp hsupport).1,
        passagesGrooved_singleton.mpr holdGroove⟩
    · simpa [ManufacturedReflector.exploration] using hpreserves
  · subst y
    left
    obtain ⟨htransient, hstable, hsimpleCycle, hphase⟩ :=
      hexcursion.simple_same_exit_cycle_traces_with_phase
        hsimpleExcursion hrepeat
    have hpositive :=
      hexcursion.simple_same_exit_cycle_all_positive
        hsimpleExcursion hrepeat
    exact ⟨(q, x) :: path, v, by simp,
      htransient, hstable, hsimpleCycle, hphase, hpositive⟩

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
        A.exploration.length + A.runway.length + 1 ≤ 2 * N + 1 ∧
        PathGrooves A.toSupported.paths state ∧
        A.baseState = start.2 ∧
        state = A.activatedState ∧
        stepN w (A.exploration.length + A.runway.length + 1) start =
          some (e, state) ∧
        (∀ j, j ∉ A.exploration.map passageSwitch →
          state j = start.2 j) := by
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
  have hfork := first_revisit_one_vector_cycle_or_activated_reflector w
    hrunway hexcursion hbeforeSimple hsw hrepeat hentry
  have hleadTrace : PhysicalTrace w start
      (runway ++ (p, x) :: path) (q, u) := hbeforeTrace
  have hleadLe : (runway ++ (p, x) :: path).length ≤ N :=
    hleadTrace.simple_length_le hN hbeforeSimple
  rcases hfork with hcycle | hreflector
  · obtain ⟨cycle, settled, hnonempty, htransient,
      hstable, hsimpleCycle, hphase, hpositive⟩ := hcycle
    exact Or.inl ⟨{
      lead := runway ++ (p, x) :: path
      atRepeat := (q, u)
      cycle := cycle
      settled := settled
      lead_trace := hleadTrace
      lead_simple := hbeforeSimple
      lead_length_le := hleadLe
      cycle_nonempty := hnonempty
      transient := htransient
      stable := hstable
      cycle_simple := hsimpleCycle
      transient_phase := hphase
      positive_settled := hpositive
    }⟩
  · right
    obtain ⟨A, state, hgrooves, hbase, hactivated,
      _hback, hpreserves⟩ := hreflector
    have hexplorationLe : A.exploration.length ≤ N :=
      A.exploration_trace.simple_length_le hN A.exploration_simple
    have hrunwayLe : A.runway.length ≤ A.exploration.length := by
      cases A <;>
        simp [ManufacturedReflector.runway,
          ManufacturedReflector.exploration]
    have hgroovesActivated :
        PathGrooves A.toSupported.paths A.activatedState := by
      rw [← hactivated]
      exact hgrooves
    have hbackExact :
        stepN w (A.runway.length + 1) A.preReturn =
          some (e, A.activatedState) := by
      have htrace := physicalTrace_contact_retraces_prefix
        A.runway_trace (A.runway_grooved hgroovesActivated)
        A.entryEdge A.return_arrive_mouth
      simpa [reversePassages_length] using htrace.sound
    have hreachBase :
        stepN w (A.exploration.length + A.runway.length + 1)
          (start.1, A.baseState) = some (e, A.activatedState) := by
      have hlen : A.exploration.length + A.runway.length + 1 =
          A.exploration.length + (A.runway.length + 1) := by omega
      rw [hlen, stepN_add, A.exploration_trace.sound]
      exact hbackExact
    refine ⟨A, state, ?_, hgrooves, hbase, hactivated, ?_, hpreserves⟩
    · omega
    · simpa [hbase, hactivated] using hreachBase

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
  path : List Passage
  old : Passage
  oriented : Passage
  full_trace : PhysicalTrace w (e, A.activatedState) full finish
  full_simple : SwitchSimple full
  split : full = approach ++ (p, x) :: suffix
  approach_trace :
    PhysicalTrace w (e, A.activatedState) approach (p, contactState)
  suffix_trace :
    PhysicalTrace w (p, contactState) ((p, x) :: suffix) finish
  old_grooves : PathGrooves A.toSupported.paths contactState
  arrive_eq : arrive contactState p = (x, nextState)
  path_mem : path ∈ A.toSupported.paths
  old_mem : old ∈ path
  old_switch : passageSwitch old = p / 3
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
  exact ⟨{
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
noncomputable def ChangedContact.history
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
    VectorCount.restrict N C.nextState ∈ C.history N := by
  apply List.mem_append_right
  simp

/-- A backward first damaging contact closes into the old route-prefix
lasso.  Both tail phases are already represented in `history`. -/
theorem ChangedContact.backward_all_time_zero_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A)
    (hbackward : C.x = C.oriented.1)
    (times : List Nat) :
    NoveltyCoverOn w N (e, A.activatedState)
      times (C.history N) 0 := by
  obtain ⟨recorded, tail, hrouteSplit⟩ :=
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
  let K := C.approach.length
  have hreach : stepN w K (e, A.activatedState) =
      some (C.p, C.contactState) := by
    simpa [K] using C.approach_trace.sound
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
    have hglobal : stepN w j (e, A.activatedState) =
        some (port, phase) := by
      rw [hjEq, stepN_add, hreach]
      exact hrun
    have hvector : restrictedTonguesAt w N
        (e, A.activatedState) j = VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [h] using C.contact_mem_history (N := N)
    · simpa [h] using C.next_mem_history (N := N)

/-- The completed-reflector forward-splice construction only used the
second reflector to supply a switch-simple route.  This is the same lemma
with that route supplied directly, so it applies to a partial second run. -/
private theorem partial_first_forward_contact_active_lead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {route approach : List Passage} {p x : Nat}
    {suffix : List Passage} {startState u v : Tongues}
    {oriented : Passage} {repaired : Tongues}
    (hsplit : route = approach ++ (p, x) :: suffix)
    (hfullSimple : SwitchSimple route)
    (happroach :
      PhysicalTrace w (e, startState) approach (p, u))
    (hpaths : PathGrooves A.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3))
    (horiented : oriented ∈ A.orientedRoute u)
    (horientedGroove : arrive u oriented.2 = (oriented.1, u))
    (horientedSwitch : passageSwitch oriented = p / 3)
    (hforward : x = oriented.2)
    (hrepair : arrive v oriented.1 = (oriented.2, repaired))
    (hrestored :
      arrive repaired oriented.2 = (oriented.1, repaired)) :
    ∃ (entry mouth returnPort outside : Nat)
        (oldPrefix oldTail candy : List Passage) (tailSteps : Nat),
      (entry, mouth) ∈ A.orientedRoute u ∧
      A.orientedRoute u = oldPrefix ++ (entry, mouth) :: oldTail ∧
      PhysicalTrace w (outside, u) oldTail (A.orientedFinish u, u) ∧
      PhysicalTrace w (e, u) approach (returnPort, u) ∧
      SwitchSimple approach ∧
      PassagesGrooved u approach ∧
      (∀ passage ∈ approach, passageSwitch passage ≠ mouth / 3) ∧
      candy = reversePassages oldPrefix ++ approach ∧
      entry % 3 ≠ 0 ∧ mouth % 3 = 0 ∧
      w.link mouth = some outside ∧
      entry ≠ returnPort ∧
      PassagesGrooved u ((mouth, entry) :: candy) ∧
      PhysicalTrace w (mouth, u) ((mouth, entry) :: candy)
        (returnPort, u) ∧
      arrive u returnPort = (mouth, flipAt u (mouth / 3)) ∧
      PathGrooves A.toSupported.paths u ∧
      PassagesGrooved u candy ∧
      (∀ passage ∈ candy, passageSwitch passage ≠ mouth / 3) ∧
      IsReflector w mouth outside (candy.length + 2)
        (fun state => PassagesGrooved state candy)
        (fun state => flipAt state (mouth / 3)) ∧
      stepN w (approach.length + 1) (e, startState) =
        some (outside, flipAt u (mouth / 3)) ∧
      stepN w tailSteps (outside, u) =
        some (e, A.toSupported.action.apply u) := by
  rcases oriented with ⟨a, s⟩
  simp only at horiented horientedGroove hforward hrepair hrestored
  subst x
  obtain ⟨hpBranch, hsEq, _hv, _hback⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hsStem : s % 3 = 0 := by
    rw [hsEq]
    omega
  have hsp : s / 3 = p / 3 := by
    rw [hsEq]
    omega
  have hsa : s / 3 = a / 3 := by
    have hswitch := arrive_exit_switch u s
    rw [horientedGroove] at hswitch
    exact hswitch.symm
  have haBranch : a % 3 ≠ 0 := by
    have haEq : branchPort (s / 3) (u (s / 3)) = a := by
      unfold arrive at horientedGroove
      rw [if_pos hsStem] at horientedGroove
      exact congrArg Prod.fst horientedGroove
    intro haStem
    cases hu : u (s / 3) <;>
      simp [branchPort, hu] at haEq <;> omega
  have hap : a ≠ p := by
    intro hEq
    subst p
    have holdForward := groove_forward horientedGroove
    rw [harrive] at holdForward
    have huv : v = u := congrArg Prod.snd holdForward
    apply hchanged
    rw [huv]
  obtain ⟨oldPrefix, oldTail, hrouteSplit⟩ :=
    List.append_of_mem horiented
  have hroute := A.orientedRoute_trace u hpaths
  have hrouteSimple := A.orientedRoute_simple u
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hOldPrefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hrouteSplit hrouteGrooved hrouteSimple
  have hOldPrefixGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hrouteSplit]
      exact List.mem_append_left _ hp)
  have hApproachSimple : SwitchSimple approach := by
    have hsimple := hfullSimple
    unfold SwitchSimple at hsimple ⊢
    rw [hsplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple hApproachSimple
  have hApproachForeign :
      ∀ passage ∈ approach, passageSwitch passage ≠ p / 3 := by
    have hsimple := hfullSimple
    unfold SwitchSimple at hsimple
    rw [hsplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (p, s)) (by simp)
    exact hne (by simpa [passageSwitch] using hEq)
  let candy := reversePassages oldPrefix ++ approach
  have hCandyGrooved : PassagesGrooved u candy := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · exact reversePassages_grooved
        hOldPrefixGrooved passage hold
    · exact hApproachGrooved passage hnew
  have hCandyForeign :
      ∀ passage ∈ candy, passageSwitch passage ≠ s / 3 := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · have hmapped : passageSwitch passage ∈
          (reversePassages oldPrefix).map passageSwitch :=
        List.mem_map.mpr ⟨passage, hold, rfl⟩
      have hmap := map_passageSwitch_reversePassages hOldPrefixData.1
      rw [hmap] at hmapped
      have horiginal : passageSwitch passage ∈
          oldPrefix.map passageSwitch := List.mem_reverse.mp hmapped
      obtain ⟨old, holdMem, holdEq⟩ := List.mem_map.mp horiginal
      intro hmouth
      apply hOldPrefixData.2 old holdMem
      exact holdEq.trans (hmouth.trans hsa)
    · intro hmouth
      apply hApproachForeign passage hnew
      exact hmouth.trans hsp
  have hback := physicalTrace_contact_retraces_prefix
    hOldPrefixData.1 hOldPrefixGrooved A.entryEdge horientedGroove
  have hforwardTrace := happroach.replay_grooved u hApproachGrooved
  have hsplice :
      PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy, List.append_assoc] using
      hback.append hforwardTrace
  have hSpliceGrooved : PassagesGrooved u ((s, a) :: candy) := by
    intro passage hpassage
    rcases List.mem_cons.mp hpassage with hhead | htail
    · simpa [hhead] using groove_forward horientedGroove
    · exact hCandyGrooved passage htail
  have hroute' := hroute
  rw [hrouteSplit] at hroute'
  obtain ⟨middle, hOldBefore, hOldAfter⟩ := hroute'.split_append
  have hMiddle : middle = (a, u) := by
    have h₁ := hOldBefore.sound
    have h₂ := hOldPrefixData.1.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hOldAfter with
  | @cons _ _ outside _ oldAfter _ _ hOldArrive hmouth hOldRest =>
      have hOldAfterState : oldAfter = u := by
        have hforwardOld := groove_forward horientedGroove
        rw [hOldArrive] at hforwardOld
        exact congrArg Prod.snd hforwardOld
      subst oldAfter
      have hcontactTrace :
          PhysicalTrace w (a, u) [(a, s)] (outside, u) :=
        PhysicalTrace.cons (groove_forward horientedGroove)
          hmouth (PhysicalTrace.nil _)
      have hlead := hOldPrefixData.1.append hcontactTrace
      have hleadSplit : A.orientedRoute u =
          (oldPrefix ++ [(a, s)]) ++ oldTail := by
        rw [hrouteSplit]
        simp [List.append_assoc]
      obtain ⟨tailSteps, _hlen, hcomplete⟩ :=
        A.complete_after_oriented_prefix u hpaths hleadSplit hlead
      have hflip : v = flipAt u (s / 3) := by
        have hv := changed_arrival_eq_flipAt harrive hchanged
        simpa [hsp] using hv
      have hone : stepN w 1 (p, u) = some (outside, v) := by
        simp [stepN, step, harrive, hmouth]
      have hreach :
          stepN w (approach.length + 1) (e, startState) =
            some (outside, flipAt u (s / 3)) := by
        rw [stepN_add, happroach.sound]
        simp only [Option.bind_some]
        rw [hone, hflip]
      have hcrossed : arrive u p =
          (s, flipAt u (s / 3)) := by
        rw [harrive, hflip]
      refine ⟨a, s, p, outside, oldPrefix, oldTail,
        candy, tailSteps, horiented, hrouteSplit, hOldRest,
        hforwardTrace, hApproachSimple, hApproachGrooved,
        (by
          intro passage hpassage
          simpa [hsp] using hApproachForeign passage hpassage),
        rfl, haBranch, hsStem, hmouth, hap, hSpliceGrooved,
        hsplice, hcrossed, hpaths, hCandyGrooved,
        hCandyForeign, ?_, hreach, hcomplete⟩
      exact stem_lobe_isReflector_foreign w candy
        hsStem haBranch hpBranch hsa hsp hap hCandyForeign
        hsplice.linked hsplice.last_link hmouth

/-- For a flip reflector, a changed forward partial contact contributes at
most the two Gray corners beyond the coefficient-one contact history. -/
theorem ChangedContact.forward_flip_all_time_two_novelty
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
    NoveltyCoverOn w N (e, (ManufacturedReflector.flip R).activatedState)
      times (C.history N) 2 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach,
      _hcomplete⟩ :=
    partial_first_forward_contact_active_lead
      (A := ManufacturedReflector.flip R)
      C.split C.full_simple C.approach_trace C.old_grooves
      C.arrive_eq C.changed C.oriented_mem C.oriented_groove
      C.oriented_switch hforward hrepair hrestored
  let K := C.approach.length + 1
  let state := C.contactState
  let alternate := flipAt state (mouth / 3)
  have hreach' :
      stepN w K (e, (ManufacturedReflector.flip R).activatedState) =
        some (outside, alternate) := by
    simpa [K, state, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.history N := by
    simpa [hnextAlternate] using C.next_mem_history (N := N)
  have hstateHistorical :
      VectorCount.restrict N state ∈ C.history N := by
    simpa [state] using C.contact_mem_history (N := N)
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
    obtain ⟨D, _hDAction, hEntryOldNe, hDpaths,
        hNewAvoidsDRaw, _htravel⟩ :=
      R.suffix_after_runway_passage_with_travel state hRpaths
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
        hmouthLink hcontact hreach' times (C.history N)
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
        hreach' times (C.history N) hentryHistorical
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
      hreach' N (C.history N) hentryHistorical times
      hleadHistorical
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

private theorem partial_twoPhase_concat
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
      (phase = u ∨ phase = v) := by
  by_cases hdl : d ≤ left
  · exact hleftPhase d hdl
  · let r := d - left
    have hr : r ≤ right := by
      dsimp [r]
      omega
    have hdecomp : d = left + r := by
      dsimp [r]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hrightPhase r hr
    refine ⟨port, phase, ?_, hphase⟩
    rw [hdecomp, stepN_add, hleft]
    simpa using hrun

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
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete⟩ :=
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
        exact partial_twoPhase_concat
          hDaltEnd hDaltPhase hReversePhase d
          (by simpa [half] using hd)
      have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact partial_twoPhase_concat
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
        exact partial_twoPhase_concat
          hHalfAlt hHalfAltPhase hHalfStatePhase d
          (by simpa [period] using hd)
      have hpositive : 0 < period := by
        have hdpos := (ManufacturedReflector.stay D).travel_pos
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
        exact partial_twoPhase_concat
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

/-- Uniform partial-run changed-contact bound.  Backward and stay-forward
contacts add no new vector; a flip-forward contact adds at most two. -/
theorem ChangedContact.all_time_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A)
    (times : List Nat) :
    NoveltyCoverOn w N (e, A.activatedState)
      times (C.history N) 2 := by
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · obtain ⟨fresh, hfresh, hmem⟩ :=
      C.backward_all_time_zero_novelty
        (N := N) hbackward times
    exact ⟨fresh, by omega, hmem⟩
  · cases A with
    | stay R =>
        obtain ⟨fresh, hfresh, hmem⟩ :=
          C.forward_stay_all_time_zero_novelty
            hforward hrepair hrestored times
        exact ⟨fresh, by omega, hmem⟩
    | flip R =>
        exact C.forward_flip_all_time_two_novelty
          hforward hrepair hrestored times

/-- The first reflector, the approach to its first damaging support contact,
and the entire resulting repair tail have at most `N+5` distinct vectors. -/
theorem ChangedContact.all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : ChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  obtain ⟨fresh, hfresh, hlocal⟩ :=
    C.all_time_two_novelty (N := N) localTimes
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.history N) 2 := by
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
      have hm := hlocal d hdMem
      have hshift := restrictedTonguesAt_sub_of_reach
        (N := N) hreach (by omega) (hlive k hk)
      rw [hshift]
      exact hm
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory := C.history_length_le_N_add_three hN hA
  omega

/-- Every finite dead run has a literal final live physical trace. -/
private theorem terminal_trace_of_dead
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
        hstable, _hsimple⟩ := hcycle
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
        hactivated, hback, _hpreserves⟩ := hreflector
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

/-- The dead partial-second-run branch costs `N+5`: its terminal trace is
simple; preserved support costs `N+2`, while first damage costs `N+5`. -/
theorem ManufacturedReflector.dead_second_run_distinct_le_N_add_five
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
    times.length ≤ N + 5 := by
  obtain ⟨finish, passages, _hlength, htrace, hfall⟩ :=
    terminal_trace_of_dead hdead
  have hsimple : SwitchSimple passages :=
    ManufacturedReflector.dead_continuation_trace_simple
      A hA hdead htrace
  by_cases hend : PathGrooves A.toSupported.paths finish.2
  · have htwo := preserved_simple_fall_distinct_le_N_add_two
      hN A hA htrace hsimple hend hfall times hlive hnd
    omega
  · obtain ⟨C⟩ :=
      ManufacturedReflector.changedContact_of_broken_simple
        A hA htrace hsimple hend
    exact C.all_run_distinct_le_N_add_five hN hA times hlive hnd

/-- A retained one-vector cycle after one reflector costs `N+5` even when
its switch-simple lead damages the old support. -/
theorem PartialSecondCycleOutcome.all_run_distinct_le_N_add_five
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
    times.length ≤ N + 5 := by
  by_cases hend : PathGrooves A.toSupported.paths C.atRepeat.2
  · have hthree := simple_lead_one_vector_tail_distinct_le_N_add_three
      hN A hA C.lead_trace C.lead_simple hend C.positive_settled
      times hlive hnd
    omega
  · obtain ⟨D⟩ :=
      ManufacturedReflector.changedContact_of_broken_simple
        A hA C.lead_trace C.lead_simple hend
    exact D.all_run_distinct_le_N_add_five hN hA times hlive hnd

/-- **Coefficient-one partial-second-run theorem.**  After one completed
reflector, the next `N+1` probe either dies (`N+5`), reaches the retained
one-vector cycle (`N+5`), or completes the opposite reflector (`N+6`). -/
theorem ManufacturedReflector.partial_second_run_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 6 := by
  cases hprobe : stepN w (N + 1) (e, A.activatedState) with
  | none =>
      have hfive :=
        ManufacturedReflector.dead_second_run_distinct_le_N_add_five
          hN A hA hprobe times hlive hnd
      omega
  | some finish =>
      have hentry : w.link g = some e := w.symm _ _ A.entryEdge
      rcases first_activated_trace_outcome_sharp_partial
          hN hprobe hentry with hcycle | hreflector
      · obtain ⟨C⟩ := hcycle
        have hfive :=
          PartialSecondCycleOutcome.all_run_distinct_le_N_add_five
            hN A hA C times hlive hnd
        omega
      · obtain ⟨B, state, _hlength, hB, hbase,
          hactivated, _hreach, _hpreserves⟩ := hreflector
        subst state
        exact A.two_reflector_all_run_distinct_le_N_add_six
          hN B hbase hA hB times hlive hnd

/-- **Known incoming edge, coefficient one.**  The first probe either dies,
settles on its own simple cycle, or manufactures `A`; in the last case the
preceding theorem closes the entire second run at `N+6`. -/
theorem known_edge_all_run_distinct_le_N_add_six
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  cases hfirst : stepN w (N + 1) start with
  | none =>
      have hshort := dead_horizon_live_distinct_le
        hfirst times hlive hnd
      omega
  | some finish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycle | hreflector
      · have hshort := hcycle times hnd
        omega
      · obtain ⟨A, state, _hlength, hA, hbase,
          hactivated, _hreach, _hpreserves⟩ := hreflector
        subst state
        have hliveA : ∀ k ∈ times,
            (stepN w k (start.1, A.baseState)).isSome := by
          simpa [hbase] using hlive
        have hndA : (times.map
            (restrictedTonguesAt w N
              (start.1, A.baseState))).Nodup := by
          simpa [hbase] using hnd
        exact
          ManufacturedReflector.partial_second_run_distinct_le_N_add_six
            hN A hA times hliveA hndA

end PartialSecondRunSharp

end GeneralN
