import EventuallyPeriodicPrefixes
import StateLawTwoSixUltra
import OneReflectorContinuation
import TraceRetainingFirstRevisit

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

/-- Trace-retaining form of the simple-cycle branch of the sharp first
activation theorem. -/
structure FirstActivatedCycleOutcome
    (w : Wiring) (start : Nat × Tongues) (N : Nat) : Type where
  lead : List Passage
  atRepeat : Nat × Tongues
  cycle : List Passage
  settled : Tongues
  lead_trace : PhysicalTrace w start lead atRepeat
  lead_simple : SwitchSimple lead
  lead_length_le : lead.length <= N
  cycle_nonempty : cycle ≠ []
  transient : PhysicalTrace w atRepeat cycle
    (atRepeat.1, settled)
  stable : PhysicalTrace w (atRepeat.1, settled) cycle
    (atRepeat.1, settled)
  cycle_simple : SwitchSimple cycle
  transient_phase : forall d, d <= cycle.length ->
    exists port phase,
      stepN w d atRepeat = some (port, phase) ∧
        (phase = atRepeat.2 ∨ phase = settled)

/-- `first_activated_count_outcome_sharp` with the physical simple-cycle
witness retained.  The reflector alternative is exactly the original sharp
alternative. -/
theorem first_activated_trace_outcome_sharp
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    Nonempty (FirstActivatedCycleOutcome w start N) ∨
      exists (A : ManufacturedReflector w start.1 e)
          (state : Tongues),
        A.exploration.length + A.runway.length + 1 <= 2 * N + 1 ∧
        PathGrooves A.toSupported.paths state ∧
        A.baseState = start.2 ∧
        state = A.activatedState ∧
        stepN w (A.exploration.length + A.runway.length + 1) start =
          some (e, state) ∧
        (forall j, j ∉ A.exploration.map passageSwitch ->
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
  rcases atOld with ⟨oldPort, u0⟩
  simp only at hatOldPort
  subst oldPort
  obtain ⟨v, hrepeat⟩ := hafterTrace.head_arrive.2
  have hmiddlePort : middle.1 = q := hafterTrace.head_arrive.1
  rcases middle with ⟨middlePort, u⟩
  simp only at hmiddlePort
  subst middlePort
  have hsw : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  have hfork := first_revisit_cycle_phase_or_activated_reflector w
    hrunway hexcursion hbeforeSimple hsw hrepeat hentry
  have hprefTrace : PhysicalTrace w start
      (runway ++ (p, x) :: path) (q, u) := hbeforeTrace
  have hprefLe : (runway ++ (p, x) :: path).length <= N :=
    hprefTrace.simple_length_le hN hbeforeSimple
  rcases hfork with hcycle | hreflector
  · obtain ⟨cycle, settled, hnonempty, htransient,
      hstable, hsimpleCycle, hphase⟩ := hcycle
    exact Or.inl ⟨{
      lead := runway ++ (p, x) :: path
      atRepeat := (q, u)
      cycle := cycle
      settled := settled
      lead_trace := hprefTrace
      lead_simple := hbeforeSimple
      lead_length_le := hprefLe
      cycle_nonempty := hnonempty
      transient := htransient
      stable := hstable
      cycle_simple := hsimpleCycle
      transient_phase := hphase
    }⟩
  · right
    obtain ⟨A, state, hgrooves, hbase, hactivated,
      _hback, hpreserves⟩ := hreflector
    have hexplorationLe : A.exploration.length <= N :=
      A.exploration_trace.simple_length_le hN A.exploration_simple
    have hrunwayLe : A.runway.length <= A.exploration.length := by
      cases A <;>
        simp [ManufacturedReflector.runway,
          ManufacturedReflector.exploration]
    have hgroovesActivated :
        PathGrooves A.toSupported.paths A.activatedState := by
      rw [← hactivated]
      exact hgrooves
    have hbackExact : stepN w (A.runway.length + 1) A.preReturn =
        some (e, A.activatedState) := by
      have htrace := physicalTrace_contact_retraces_prefix
        A.runway_trace (A.runway_grooved hgroovesActivated)
        A.entryEdge A.return_arrive_mouth
      simpa [reversePassages_length] using htrace.sound
    have hreachBase : stepN w
        (A.exploration.length + A.runway.length + 1)
        (start.1, A.baseState) = some (e, A.activatedState) := by
      have hlen : A.exploration.length + A.runway.length + 1 =
          A.exploration.length + (A.runway.length + 1) := by omega
      rw [hlen, stepN_add, A.exploration_trace.sound]
      exact hbackExact
    refine ⟨A, state, ?_, hgrooves, hbase, hactivated, ?_, hpreserves⟩
    · omega
    · simpa [hbase, hactivated] using hreachBase

private theorem coeffTop_nodup_filter_nat (p : Nat -> Bool) :
    forall {xs : List Nat}, xs.Nodup -> (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact And.intro
            (fun hm => hnd.1 (List.mem_filter.mp hm).1)
            (ih hnd.2)
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem coeffTop_nodup_of_map_nodup
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) :
    forall {xs : List alpha}, (xs.map f).Nodup -> xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

private theorem coeffTop_live_distinct_le_of_stepN_none
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    {times : List Nat}
    (hnone : stepN w L start = none)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= L := by
  have htimesNodup : times.Nodup :=
    coeffTop_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  apply nodup_nat_lt_length htimesNodup
  intro k hk
  by_cases hlt : k < L
  · exact hlt
  · have hkEq : k = L + (k - L) := by omega
    have hnoneK : stepN w k start = none := by
      rw [hkEq, stepN_add, hnone]
      simp
    have hkLive := hlive k hk
    rw [hnoneK] at hkLive
    simp at hkLive

private theorem coeffTop_nodup_map_nat_of_injective_on
    {f : Nat -> Nat} {xs : List Nat}
    (hinj : forall x, x ∈ xs -> forall y, y ∈ xs ->
      f x = f y -> x = y)
    (hnd : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
        have hxy := hinj x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih
          (fun a ha b hb => hinj a
            (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb))
          hnd.2

/-- A productive passage in a switch-simple continuation cannot use an old
reusable coordinate when the old support is grooved at both endpoints.  Its
unique write would survive to the endpoint, contradicting the two old groove
values. -/
theorem PhysicalTrace.productive_writer_not_reusable_of_endpoint_grooves
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2)
    {k : Nat} (hk : k < passages.length)
    (hprod : RawProductiveAt w N start k) :
    rawWriterAt w start k ∉ A.reusableSwitches := by
  intro hreusable
  have hsurvives :=
    htrace.simple_raw_productive_writer_survives
      hN hsimple hk hprod
  obtain ⟨path, hpath, old, hold, hswitch⟩ :=
    A.mem_reusableSwitches hreusable
  have hbaseOld := hbase path hpath old hold
  have hendOld := hend path hpath old hold
  have hagree := grooved_states_agree_on_passage hbaseOld hendOld
  have hexit : old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch start.2 old.2
    rw [hbaseOld] at hs
    exact hs.symm
  apply hsurvives
  calc
    finish.2 (rawWriterAt w start k) =
        finish.2 (old.2 / 3) := by rw [hexit, hswitch]
    _ = start.2 (old.2 / 3) := hagree.symm
    _ = start.2 (rawWriterAt w start k) := by rw [hexit, hswitch]

/-- The old reusable coordinates and the first productive writers of a
support-preserving simple continuation fit in one ambient switch budget. -/
theorem ManufacturedReflector.reusable_add_preserved_first_writers_le_N
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2) :
    A.reusableSwitches.length +
      (rawFirstWriterTimes w N start passages.length).length <= N := by
  classical
  let times := rawFirstWriterTimes w N start passages.length
  let writers := times.map (rawWriterAt w start)
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact coeffTop_nodup_filter_nat _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply coeffTop_nodup_map_nat_of_injective_on
    · intro i hi j hj hEq
      have hiData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hi)
      have hjData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hj)
      exact rawFirstWriterAt_injective hiData.2 hjData.2 hEq
    · exact htimesNodup
  have hdisjoint : forall oldSwitch, oldSwitch ∈ A.reusableSwitches ->
      forall freshSwitch, freshSwitch ∈ writers ->
        oldSwitch ≠ freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside :=
      htrace.productive_writer_not_reusable_of_endpoint_grooves
        hN A hsimple hbase hend hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let switches := A.reusableSwitches ++ writers
  have hnd : switches.Nodup := by
    dsimp [switches]
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  have hlt : forall switch, switch ∈ switches -> switch < N := by
    intro switch hswitch
    rcases List.mem_append.mp hswitch with hOld | hFresh
    · exact A.reusableSwitch_lt hN hOld
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
      have hkData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hk)
      exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hnd hlt
  have hlength : A.reusableSwitches.length + times.length <= N := by
    simpa [switches, writers] using hbound
  simpa [times] using hlength

/-- The compressed history for one completed reflector and a subsequent
support-preserving switch-simple continuation.  The common activated vector
is erased from the continuation history. -/
noncomputable def ManufacturedReflector.preservedSimpleContinuationHistory
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (N : Nat) (start : Nat × Tongues) (length : Nat) :
    List (List Bool) :=
  A.sharpHistoryCore N ++
    (rawFirstWriterHistory w N start length).erase
      (VectorCount.restrict N A.activatedState)

/-- A preserved simple continuation and the completed first construction
have a coefficient-one history of size at most `N+2`. -/
theorem ManufacturedReflector.preservedSimpleContinuationHistory_length_le
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (hstart : start.2 = A.activatedState)
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2) :
    (A.preservedSimpleContinuationHistory N start passages.length).length <=
      N + 2 := by
  have hboundary : VectorCount.restrict N A.activatedState ∈
      rawFirstWriterHistory w N start passages.length := by
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hstart]
  have hcharge := A.reusable_add_preserved_first_writers_le_N
    hN htrace hsimple hbase hend
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.preservedSimpleContinuationHistory
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length]
  simp [rawFirstWriterHistory]
  omega

/-- Every local continuation vector is represented by the compressed
coefficient-one history. -/
theorem ManufacturedReflector.mem_preservedSimpleContinuationHistory
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (hstart : start.2 = A.activatedState)
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    {d : Nat} (hd : d <= passages.length) :
    restrictedTonguesAt w N start d ∈
      A.preservedSimpleContinuationHistory N start passages.length := by
  have hm := htrace.restrictedTonguesAt_mem_rawFirstWriterHistory
    (N := N) hsimple d hd
  by_cases hboundary : restrictedTonguesAt w N start d =
      VectorCount.restrict N A.activatedState
  · apply List.mem_append_left
    rw [hboundary]
    exact A.activated_mem_sharpHistoryCore
  · apply List.mem_append_right
    exact (List.mem_erase_of_ne hboundary).mpr hm

/-- Pointwise global coverage through the completed first journey and the
preserved simple continuation. -/
theorem ManufacturedReflector.journey_then_preserved_simple_mem
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    {k : Nat}
    (hk : k <= A.exploration.length + A.runway.length + 1 +
      passages.length) :
    restrictedTonguesAt w N (g, A.baseState) k ∈
      A.preservedSimpleContinuationHistory N
        (e, A.activatedState) passages.length := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localStart : Nat × Tongues := (e, A.activatedState)
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some localStart := by
    simpa [firstTravel, localStart] using
      A.manufacturing_journey_reaches_activated hA
  by_cases hfirst : k <= firstTravel
  · apply List.mem_append_left
    apply A.mem_sharpHistoryCore_of_mem
    exact A.manufacturing_journey_mem_sharpHistory hA (by
      simpa [firstTravel] using hfirst)
  · let d := k - firstTravel
    have hkEq : k = firstTravel + d := by
      dsimp [d]
      omega
    have hd : d <= passages.length := by
      dsimp [d, firstTravel] at hk ⊢
      omega
    have hlocalLive := stepN_prefix_some hd htrace.sound
    have hshift := tonguesAt_add_of_reaches hreachA hlocalLive
    have hvector : restrictedTonguesAt w N
        (g, A.baseState) k =
        restrictedTonguesAt w N localStart d := by
      unfold restrictedTonguesAt
      rw [hkEq]
      exact congrArg (VectorCount.restrict N) hshift
    rw [hvector]
    exact A.mem_preservedSimpleContinuationHistory
      (N := N) (finish := finish) (passages := passages)
      rfl htrace hsimple hd

/-- A trace-retained sharp cycle has exactly the two tongue phases exposed by
the first-activation theorem, at all future times. -/
theorem FirstActivatedCycleOutcome.tail_distinct_le_two
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : FirstActivatedCycleOutcome w start N)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N C.atRepeat)).Nodup) :
    times.length <= 2 := by
  have hpositive : 0 < C.cycle.length := by
    cases hcycle : C.cycle with
    | nil => exact (C.cycle_nonempty hcycle).elim
    | cons passage rest => simp
  have hperiod : stepN w C.cycle.length
      (C.atRepeat.1, C.settled) =
      some (C.atRepeat.1, C.settled) := C.stable.sound
  have hgrooved : PassagesGrooved C.settled C.cycle :=
    C.stable.grooved_of_switchSimple C.cycle_simple
  have hsettledAll : forall d, exists port,
      stepN w d (C.atRepeat.1, C.settled) =
        some (port, C.settled) := by
    intro d
    have hwindow : forall r, r <= C.cycle.length ->
        exists port phase,
          stepN w r (C.atRepeat.1, C.settled) =
            some (port, phase) ∧
          (phase = C.settled ∨ phase = C.settled) := by
      intro r hr
      obtain ⟨port, hrun⟩ :=
        C.stable.grooved_prefix_tongues C.settled hgrooved hr
      exact ⟨port, C.settled, hrun, Or.inl rfl⟩
    obtain ⟨port, phase, hrun, hphase⟩ :=
      periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow d
    refine ⟨port, ?_⟩
    rcases hphase with h | h <;> rwa [h] at hrun
  let history :=
    [VectorCount.restrict N C.atRepeat.2,
      VectorCount.restrict N C.settled]
  have hcover : NoveltyCoverOn w N C.atRepeat times history 0 := by
    refine ⟨[], by simp, ?_⟩
    intro d _hd
    simp only [List.append_nil]
    by_cases hfirst : d <= C.cycle.length
    · obtain ⟨port, phase, hrun, hphase⟩ :=
        C.transient_phase d hfirst
      have hvector : restrictedTonguesAt w N C.atRepeat d =
          VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hrun]
      rw [hvector]
      rcases hphase with h | h
      · simp [h, history]
      · simp [h, history]
    · let r := d - C.cycle.length
      have hdEq : d = C.cycle.length + r := by
        dsimp [r]
        omega
      obtain ⟨port, hrun⟩ := hsettledAll r
      have hglobal : stepN w d C.atRepeat =
          some (port, C.settled) := by
        rw [hdEq, stepN_add, C.transient.sound]
        exact hrun
      have hvector : restrictedTonguesAt w N C.atRepeat d =
          VectorCount.restrict N C.settled := by
        simp [restrictedTonguesAt, tonguesAt, hglobal]
      simp [hvector, history]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  dsimp [history] at hcount
  omega

/-- If the trace-retained cycle branch preserves the first reflector's old
support at the repeat configuration, the whole original run has at most
`N+3` distinct vectors. -/
theorem FirstActivatedCycleOutcome.preserved_all_run_distinct_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (C : FirstActivatedCycleOutcome w (e, A.activatedState) N)
    (hend : PathGrooves A.toSupported.paths C.atRepeat.2)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + 3 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let lead := firstTravel + C.lead.length
  let history := A.preservedSimpleContinuationHistory N
    (e, A.activatedState) C.lead.length
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hreach : stepN w lead (g, A.baseState) =
      some C.atRepeat := by
    dsimp [lead]
    rw [stepN_add, hreachA]
    exact C.lead_trace.sound
  have hprefix : forall d, d <= lead ->
      restrictedTonguesAt w N (g, A.baseState) d ∈ history := by
    intro d hd
    dsimp [history]
    exact A.journey_then_preserved_simple_mem hA
      C.lead_trace C.lead_simple (by
        simpa [lead, firstTravel] using hd)
  have hboundary : VectorCount.restrict N C.atRepeat.2 ∈ history := by
    have hm := hprefix lead (Nat.le_refl _)
    have hvector : restrictedTonguesAt w N
        (g, A.baseState) lead =
        VectorCount.restrict N C.atRepeat.2 := by
      simp [restrictedTonguesAt, tonguesAt, hreach]
    rwa [hvector] at hm
  have htail : forall tailTimes : List Nat,
      (forall k, k ∈ tailTimes ->
        (stepN w k C.atRepeat).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N C.atRepeat)).Nodup ->
      tailTimes.length <= 2 := by
    intro tailTimes _ htailNodup
    exact C.tail_distinct_le_two tailTimes htailNodup
  have hcover := boundary_history_then_direct_tail_cover
    hreach history hprefix hboundary htail (by omega)
      times hlive hnd
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength :=
    A.preservedSimpleContinuationHistory_length_le
      hN rfl C.lead_trace C.lead_simple hA hend
  dsimp [history] at hcount hlength
  omega

/-! ## Exact remaining one-reflector branches -/

/-- The second run falls before the second sharp first-revisit horizon. -/
structure OneReflectorSecondDead
    (w : Wiring) (N e : Nat) (start : Nat × Tongues) : Type where
  A : ManufacturedReflector w start.1 e
  grooves : PathGrooves A.toSupported.paths A.activatedState
  base : A.baseState = start.2
  reached : stepN w
    (A.exploration.length + A.runway.length + 1) start =
      some (e, A.activatedState)
  dead : stepN w (N + 1) (e, A.activatedState) = none

/-- The second first-revisit settles on a simple cycle, but its repeat state
has genuinely damaged the old reflector support.  The support-preserving
cycle case is already bounded by `N+3`. -/
structure OneReflectorDamagedCycle
    (w : Wiring) (N e : Nat) (start : Nat × Tongues) : Type where
  A : ManufacturedReflector w start.1 e
  grooves : PathGrooves A.toSupported.paths A.activatedState
  base : A.baseState = start.2
  reached : stepN w
    (A.exploration.length + A.runway.length + 1) start =
      some (e, A.activatedState)
  cycle : FirstActivatedCycleOutcome w (e, A.activatedState) N
  damaged : ¬ PathGrooves A.toSupported.paths cycle.atRepeat.2

/-- **Top-level coefficient-one dichotomy from a known incoming edge.**

The sharp activation theorem is applied twice.  First death/cycle and every
completed two-reflector branch are bounded by `N+6`; a support-preserving
second cycle is bounded by `N+3`.  The only branches not yet absorbed are
represented by the two concrete structures above. -/
theorem known_edge_N_add_six_or_one_reflector_early_outcome
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= N + 6 ∨
      Nonempty (OneReflectorSecondDead w N e start) ∨
      Nonempty (OneReflectorDamagedCycle w N e start) := by
  cases hfirst : stepN w (N + 1) start with
  | none =>
      left
      have hc := coeffTop_live_distinct_le_of_stepN_none
        (N := N) hfirst hlive hnd
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycleA | hreflectorA
      · left
        have hc := hcycleA times hnd
        omega
      · obtain ⟨A, stateA, _hfirstLe, hgroovesA,
          hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
        subst stateA
        have hentryB : w.link start.1 = some e :=
          w.symm _ _ hentry
        have hliveA : forall k, k ∈ times ->
            (stepN w k (start.1, A.baseState)).isSome := by
          simpa [hbaseA] using hlive
        have hndA : (times.map
            (restrictedTonguesAt w N
              (start.1, A.baseState))).Nodup := by
          simpa [hbaseA] using hnd
        have closePair : forall
            (B : ManufacturedReflector w e start.1),
            B.baseState = A.activatedState ->
            PathGrooves B.toSupported.paths B.activatedState ->
            times.length <= N + 6 := by
          intro B hbaseB hgroovesB
          exact A.two_reflector_all_run_distinct_le_N_add_six
            hN B hbaseB hgroovesA hgroovesB
            times hliveA hndA
        cases hsecond : stepN w (N + 1)
            (e, A.activatedState) with
        | none =>
            right
            left
            exact ⟨{
              A := A
              grooves := hgroovesA
              base := hbaseA
              reached := hreachA
              dead := hsecond
            }⟩
        | some secondFinish =>
            rcases first_activated_count_outcome_sharp
                (w := w) (N := N) (e := start.1)
                hN hsecond hentryB with
              _hcycleB | hreflectorB
            · rcases first_activated_trace_outcome_sharp
                  (w := w) (N := N) (e := start.1)
                  hN hsecond hentryB with htraceCycle | hreflectorB'
              · obtain ⟨C⟩ := htraceCycle
                by_cases hrepeat :
                    PathGrooves A.toSupported.paths C.atRepeat.2
                · left
                  have hc := C.preserved_all_run_distinct_le_N_add_three
                    hN A hgroovesA hrepeat times hliveA hndA
                  omega
                · right
                  right
                  exact ⟨{
                    A := A
                    grooves := hgroovesA
                    base := hbaseA
                    reached := hreachA
                    cycle := C
                    damaged := hrepeat
                  }⟩
              · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                    hbaseB, hactivatedB, _hreachB,
                    _hpreservesB⟩ := hreflectorB'
                subst stateB
                left
                exact closePair B hbaseB hgroovesB
            · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                  hbaseB, hactivatedB, _hreachB,
                  _hpreservesB⟩ := hreflectorB
              subst stateB
              left
              exact closePair B hbaseB hgroovesB

structure SimpleContinuationChangedContact
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
  full_trace :
    PhysicalTrace w (e, A.activatedState) full finish
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

/-- Extract the first damaging contact from an arbitrary switch-simple
continuation.  This is the generic form needed by both partial-second-run
outcomes. -/
theorem ManufacturedReflector.simpleContinuationChangedContact
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    (hbroken : ¬ PathGrooves A.toSupported.paths finish.2) :
    Nonempty (SimpleContinuationChangedContact w A) := by
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

theorem SimpleContinuationChangedContact.approach_simple
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A) :
    SwitchSimple C.approach := by
  have hs := C.full_simple
  unfold SwitchSimple at hs ⊢
  rw [C.split] at hs
  simp only [List.map_append, List.map_cons] at hs
  exact (List.nodup_append.mp hs).1

theorem SimpleContinuationChangedContact.post_reaches
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A) :
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

/-- Coefficient-one history through the first damaging contact.  The first
reflector and all productive approach writers share the same `N`-coordinate
budget; the changed post-vector is the only extra singleton. -/
noncomputable def SimpleContinuationChangedContact.compressedLead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A) (N : Nat) :
    List (List Bool) :=
  A.sharpHistoryCore N ++
    ((rawFirstWriterHistory w N (e, A.activatedState)
      C.approach.length).erase
        (VectorCount.restrict N A.activatedState) ++
      [VectorCount.restrict N C.nextState])

theorem SimpleContinuationChangedContact.compressedLead_length_le
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
  have hcharge := A.reusable_add_preserved_first_writers_le_N
    hN C.approach_trace C.approach_simple hA C.old_grooves
  have houter := A.exploration_length_le_reusable_add_one
  unfold SimpleContinuationChangedContact.compressedLead
  rw [List.length_append, List.length_append,
    List.length_erase_of_mem hboundary, A.sharpHistoryCore_length]
  simp [rawFirstWriterHistory]
  omega

theorem SimpleContinuationChangedContact.mem_compressedLead_of_approach
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
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

theorem SimpleContinuationChangedContact.contact_mem_compressedLead
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A) :
    VectorCount.restrict N C.contactState ∈ C.compressedLead N := by
  have hm := C.mem_compressedLead_of_approach
    (N := N) (j := C.approach.length) (Nat.le_refl _)
  simpa [restrictedTonguesAt, tonguesAt,
    C.approach_trace.sound] using hm

theorem SimpleContinuationChangedContact.next_mem_compressedLead
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A) :
    VectorCount.restrict N C.nextState ∈ C.compressedLead N := by
  apply List.mem_append_right
  apply List.mem_append_right
  simp

/-- A backward first damaging contact closes immediately into the old
route-prefix lasso.  Every local vector, including the two contact phases,
is already in the coefficient-one compressed lead. -/
theorem SimpleContinuationChangedContact.backward_all_time_zero_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
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

/-- Absolute coefficient-one bound for the entire original run once the
first damaging continuation contact points backward. -/
theorem SimpleContinuationChangedContact.backward_all_run_distinct_le_N_add_three
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

/-- Exact residual after the generic backward-contact lasso has been
removed from `OneReflectorDamagedCycle`: the first damaging contact exits
forward on the old selected route and is self-repaired by the corresponding
trailing traversal. -/
structure OneReflectorForwardDamagedCycle
    (w : Wiring) (N e : Nat) (start : Nat × Tongues) : Type where
  A : ManufacturedReflector w start.1 e
  grooves : PathGrooves A.toSupported.paths A.activatedState
  base : A.baseState = start.2
  reached : stepN w
    (A.exploration.length + A.runway.length + 1) start =
      some (e, A.activatedState)
  cycle : FirstActivatedCycleOutcome w (e, A.activatedState) N
  contact : SimpleContinuationChangedContact w A
  repaired : Tongues
  forward : contact.x = contact.oriented.2
  repair : arrive contact.nextState contact.oriented.1 =
    (contact.oriented.2, repaired)
  restored : arrive repaired contact.oriented.2 =
    (contact.oriented.1, repaired)

/-- Split a damaged simple-cycle capture at its first damaging passage.
The backward orientation is already bounded by `N+3`; the forward
self-repairing orientation is retained as the sole exact residual. -/
theorem OneReflectorDamagedCycle.N_add_three_or_forward
    {w : Wiring} {N e : Nat} {start : Nat × Tongues}
    (D : OneReflectorDamagedCycle w N e start)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 3 ∨
      Nonempty (OneReflectorForwardDamagedCycle w N e start) := by
  obtain ⟨C⟩ := D.A.simpleContinuationChangedContact
    D.grooves D.cycle.lead_trace D.cycle.lead_simple D.damaged
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · left
    have hliveA : ∀ k ∈ times,
        (stepN w k (start.1, D.A.baseState)).isSome := by
      simpa [D.base] using hlive
    have hndA : (times.map
        (restrictedTonguesAt w N
          (start.1, D.A.baseState))).Nodup := by
      simpa [D.base] using hnd
    exact C.backward_all_run_distinct_le_N_add_three
      hN D.grooves hbackward times hliveA hndA
  · right
    exact ⟨{
      A := D.A
      grooves := D.grooves
      base := D.base
      reached := D.reached
      cycle := D.cycle
      contact := C
      repaired := repaired
      forward := hforward
      repair := hrepair
      restored := hrestored
    }⟩

/-- Sharpened known-edge assembly.  The completed two-reflector branch,
both initial cycle/death branches, support-preserving second cycles, and now
backward damaging second cycles are all closed at `N+6`.  Exactly two raw
outcomes remain: second-run death before its first-revisit horizon, and a
forward self-repairing first damage before a same-exit cycle. -/
theorem known_edge_N_add_six_or_exact_one_reflector_outcome
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 ∨
      Nonempty (OneReflectorSecondDead w N e start) ∨
      Nonempty (OneReflectorForwardDamagedCycle w N e start) := by
  rcases known_edge_N_add_six_or_one_reflector_early_outcome
      hN hentry times hlive hnd with hclosed | hdead | hdamaged
  · exact Or.inl hclosed
  · exact Or.inr (Or.inl hdead)
  · obtain ⟨D⟩ := hdamaged
    rcases D.N_add_three_or_forward hN times hlive hnd with
      hbackward | hforward
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr hforward)

/-! ## Collapsing the early-death residual

The last live prefix before a fall is more rigid than an arbitrary short
prefix.  If it repeated a switch, the trace-retaining first-revisit theorem
would expose either a stable cycle or a completed opposite reflector.  Both
outcomes are eventually periodic and therefore contradict the later fall.
-/

/-- Every finite dead run has a literal final live physical trace. -/
private theorem coeffTop_terminal_trace_of_dead
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
          obtain ⟨finish, passages, hlength, htrace, hfall⟩ :=
            ih hprev
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
        hstable, _hsimple⟩ := hcycle
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
        hactivated, hback, _hpreserves⟩ := hreflector
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
  reached : stepN w
    (A.exploration.length + A.runway.length + 1) start =
      some (e, A.activatedState)
  contact : SimpleContinuationChangedContact w A
  repaired : Tongues
  forward : contact.x = contact.oriented.2
  repair : arrive contact.nextState contact.oriented.1 =
    (contact.oriented.2, repaired)
  restored : arrive repaired contact.oriented.2 =
    (contact.oriented.1, repaired)

/-- Forget the eventual cycle: its forward first damage already has the
generic continuation certificate above. -/
def OneReflectorForwardDamagedCycle.toForwardContact
    {w : Wiring} {N e : Nat} {start : Nat × Tongues}
    (D : OneReflectorForwardDamagedCycle w N e start) :
    OneReflectorForwardContact w N e start := {
  A := D.A
  grooves := D.grooves
  base := D.base
  reached := D.reached
  contact := D.contact
  repaired := D.repaired
  forward := D.forward
  repair := D.repair
  restored := D.restored
}

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
  obtain ⟨finish, passages, _hlength, htrace, hfall⟩ :=
    coeffTop_terminal_trace_of_dead D.dead
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
  · obtain ⟨C⟩ := D.A.simpleContinuationChangedContact
      D.grooves htrace hsimple hend
    rcases C.direction with hbackward |
        ⟨hforward, repaired, hrepair, hrestored⟩
    · left
      exact C.backward_all_run_distinct_le_N_add_three
        hN D.grooves hbackward times hliveA hndA
    · right
      exact ⟨{
        A := D.A
        grooves := D.grooves
        base := D.base
        reached := D.reached
        contact := C
        repaired := repaired
        forward := hforward
        repair := hrepair
        restored := hrestored
      }⟩

/-- The entire known-edge coefficient-one assembly now has one, and only
one, explicit physical residual: a forward first damage in an arbitrary
switch-simple continuation after the first manufactured reflector. -/
theorem known_edge_N_add_six_or_forward_contact
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 ∨
      Nonempty (OneReflectorForwardContact w N e start) := by
  rcases known_edge_N_add_six_or_exact_one_reflector_outcome
      hN hentry times hlive hnd with hclosed | hdead | hcycle
  · exact Or.inl hclosed
  · obtain ⟨D⟩ := hdead
    rcases D.N_add_three_or_forward hN times hlive hnd with
      hsmall | hforward
    · exact Or.inl (by omega)
    · exact Or.inr hforward
  · obtain ⟨D⟩ := hcycle
    exact Or.inr ⟨D.toForwardContact⟩

/-! ## Generic closure of the forward-contact residual

The following argument is integrated here because `PartialContactDichotomy`
is deliberately downstream of this top-level work file.  It uses only the
arbitrary switch-simple continuation certificate above; no completed second
reflector is assumed.
-/

/-- The forward-contact splice uses only a simple partial approach.  The
completed second reflector in the older API supplied no additional dynamic
information: its only uses were simplicity of the approach and the trace to
the contact. -/
theorem partial_forward_contact_active_lead
    {w : Wiring} {g e p x : Nat} {base : Tongues}
    {A : ManufacturedReflector w g e}
    {approach suffix : List Passage} {u v : Tongues}
    {oriented : Passage} {repaired : Tongues}
    (hsimple : SwitchSimple (approach ++ (p, x) :: suffix))
    (happroach : PhysicalTrace w (e, base) approach (p, u))
    (hpaths : PathGrooves A.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3))
    (horiented : oriented ∈ A.orientedRoute u)
    (horientedGroove : arrive u oriented.2 = (oriented.1, u))
    (horientedSwitch : passageSwitch oriented = p / 3)
    (hforward : x = oriented.2)
    (hrepair : arrive v oriented.1 = (oriented.2, repaired))
    (hrestored : arrive repaired oriented.2 = (oriented.1, repaired)) :
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
      w.link mouth = some outside ∧ entry ≠ returnPort ∧
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
      stepN w (approach.length + 1) (e, base) =
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
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple hApproachSimple
  have hApproachForeign :
      ∀ passage ∈ approach, passageSwitch passage ≠ p / 3 := by
    unfold SwitchSimple at hsimple
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
    · exact reversePassages_grooved hOldPrefixGrooved passage hold
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
    have h1 := hOldBefore.sound
    have h2 := hOldPrefixData.1.sound
    rw [h2] at h1
    exact (Option.some.inj h1).symm
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
          stepN w (approach.length + 1) (e, base) =
            some (outside, flipAt u (s / 3)) := by
        rw [stepN_add, happroach.sound]
        simp only [Option.bind_some]
        rw [hone, hflip]
      have hcrossed : arrive u p = (s, flipAt u (s / 3)) := by
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

/-- A forward first-changing contact into a flip reflector has at most two
new restricted vectors after the coefficient-one contact history.  This is
the partial-continuation analogue of the completed-second-reflector theorem.
-/
theorem SimpleContinuationChangedContact.forward_flip_two_novelty
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
  have hsimple :
      SwitchSimple (C.approach ++ (C.p, C.x) :: C.suffix) := by
    rw [← C.split]
    exact C.full_simple
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, _hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach,
      _hcomplete⟩ :=
    partial_forward_contact_active_lead
      (A := ManufacturedReflector.flip R) hsimple
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

private theorem partialContact_twoPhase_concat
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

/-- A forward first-changing contact into a stay reflector is trapped in a
literal two-phase orbit. -/
theorem SimpleContinuationChangedContact.forward_stay_two_phase_tail
    {w : Wiring} {g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.stay R))
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair : arrive C.nextState C.oriented.1 =
      (C.oriented.2, repaired))
    (hrestored : arrive repaired C.oriented.2 =
      (C.oriented.1, repaired)) :
    ∃ outside mouth,
      stepN w (C.approach.length + 1)
        (e, (ManufacturedReflector.stay R).activatedState) =
          some (outside,
            flipAt C.contactState (mouth / 3)) ∧
      ∀ d, ∃ port phase,
        stepN w d
          (outside, flipAt C.contactState (mouth / 3)) =
            some (port, phase) ∧
        (phase = flipAt C.contactState (mouth / 3) ∨
          phase = C.contactState) := by
  have hsimple :
      SwitchSimple (C.approach ++ (C.p, C.x) :: C.suffix) := by
    rw [← C.split]
    exact C.full_simple
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, _hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete⟩ :=
    partial_forward_contact_active_lead
      (A := ManufacturedReflector.stay R) hsimple
      C.approach_trace C.old_grooves C.arrive_eq C.changed
      C.oriented_mem C.oriented_groove C.oriented_switch
      hforward hrepair hrestored
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
        R.suffix_after_runway_passage C.contactState hRpaths
          hsplit hmouthLink
      have hAvoid' :
          (LocalAction.flip k).Avoids D.toSupported.paths := by
        dsimp [k]
        simpa [hentryMouthSwitch] using hAvoid
      have hDalt : PathGrooves D.toSupported.paths alternate := by
        dsimp [alternate]
        exact hDpaths.after_avoiding_action hAvoid'
      let dTravel := D.toSupported.travel
      let lTravel := candy.length + 2
      have hDaltEnd :
          stepN w dTravel (outside, alternate) =
            some (mouth, alternate) := by
        dsimp [dTravel]
        exact (D.toSupported.run alternate hDalt).1
      have hDstateEnd :
          stepN w dTravel (outside, C.contactState) =
            some (mouth, C.contactState) := by
        dsimp [dTravel]
        exact (D.toSupported.run C.contactState hDpaths).1
      have hDaltPhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ := D.travel_state_stepN alternate hDalt (by
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
      have hReverseEnd :
          stepN w lTravel (mouth, alternate) =
            some (outside, C.contactState) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (mouth, alternate) =
          some (outside, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd :
          stepN w lTravel (mouth, C.contactState) =
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
        exact partialContact_twoPhase_concat
          hDaltEnd hDaltPhase hReversePhase d
          (by simpa [half] using hd)
      have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, C.contactState) = some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact partialContact_twoPhase_concat
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
        exact partialContact_twoPhase_concat
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
      have hReverseEnd :
          stepN w lTravel (R.arm, alternate) =
            some (R.arm, C.contactState) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (R.arm, alternate) =
          some (R.arm, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd :
          stepN w lTravel (R.arm, C.contactState) =
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
        exact partialContact_twoPhase_concat
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

/-- The stay-forward branch contributes no vector beyond the contact pre/post
vectors already stored in `compressedLead`. -/
theorem SimpleContinuationChangedContact.forward_stay_zero_novelty
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
theorem SimpleContinuationChangedContact.changed_two_novelty
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

/-- Absolute coefficient-one bound once a partial simple continuation first
damages the old reflector support. -/
theorem SimpleContinuationChangedContact.changed_all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
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
    C.changed_two_novelty (N := N) localTimes
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.compressedLead N) 2 := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hfirst : k ≤ firstTravel
    · unfold SimpleContinuationChangedContact.compressedLead
      apply List.mem_append_left
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
  have hlength := C.compressedLead_length_le hN hA
  omega


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
  rcases known_edge_N_add_six_or_forward_contact
      hN hentry times hlive hnd with hclosed | hforward
  · exact hclosed
  · obtain ⟨F⟩ := hforward
    have hliveA : ∀ k ∈ times,
        (stepN w k (start.1, F.A.baseState)).isSome := by
      simpa [F.base] using hlive
    have hndA : (times.map
        (restrictedTonguesAt w N
          (start.1, F.A.baseState))).Nodup := by
      simpa [F.base] using hnd
    have hfive :=
      F.contact.changed_all_run_distinct_le_N_add_five
        hN F.grooves times hliveA hndA
    omega

end GeneralN
