import OneReflectorContinuation
import FirstChangedSupportTail
import OldContactContinuation

/-!
# A damaging support contact in an unfinished continuation

The older first-changed-support package was indexed by a completed second
`ManufacturedReflector`.  An unfinished second probe has no such object.  This
file retains only the data actually supplied by an arbitrary switch-simple
`PhysicalTrace` after the first reflector.

The strict approach to the first damaging passage shares one coefficient-one
switch budget with the first reflector.  Its compressed history, including
the post-contact vector, therefore has length at most `N + 3`.

The contact itself has the exact dynamic dichotomy supplied by the raw track
semantics: it either closes a backward periodic lasso, or is a forward
self-repairing passage.  The backward branch is counted outright.  A separate
theorem counts the whole run by `N + 4` whenever the post-contact configuration
already feeds a one-vector tail.
-/

namespace GeneralN

/-- The first passage of an arbitrary switch-simple continuation which
damages a groove supported by the already manufactured reflector `A`.

Unlike `FirstChangedSupportContact`, this record has no completed second
reflector parameter. -/
structure PartialSupportDamage
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

/-- Extract the canonical first damaging support passage from an arbitrary
switch-simple continuation. -/
theorem ManufacturedReflector.partialSupportDamage
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w (e, A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    (hbroken : ¬ PathGrooves A.toSupported.paths finish.2) :
    Nonempty (PartialSupportDamage w A) := by
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

theorem PartialSupportDamage.approach_simple
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A) :
    SwitchSimple C.approach := by
  have hs := C.full_simple
  unfold SwitchSimple at hs ⊢
  rw [C.split] at hs
  simp only [List.map_append, List.map_cons] at hs
  exact (List.nodup_append.mp hs).1

/-- The approach together with the damaging passage is still switch-simple. -/
theorem PartialSupportDamage.approach_contact_simple
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A) :
    SwitchSimple (C.approach ++ [(C.p, C.x)]) := by
  have hs := C.full_simple
  unfold SwitchSimple at hs ⊢
  rw [C.split] at hs
  simp only [List.map_append, List.map_cons] at hs ⊢
  have hparts := List.nodup_append.mp hs
  apply List.nodup_append.mpr
  refine ⟨hparts.1, by simp, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_cons, List.map_nil, List.not_mem_nil, or_false] at hb
  apply hparts.2.2 a ha (passageSwitch (C.p, C.x)) (by simp)
  exact hab.trans hb

/-- The post-contact state is reached at the literal next time. -/
theorem PartialSupportDamage.post_reaches
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A) :
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

/-- The coefficient-one history through the damaging passage. -/
noncomputable def PartialSupportDamage.compressedLead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A) (N : Nat) :
    List (List Bool) :=
  A.continuationHistory N (e, A.activatedState) C.approach.length ++
    [VectorCount.restrict N C.nextState]

/-- The first reflector, every productive first writer in the strict
approach, and the post-contact vector use at most `N + 3` history slots. -/
theorem PartialSupportDamage.compressedLead_length_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState) :
    (C.compressedLead N).length ≤ N + 3 := by
  have hbase := A.continuationHistory_length_le
    hN (start := (e, A.activatedState))
      (finish := (C.p, C.contactState))
      (passages := C.approach)
      rfl C.approach_trace C.approach_simple hA C.old_grooves
  unfold PartialSupportDamage.compressedLead
  simp only [List.length_append, List.length_singleton]
  omega

theorem PartialSupportDamage.mem_compressedLead_of_approach
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A)
    {j : Nat} (hj : j ≤ C.approach.length) :
    restrictedTonguesAt w N (e, A.activatedState) j ∈
      C.compressedLead N := by
  apply List.mem_append_left
  exact A.mem_continuationHistory
    (N := N) (finish := (C.p, C.contactState))
      (passages := C.approach)
      C.approach_trace C.approach_simple hj

theorem PartialSupportDamage.contact_mem_compressedLead
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A) :
    VectorCount.restrict N C.contactState ∈ C.compressedLead N := by
  have hm := C.mem_compressedLead_of_approach
    (N := N) (j := C.approach.length) (Nat.le_refl _)
  simpa [restrictedTonguesAt, tonguesAt,
    C.approach_trace.sound] using hm

theorem PartialSupportDamage.next_mem_compressedLead
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A) :
    VectorCount.restrict N C.nextState ∈ C.compressedLead N := by
  apply List.mem_append_right
  simp

/-- The exact contact dichotomy for a partial trace.  No completed second
reflector occurs in either the statement or the proof. -/
theorem PartialSupportDamage.periodic_or_forward
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A) :
    EventuallyPeriodic w (e, A.activatedState) ∨
      ∃ oriented repaired,
        oriented ∈ A.orientedRoute C.contactState ∧
        arrive C.contactState oriented.2 =
          (oriented.1, C.contactState) ∧
        passageSwitch oriented = C.p / 3 ∧
        C.x = oriented.2 ∧
        arrive C.nextState oriented.1 =
          (oriented.2, repaired) ∧
        arrive repaired oriented.2 = (oriented.1, repaired) := by
  exact A.protected_changed_contact_periodic_or_forward
    (route := C.approach ++ [(C.p, C.x)])
    (approach := C.approach) (suffix := [])
    (by simp) C.approach_contact_simple C.approach_trace
      C.old_grooves C.arrive_eq C.path_mem C.old_mem
      C.old_switch C.changed

/-- In the backward orientation, every later tongue vector is one of the
two contact vectors already stored in the compressed lead. -/
theorem PartialSupportDamage.backward_all_time_zero_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A)
    (hbackward : C.x = C.oriented.1)
    (times : List Nat) :
    NoveltyCoverOn w N (e, A.activatedState)
      times (C.compressedLead N) 0 := by
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
  have hcontact :
      arrive C.contactState C.p = (C.oriented.1, C.nextState) := by
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
  · exact C.mem_compressedLead_of_approach (N := N) (by
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
    · simpa [h] using C.contact_mem_compressedLead (N := N)
    · simpa [h] using C.next_mem_compressedLead (N := N)

/-- Absolute coefficient-one count for the backward damaging-contact branch. -/
theorem PartialSupportDamage.backward_all_run_distinct_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A)
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
    simpa [firstTravel] using A.manufacturing_journey_reaches_activated hA
  obtain ⟨fresh, hfresh, hlocal⟩ :=
    C.backward_all_time_zero_novelty (N := N) hbackward localTimes
  have hfreshNil : fresh = [] := by
    cases fresh with
    | nil => rfl
    | cons x xs =>
        simp only [List.length_cons] at hfresh
        omega
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.compressedLead N) 0 := by
    refine ⟨[], by simp, ?_⟩
    intro k hk
    simp only [List.append_nil]
    by_cases hfirst : k ≤ firstTravel
    · apply List.mem_append_left
      apply List.mem_append_left
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

/-- If the post-contact configuration already feeds a one-vector positive
tail, the entire original run has at most `N + 4` distinct tongue vectors.
This is the exact bridge to a settled simple-cycle tail; the remaining open
forward case is obtaining such a tail without paying for an uncharged finite
residual prefix. -/
theorem PartialSupportDamage.one_vector_tail_all_run_distinct_le_N_add_four
    {w : Wiring} {N g e q : Nat}
    (hN : ∀ p r, w.link p = some r → p < 3 * N ∧ r < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : PartialSupportDamage w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hpost : stepN w (C.approach.length + 1)
      (e, A.activatedState) = some (q, C.nextState))
    {settled : Tongues}
    (htail : ∀ d, 0 < d → ∃ port,
      stepN w d (q, C.nextState) = some (port, settled))
    (times : List Nat)
    (_hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 4 := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localStart : Nat × Tongues := (e, A.activatedState)
  let K := C.approach.length + 1
  let history := C.compressedLead N
  let settledVector := VectorCount.restrict N settled
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some localStart := by
    simpa [firstTravel, localStart] using
      A.manufacturing_journey_reaches_activated hA
  have hpost' : stepN w K localStart =
      some (q, C.nextState) := by
    simpa [K, localStart] using hpost
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times history 1 := by
    refine ⟨[settledVector], by simp, ?_⟩
    intro k _hk
    by_cases hfirst : k ≤ firstTravel
    · apply List.mem_append_left
      dsimp [history]
      apply List.mem_append_left
      apply List.mem_append_left
      apply A.mem_sharpHistoryCore_of_mem
      exact A.manufacturing_journey_mem_sharpHistory hA (by
        simpa [firstTravel] using hfirst)
    · let d := k - firstTravel
      have hkEq : k = firstTravel + d := by
        dsimp [d]
        omega
      by_cases happroach : d ≤ C.approach.length
      · obtain ⟨middle, hlocal⟩ :=
          stepN_prefix_some happroach C.approach_trace.sound
        have hglobal : stepN w k (g, A.baseState) = some middle := by
          rw [hkEq, stepN_add, hreachA]
          exact hlocal
        have hlocal' : stepN w d localStart = some middle := by
          simpa [localStart] using hlocal
        have hvector : restrictedTonguesAt w N (g, A.baseState) k =
            restrictedTonguesAt w N localStart d := by
          simp [restrictedTonguesAt, tonguesAt, hglobal, hlocal']
        apply List.mem_append_left
        dsimp [history]
        rw [hvector]
        exact C.mem_compressedLead_of_approach happroach
      · by_cases hcontact : d = K
        · have hglobal : stepN w k (g, A.baseState) =
              some (q, C.nextState) := by
            rw [hkEq, hcontact, stepN_add, hreachA]
            exact hpost'
          have hvector : restrictedTonguesAt w N (g, A.baseState) k =
              VectorCount.restrict N C.nextState := by
            simp [restrictedTonguesAt, tonguesAt, hglobal]
          apply List.mem_append_left
          dsimp [history]
          rw [hvector]
          exact C.next_mem_compressedLead
        · let r := d - K
          have hr : 0 < r := by
            dsimp [r, K] at ⊢
            omega
          have hdEq : d = K + r := by
            dsimp [r]
            omega
          obtain ⟨port, hrun⟩ := htail r hr
          have hlocal : stepN w d localStart = some (port, settled) := by
            rw [hdEq, stepN_add, hpost']
            exact hrun
          have hglobal : stepN w k (g, A.baseState) =
              some (port, settled) := by
            rw [hkEq, stepN_add, hreachA]
            exact hlocal
          have hvector : restrictedTonguesAt w N (g, A.baseState) k =
              settledVector := by
            simp [restrictedTonguesAt, tonguesAt, hglobal, settledVector]
          apply List.mem_append_right
          simp [hvector]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength := C.compressedLead_length_le hN hA
  dsimp [history] at hcount
  omega

end GeneralN
