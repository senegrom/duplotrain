import TwoHistoryUnionCharge
import CrossingCallerSerialAssembly

/-!
# First changed support contact

This file deliberately does not use the stronger "first support contact"
hypothesis.  Earlier passages may meet an old support switch harmlessly.
Only productive first writers of the switch-simple approach are charged.

The explicit compressed lead is the first reflector's sharp core, the
productive-writer history of the approach with the common boundary erased,
and the one post-contact vector.
-/

namespace GeneralN

private theorem firstChanged_nodup_filter_nat (p : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hmem => hnd.1 ((List.mem_filter.mp hmem).1),
            ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem firstChanged_nodup_map_nat_of_injective_on
    {f : Nat → Nat} {xs : List Nat}
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs →
      f x = f y → x = y)
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

/-- Data exposed by the first *changing* support passage.  Unlike
`SecondHistorySupportContact`, the approach may contain harmless earlier
old-support passages. -/
structure FirstChangedSupportContact
    {g e : Nat} (w : Wiring)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) : Type where
  approach : List Passage
  p : Nat
  x : Nat
  suffix : List Passage
  contactState : Tongues
  nextState : Tongues
  path : List Passage
  old : Passage
  oriented : Passage
  split : B.exploration = approach ++ (p, x) :: suffix
  approach_trace :
    PhysicalTrace w (e, B.baseState) approach (p, contactState)
  suffix_trace :
    PhysicalTrace w (p, contactState) ((p, x) :: suffix) B.preReturn
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

/-- Extract the canonical first changed support contact from an outward fault.
The construction uses `first_changed_oriented`, not first support contact. -/
theorem ManufacturedReflector.OutwardSupportFault.firstChangedSupportContact
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    {after : Tongues}
    (hfault : A.OutwardSupportFault B after)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState) :
    Nonempty (FirstChangedSupportContact w A B) := by
  obtain ⟨approach, p, x, suffix, u, v, path, old, oriented,
      hsplit, happroach, hgrooves, harrive,
      hpath, hold, hswitch, hchanged,
      horiented, horientedGroove, horientedSwitch, hdirection⟩ :=
    hfault.first_changed_oriented hbaseGrooves
  have hfull := B.exploration_trace
  rw [hsplit] at hfull
  obtain ⟨middle, hprefix, htail⟩ := hfull.split_append
  have hmiddle : middle = (p, u) := by
    have h1 := hprefix.sound
    have h2 := happroach.sound
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  subst middle
  exact ⟨{
    approach := approach
    p := p
    x := x
    suffix := suffix
    contactState := u
    nextState := v
    path := path
    old := old
    oriented := oriented
    split := hsplit
    approach_trace := happroach
    suffix_trace := htail
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

/-- The strict approach is switch-simple because it is a prefix of the
second manufactured exploration. -/
theorem FirstChangedSupportContact.approach_simple
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B) :
    SwitchSimple C.approach := by
  have hs := B.exploration_simple
  unfold SwitchSimple at hs ⊢
  rw [C.split] at hs
  simp only [List.map_append, List.map_cons] at hs
  exact (List.nodup_append.mp hs).1

/-- The contact post-state is reached at the literal next time. -/
theorem FirstChangedSupportContact.post_reaches
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B) :
    ∃ q, stepN w (C.approach.length + 1) (e, B.baseState) =
      some (q, C.nextState) := by
  cases C.suffix_trace with
  | @cons _ _ q _ next _ _ harrive hlink tail =>
      have hnext : next = C.nextState := by
        rw [C.arrive_eq] at harrive
        exact (Prod.mk.inj harrive).2.symm
      subst next
      refine ⟨q, ?_⟩
      rw [stepN_add, C.approach_trace.sound]
      simp [stepN, step, C.arrive_eq, hlink]

/-- A productive writer of the simple approach survives to the contact state.
Since both the initial and contact states groove the old support, that writer
cannot be a reusable old-support coordinate.  Harmless old-support passages
are intentionally absent from this statement. -/
theorem FirstChangedSupportContact.approach_productive_writer_not_reusable
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    {k : Nat} (hk : k < C.approach.length)
    (hprod : RawProductiveAt w N (e, B.baseState) k) :
    rawWriterAt w (e, B.baseState) k ∉ A.reusableSwitches := by
  intro hreusable
  have hsurvives :=
    C.approach_trace.simple_raw_productive_writer_survives
      hN C.approach_simple hk hprod
  obtain ⟨path, hpath, old, hold, hswitch⟩ :=
    A.mem_reusableSwitches hreusable
  have hbaseOld := hbaseGrooves path hpath old hold
  have hcontactOld := C.old_grooves path hpath old hold
  have hagree :=
    grooved_states_agree_on_passage hbaseOld hcontactOld
  have hexit : old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch B.baseState old.2
    rw [hbaseOld] at hs
    exact hs.symm
  apply hsurvives
  calc
    C.contactState (rawWriterAt w (e, B.baseState) k) =
        C.contactState (old.2 / 3) := by
          rw [hexit, hswitch]
    _ = B.baseState (old.2 / 3) := hagree.symm
    _ = B.baseState (rawWriterAt w (e, B.baseState) k) := by
          rw [hexit, hswitch]

/-- Coefficient-one charge for the old reusable support and all productive
first writers before the changed contact. -/
theorem FirstChangedSupportContact.reusable_add_approach_first_writers_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState) :
    A.reusableSwitches.length +
      (rawFirstWriterTimes w N (e, B.baseState)
        C.approach.length).length ≤ N := by
  classical
  let times :=
    rawFirstWriterTimes w N (e, B.baseState) C.approach.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact firstChanged_nodup_filter_nat _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply firstChanged_nodup_map_nat_of_injective_on
    · intro i hi j hj hEq
      have hiData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hi)
      have hjData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hj)
      exact rawFirstWriterAt_injective hiData.2 hjData.2 hEq
    · exact htimesNodup
  have hdisjoint :
      ∀ oldSwitch ∈ A.reusableSwitches,
        ∀ freshSwitch ∈ writers, oldSwitch ≠ freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside :=
      C.approach_productive_writer_not_reusable
        hN hbaseGrooves hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let switches := A.reusableSwitches ++ writers
  have hnd : switches.Nodup := by
    dsimp [switches]
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  have hlt : ∀ switch ∈ switches, switch < N := by
    intro switch hswitch
    rcases List.mem_append.mp hswitch with hOld | hFresh
    · exact A.reusableSwitch_lt hN hOld
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
      have hkData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hk)
      exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hnd hlt
  have hlength :
      A.reusableSwitches.length + times.length ≤ N := by
    simpa [switches, writers] using hbound
  simpa [times] using hlength

/-- Explicit coefficient-one lead through the first changed support passage.
The final singleton is the changed contact's post-vector. -/
noncomputable def FirstChangedSupportContact.compressedLead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B) (N : Nat) :
    List (List Bool) :=
  A.sharpHistoryCore N ++
    ((rawFirstWriterHistory w N (e, B.baseState)
      C.approach.length).erase
        (VectorCount.restrict N A.activatedState) ++
      [VectorCount.restrict N C.nextState])

/-- The explicit compressed lead has size at most N+3. -/
theorem FirstChangedSupportContact.compressedLead_length_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState) :
    (C.compressedLead N).length ≤ N + 3 := by
  have hboundary :
      VectorCount.restrict N A.activatedState ∈
        rawFirstWriterHistory w N (e, B.baseState)
          C.approach.length := by
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    C.reusable_add_approach_first_writers_le hN hbaseGrooves
  have houter := A.exploration_length_le_reusable_add_one
  have hraw :
      (rawFirstWriterHistory w N (e, B.baseState)
        C.approach.length).length =
          (rawFirstWriterTimes w N (e, B.baseState)
            C.approach.length).length + 1 := by
    simp [rawFirstWriterHistory]
  have herase :
      ((rawFirstWriterHistory w N (e, B.baseState)
        C.approach.length).erase
          (VectorCount.restrict N A.activatedState)).length =
        (rawFirstWriterTimes w N (e, B.baseState)
          C.approach.length).length := by
    rw [List.length_erase_of_mem hboundary, hraw]
    omega
  unfold FirstChangedSupportContact.compressedLead
  rw [List.length_append, List.length_append, herase,
    A.sharpHistoryCore_length]
  simp only [List.length_singleton]
  omega

/-- Every state through the contact pre-state belongs to the compressed lead. -/
theorem FirstChangedSupportContact.mem_compressedLead_of_approach
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B)
    {j : Nat} (hj : j ≤ C.approach.length) :
    restrictedTonguesAt w N (e, B.baseState) j ∈
      C.compressedLead N := by
  classical
  have hm :=
    PhysicalTrace.restrictedTonguesAt_mem_rawFirstWriterHistory
      (N := N) C.approach_trace C.approach_simple j hj
  by_cases hboundary :
      restrictedTonguesAt w N (e, B.baseState) j =
        VectorCount.restrict N A.activatedState
  · apply List.mem_append_left
    rw [hboundary]
    exact A.activated_mem_sharpHistoryCore
  · apply List.mem_append_right
    apply List.mem_append_left
    exact (List.mem_erase_of_ne hboundary).mpr hm

/-- The changed contact post-vector is explicitly present in the lead. -/
theorem FirstChangedSupportContact.next_mem_compressedLead
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B) :
    VectorCount.restrict N C.nextState ∈ C.compressedLead N := by
  apply List.mem_append_right
  apply List.mem_append_right
  simp

/-- The contact pre-vector is represented by the approach endpoint. -/
theorem FirstChangedSupportContact.contact_mem_compressedLead
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B) :
    VectorCount.restrict N C.contactState ∈ C.compressedLead N := by
  have hm := C.mem_compressedLead_of_approach
    (N := N) (j := C.approach.length) (Nat.le_refl _)
  simpa [restrictedTonguesAt, tonguesAt,
    C.approach_trace.sound] using hm


/-- Backward orientation is the old theta lasso. Earlier harmless overlaps
in the approach do not matter: switch simplicity excludes only the changing
contact switch, which is exactly what replay after the flip requires. Both
tail phases are already in the compressed lead, so the novelty budget is
zero. -/
theorem FirstChangedSupportContact.backward_all_time_zero_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B)
    (hbackward : C.x = C.oriented.1)
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
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
    have hs := B.exploration_simple
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
      C.nextState =
        flipAt C.contactState (C.p / 3) :=
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
      stepN w K (e, B.baseState) =
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
        stepN w j (e, B.baseState) = some (port, phase) := by
      rw [hjEq, stepN_add, hreach]
      exact hrun
    have hvector :
        restrictedTonguesAt w N (e, B.baseState) j =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [h] using C.contact_mem_compressedLead (N := N)
    · simpa [h] using C.next_mem_compressedLead (N := N)


/-- Package the forward half of the orientation dichotomy as the raw
`ForwardOrientedFault` consumed by the splice theorem. -/
theorem FirstChangedSupportContact.forwardOrientedFault
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B)
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 =
        (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 =
        (C.oriented.1, repaired)) :
    A.ForwardOrientedFault B := by
  exact ⟨C.approach, C.p, C.x, C.suffix,
    C.contactState, C.nextState, C.oriented, repaired,
    C.split, C.approach_trace, C.old_grooves,
    C.arrive_eq, C.changed, C.oriented_mem,
    C.oriented_groove, C.oriented_switch,
    hforward, hrepair, hrestored⟩

/-- The first changed forward contact therefore produces the canonical
spliced lobe even when its approach had harmless old-support overlaps. -/
theorem FirstChangedSupportContact.forward_spliced_lobe_reflector
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B)
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 =
        (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 =
        (C.oriented.1, repaired)) :
    ∃ mouth outside candy state tailSteps,
      IsReflector w mouth outside (candy.length + 2)
        (fun state => PassagesGrooved state candy)
        (fun state => flipAt state (mouth / 3)) ∧
      stepN w tailSteps (outside, state) =
        some (e, A.toSupported.action.apply state) :=
  ManufacturedReflector.ForwardOrientedFault.spliced_lobe_reflector
    (C.forwardOrientedFault hforward hrepair hrestored)

/-- For a flip old reflector, the quantitative splice theorem leaves at most
two nonhistorical Gray corners. Its lead hypotheses are discharged by the
explicit compressed lead, including the literal post-contact vector. -/
theorem FirstChangedSupportContact.forward_flip_all_time_two_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w
      (ManufacturedReflector.flip R) B)
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 =
        (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 =
        (C.oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
      times (C.compressedLead N) 2 := by
  have _hcanonicalSplice :=
    C.forward_spliced_lobe_reflector
      hforward hrepair hrestored
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach,
      _hcomplete⟩ :=
    first_forward_contact_active_lead_two_history
      (A := ManufacturedReflector.flip R)
      C.split C.approach_trace C.old_grooves
      C.arrive_eq C.changed C.oriented_mem C.oriented_groove
      C.oriented_switch hforward hrepair hrestored
  let K := C.approach.length + 1
  let state := C.contactState
  let alternate := flipAt state (mouth / 3)
  have hreach' :
      stepN w K (e, B.baseState) =
        some (outside, alternate) := by
    simpa [K, state, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.compressedLead N := by
    simpa [hnextAlternate] using
      C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N state ∈ C.compressedLead N := by
    simpa [state] using C.contact_mem_compressedLead (N := N)
  have hleadHistorical : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N (e, B.baseState) j ∈
        C.compressedLead N := by
    intro j _hj hjK
    exact C.mem_compressedLead_of_approach (N := N) (by
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
      have hheadGroove :
          arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch state entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe : mouth / 3 ≠ D.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsD :
        (LocalAction.flip (mouth / 3)).Avoids
          D.toSupported.paths := by
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
    have hentryGrooved :
        arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved hApproachReplay
      hApproachGrooved hApproachForeign hcrossed hmouthLink harms
      hreach' N (C.compressedLead N) hentryHistorical times
      hleadHistorical
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩


private theorem firstChanged_twoPhase_concat
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

/-- Exact two-phase tail for a first changed forward contact into a stay
reflector. This is the quantitative content of the spliced lobe, with no
first-support-freshness premise. -/
theorem FirstChangedSupportContact.forward_stay_two_phase_tail
    {w : Wiring} {g e : Nat}
    {R : ManufacturedStayReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w
      (ManufacturedReflector.stay R) B)
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 =
        (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 =
        (C.oriented.1, repaired)) :
    ∃ outside mouth,
      stepN w (C.approach.length + 1) (e, B.baseState) =
        some (outside,
          flipAt C.contactState (mouth / 3)) ∧
      ∀ d, ∃ port phase,
        stepN w d
          (outside, flipAt C.contactState (mouth / 3)) =
            some (port, phase) ∧
        (phase = flipAt C.contactState (mouth / 3) ∨
          phase = C.contactState) := by
  have _hcanonicalSplice :=
    C.forward_spliced_lobe_reflector
      hforward hrepair hrestored
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete⟩ :=
    first_forward_contact_active_lead_two_history
      (A := ManufacturedReflector.stay R)
      C.split C.approach_trace C.old_grooves
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
    (ManufacturedReflector.stay R).orientedRoute_simple
      C.contactState
  have hOldGrooved :=
    hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward :
      arrive C.contactState entry =
        (mouth, C.contactState) :=
    groove_forward (hOldGrooved (entry, mouth) hentryOld)
  have hentryMouthSwitch : entry / 3 = mouth / 3 := by
    have hswitch := arrive_exit_switch C.contactState entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  have hallAfter : ∀ d, ∃ port phase,
      stepN w d (outside, alternate) =
        some (port, phase) ∧
      (phase = alternate ∨ phase = C.contactState) := by
    change (entry, mouth) ∈
      R.runway ++ [(R.mouth, R.arm)] at hentryOld
    rcases List.mem_append.mp hentryOld with hrunway | hcore
    · obtain ⟨before, after, hsplit⟩ :=
        List.append_of_mem hrunway
      obtain ⟨D, hDpaths, hAvoid⟩ :=
        R.suffix_after_runway_passage
          C.contactState hRpaths hsplit hmouthLink
      have hAvoid' :
          (LocalAction.flip k).Avoids D.toSupported.paths := by
        dsimp [k]
        simpa [hentryMouthSwitch] using hAvoid
      have hDalt :
          PathGrooves D.toSupported.paths alternate := by
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
          stepN w d (outside, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          D.travel_state_stepN alternate hDalt (by
            simpa [dTravel, ManufacturedReflector.toSupported,
              ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, alternate, hrun, Or.inl rfl⟩
      have hDstatePhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (outside, C.contactState) =
            some (port, phase) ∧
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
          stepN w d (mouth, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, C.contactState) =
            some (port, phase) ∧
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
      have hHalfAlt :
          stepN w half (outside, alternate) =
            some (outside, C.contactState) := by
        dsimp [half]
        rw [stepN_add, hDaltEnd]
        exact hReverseEnd
      have hHalfState :
          stepN w half (outside, C.contactState) =
            some (outside, alternate) := by
        dsimp [half]
        rw [stepN_add, hDstateEnd]
        exact hForwardEnd
      have hHalfAltPhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact firstChanged_twoPhase_concat
          hDaltEnd hDaltPhase hReversePhase d
          (by simpa [half] using hd)
      have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, C.contactState) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact firstChanged_twoPhase_concat
          hDstateEnd hDstatePhase hForwardPhase d
          (by simpa [half] using hd)
      let period := half + half
      have hperiod :
          stepN w period (outside, alternate) =
            some (outside, alternate) := by
        dsimp [period]
        rw [stepN_add, hHalfAlt]
        exact hHalfState
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (outside, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact firstChanged_twoPhase_concat
          hHalfAlt hHalfAltPhase hHalfStatePhase d
          (by simpa [period] using hd)
      have hpositive : 0 < period := by
        have hdpos := (ManufacturedReflector.stay D).travel_pos
        dsimp [period, half, dTravel, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow
    · simp only [List.mem_singleton] at hcore
      have hentryEq : entry = R.mouth :=
        congrArg Prod.fst hcore
      have hmouthEq : mouth = R.arm :=
        congrArg Prod.snd hcore
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
          stepN w d (R.arm, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, C.contactState) =
            some (port, phase) ∧
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
      have hperiod :
          stepN w period (R.arm, alternate) =
            some (R.arm, alternate) := by
        dsimp [period]
        rw [stepN_add, hReverseEnd]
        exact hForwardEnd
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (R.arm, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact firstChanged_twoPhase_concat
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

/-- The stay branch has zero post-lead novelty: both all-time phases are the
contact pre-vector and the explicitly stored post-vector. -/
theorem FirstChangedSupportContact.forward_stay_all_time_zero_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedStayReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w
      (ManufacturedReflector.stay R) B)
    {repaired : Tongues}
    (hforward : C.x = C.oriented.2)
    (hrepair :
      arrive C.nextState C.oriented.1 =
        (C.oriented.2, repaired))
    (hrestored :
      arrive repaired C.oriented.2 =
        (C.oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
      times (C.compressedLead N) 0 := by
  obtain ⟨outside, mouth, hreach, hall⟩ :=
    C.forward_stay_two_phase_tail
      hforward hrepair hrestored
  let K := C.approach.length + 1
  let alternate := flipAt C.contactState (mouth / 3)
  have hreach' :
      stepN w K (e, B.baseState) =
        some (outside, alternate) := by
    simpa [K, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.compressedLead N := by
    simpa [hnextAlternate] using
      C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N C.contactState ∈
        C.compressedLead N :=
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
    have hglobal :
        stepN w j (e, B.baseState) =
          some (port, phase) := by
      rw [hjEq, stepN_add, hreach']
      exact hrun
    have hvector :
        restrictedTonguesAt w N (e, B.baseState) j =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [alternate, h] using hentryHistorical
    · simpa [h] using hstateHistorical


/-- Unified orientation theorem. Backward and stay-forward contacts use no
new vector; a flip-forward contact uses at most the two quantitative splice
corners. -/
theorem FirstChangedSupportContact.changed_all_time_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : FirstChangedSupportContact w A B)
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
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
          C.forward_stay_all_time_zero_novelty
            hforward hrepair hrestored times
        exact ⟨fresh, by omega, hmem⟩
    | flip R =>
        exact C.forward_flip_all_time_two_novelty
          hforward hrepair hrestored times

/-- **First-changed-support tail package.**

For the canonical first passage that actually damages the old support, there
is an explicit compressed lead of size at most `N+3`. Every requested time
on the entire second run is covered by that lead plus at most two vectors.
Harmless earlier old-support overlaps consume neither a coordinate charge nor
a novelty slot. -/
theorem ManufacturedReflector.OutwardSupportFault.first_changed_compressed_tail
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    {after : Tongues}
    (hfault : A.OutwardSupportFault B after)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState) :
    ∃ C : FirstChangedSupportContact w A B,
      (C.compressedLead N).length ≤ N + 3 ∧
      ∀ times : List Nat,
        NoveltyCoverOn w N (e, B.baseState)
          times (C.compressedLead N) 2 := by
  let C := Classical.choice
    (hfault.firstChangedSupportContact hbaseGrooves)
  refine ⟨C, C.compressedLead_length_le
    hN hbase hbaseGrooves, ?_⟩
  intro times
  exact C.changed_all_time_two_novelty times

/-- Direct duplicate-free count supplied by the first-changed package. The
proved constant is `N+5`, one better than the `N+6` assembly target. -/
theorem ManufacturedReflector.OutwardSupportFault.first_changed_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    {after : Tongues}
    (hfault : A.OutwardSupportFault B after)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (e, B.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  obtain ⟨C, hlead, hcover⟩ :=
    hfault.first_changed_compressed_tail
      hN hbase hbaseGrooves
  have hcount :=
    noveltyCoverOn_distinct_count (hcover times) hnd
  omega

/-- The exact form needed by an `A.sharpHistoryCore`-based `N+6`
assembly. -/
theorem ManufacturedReflector.OutwardSupportFault.first_changed_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    {after : Tongues}
    (hfault : A.OutwardSupportFault B after)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (e, B.baseState))).Nodup) :
    times.length ≤ N + 6 := by
  have hfive :=
    hfault.first_changed_distinct_le_N_add_five
      hN hbase hbaseGrooves times hnd
  omega

end GeneralN
