import MellitDirectSharpAssembly
import NoveltyChargeBound
import FirstCycleCountSharp

/-!
# Dynamic residual refinement for the direct Mellit assembly

This file retains the immediate two-phase cycle produced by the canonical
union-first-repeat construction. The older `UnionFreshSimpleCycle` stores
only `SettlesOnSimpleCycle`; that eventual-cycle proposition is insufficient
for sharp repeated-writer accounting because it forgets the physical first
lap which produced it.

`GeneralN.StateLaw` remains open.  This file isolates, without assuming, the
remaining dynamic old-contact continuation.
-/

namespace GeneralN

/-! ## Exact immediate cycle certificate -/

/-- The immediate two-phase cycle produced by a concrete first revisit.
Unlike `SettlesOnSimpleCycle`, this retains the transient lap, the stable
lap, switch simplicity, and the exact two-state phase law. -/
structure DynamicReachedSimpleCycle
    (w : Wiring) (atRepeat : Nat × Tongues) : Type where
  cycle : List Passage
  settled : Tongues
  nonempty : cycle ≠ []
  transient :
    PhysicalTrace w atRepeat cycle (atRepeat.1, settled)
  stable :
    PhysicalTrace w (atRepeat.1, settled) cycle
      (atRepeat.1, settled)
  simple : SwitchSimple cycle
  phase :
    ∀ d, d ≤ cycle.length → ∃ port state,
      stepN w d atRepeat = some (port, state) ∧
        (state = atRepeat.2 ∨ state = settled)

/-- First-revisit extraction retaining both exact reflector support and the
immediate two-phase cycle. -/
private theorem first_revisit_cycle_phase_or_activated_dynamic_exact
    (w : Wiring) {start : Nat × Tongues}
    {runway path : List Passage}
    {p x q y e : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hsw : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v))
    (hentry : w.link e = some start.1) :
    Nonempty (DynamicReachedSimpleCycle w (q, u)) ∨
      Nonempty
        (ExactActivatedFirstRevisit
          w start runway path p x q e u) := by
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
    have hgrooved :=
      hexcursion.grooved_of_switchSimple hsimpleExcursion
    have hstable :
        PhysicalTrace w (p, u) ((p, x) :: path) (p, u) :=
      physicalTrace_grooved_passages w u p x p path
        hexcursion.linked hgrooved hexcursion.last_link
    have hphase :
        ∀ d, d ≤ ((p, x) :: path).length → ∃ port state,
          stepN w d (p, u) = some (port, state) ∧
            (state = u ∨ state = u) := by
      intro d hd
      obtain ⟨port, hrun⟩ :=
        hstable.grooved_prefix_tongues u hgrooved hd
      exact ⟨port, u, hrun, Or.inl rfl⟩
    exact ⟨{
      cycle := (p, x) :: path
      settled := u
      nonempty := by simp
      transient := hstable
      stable := hstable
      simple := hsimpleExcursion
      phase := hphase
    }⟩
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
      right
      refine ⟨{
        reflector := .stay A
        state := u
        paths := ?_
        base := rfl
        activated := rfl
        back := hback
        preserves := ?_
        exploration_eq := ?_
      }⟩
      · change PathGrooves [runway, [(p, x)]] u
        apply pathGrooves_pair.mpr
        exact ⟨(pathGrooves_pair.mp hsupport).1,
          passagesGrooved_singleton.mpr holdGroove⟩
      · simpa [ManufacturedReflector.exploration] using hpreserves
      · rfl
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
      right
      refine ⟨{
        reflector := .flip A
        state := v
        paths := hsupport
        base := rfl
        activated := rfl
        back := hback
        preserves := ?_
        exploration_eq := ?_
      }⟩
      · simpa [ManufacturedReflector.exploration] using hpreserves
      · rfl
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
    right
    refine ⟨{
      reflector := .stay A
      state := u
      paths := ?_
      base := rfl
      activated := rfl
      back := hback
      preserves := ?_
      exploration_eq := ?_
    }⟩
    · change PathGrooves [runway, [(p, x)]] u
      apply pathGrooves_pair.mpr
      exact ⟨(pathGrooves_pair.mp hsupport).1,
        passagesGrooved_singleton.mpr holdGroove⟩
    · simpa [ManufacturedReflector.exploration] using hpreserves
    · rfl
  · subst y
    left
    obtain ⟨htransient, hstable, hsimpleCycle, hphase⟩ :=
      hexcursion.simple_same_exit_cycle_traces_with_phase
        hsimpleExcursion hrepeat
    exact ⟨{
      cycle := (q, x) :: path
      settled := v
      nonempty := by simp
      transient := htransient
      stable := hstable
      simple := hsimpleCycle
      phase := hphase
    }⟩

/-! ## Exact lifting of the internal union repeat -/

/-- The exact first-lap cycle branch of an internal union repeat. -/
structure DynamicUnionInternalCycleResult
    (w : Wiring) (start : Nat × Tongues)
    (before : List Passage) : Type where
  atRepeat : Nat × Tongues
  prefixTrace : PhysicalTrace w start before atRepeat
  reached : stepN w before.length start = some atRepeat
  cycle : DynamicReachedSimpleCycle w atRepeat

/-- The internal union-repeat fork with no loss of cycle data. -/
private theorem PhysicalTrace.internal_union_repeat_dynamic_exact
    {w : Wiring} {old fresh : List Passage}
    {start finish : Nat × Tongues} {entryEdge : Nat}
    (htrace : PhysicalTrace w start fresh finish)
    (R : UnionFirstRepeat old fresh)
    (hinternal :
      passageSwitch R.repeated ∈
        R.before.map passageSwitch)
    (hentry : w.link entryEdge = some start.1) :
    Nonempty
        (DynamicUnionInternalCycleResult w start R.before) ∨
      Nonempty
        (UnionInternalReflectorResult
          w start R.before entryEdge) := by
  rcases R with
    ⟨before, repeated, after, hsplit, hcombined, hrepeats⟩
  change passageSwitch repeated ∈
    before.map passageSwitch at hinternal
  change
    Nonempty (DynamicUnionInternalCycleResult w start before) ∨
      Nonempty (UnionInternalReflectorResult w start before entryEdge)
  have htraceSplit := htrace
  rw [hsplit] at htraceSplit
  obtain ⟨atRepeat, hbeforeTrace, hafterTrace⟩ :=
    htraceSplit.split_append
  have hreached :
      stepN w before.length start = some atRepeat :=
    hbeforeTrace.sound
  obtain ⟨oldPassage, hold, hsameSwitch⟩ :=
    List.mem_map.mp hinternal
  obtain ⟨runway, path, hbeforeSplit⟩ :=
    List.append_of_mem hold
  have hbeforeSimple : SwitchSimple before := by
    unfold SwitchSimple at hcombined ⊢
    rw [List.map_append] at hcombined
    exact (List.nodup_append.mp hcombined).2.1
  rw [hbeforeSplit] at hbeforeTrace
  obtain ⟨atOld, hrunway, hexcursion⟩ :=
    hbeforeTrace.split_append
  rcases oldPassage with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  have hatOldPort : atOld.1 = p :=
    hexcursion.head_arrive.1
  rcases atOld with ⟨oldPort, u₀⟩
  simp only at hatOldPort
  subst oldPort
  have hatRepeatPort : atRepeat.1 = q :=
    hafterTrace.head_arrive.1
  rcases atRepeat with ⟨repeatPort, u⟩
  simp only at hatRepeatPort
  subst repeatPort
  obtain ⟨v, hrepeat⟩ :=
    hafterTrace.head_arrive.2
  have hsimple :
      SwitchSimple (runway ++ (p, x) :: path) := by
    simpa [hbeforeSplit] using hbeforeSimple
  have hswitch : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  have hout := first_revisit_cycle_phase_or_activated_dynamic_exact w
    hrunway hexcursion hsimple hswitch hrepeat hentry
  rcases hout with hcycle | hreflector
  · left
    obtain ⟨cycle⟩ := hcycle
    exact ⟨{
      atRepeat := (q, u)
      prefixTrace := by
        simpa [hbeforeSplit] using hbeforeTrace
      reached := by simpa using hreached
      cycle := cycle
    }⟩
  · right
    obtain ⟨E⟩ := hreflector
    refine ⟨{
      atRepeat := (q, u)
      reached := by simpa using hreached
      reflector := E.reflector
      state := E.state
      backSteps := runway.length + 1
      paths := E.paths
      base := E.base
      activated := E.activated
      back := E.back
      preserves := ?_
      exploration_eq := ?_
    }⟩
    · intro j hj
      apply E.preserves j
      simpa [hbeforeSplit] using hj
    · exact E.exploration_eq.trans hbeforeSplit.symm

/-- The internal branch retaining the immediate two-phase cycle. -/
structure UnionFreshDynamicCycle
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (fresh : List Passage) : Type where
  selection : UnionFirstRepeat A.exploration fresh
  internal :
    passageSwitch selection.repeated ∈
      selection.before.map passageSwitch
  result :
    DynamicUnionInternalCycleResult
      w (e, A.activatedState) selection.before

/-- Exact agreement outside a switch-disjoint second exploration preserves
all grooves of the old reflector. -/
private theorem dynamic_old_support_grooves
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (before after : Tongues)
    (hpaths : PathGrooves A.toSupported.paths before)
    (hsimple : SwitchSimple (A.exploration ++ B.exploration))
    (hpreserves :
      ∀ j, j ∉ B.exploration.map passageSwitch →
        after j = before j) :
    PathGrooves A.toSupported.paths after := by
  intro path hpath passage hpassage
  have hgroove := hpaths path hpath passage hpassage
  apply groove_transfer hgroove
  have hexit :
      passage.2 / 3 = passageSwitch passage := by
    have hs := arrive_exit_switch before passage.2
    rw [hgroove] at hs
    exact hs.symm
  rw [hexit]
  apply hpreserves
  intro hBmem
  have hAmem :=
    A.support_switch_mem_exploration hpath hpassage
  unfold SwitchSimple at hsimple
  rw [List.map_append] at hsimple
  have hcross := (List.nodup_append.mp hsimple).2.2
  exact (hcross (passageSwitch passage) hAmem
    (passageSwitch passage) hBmem) rfl

/-- **Exact direct trichotomy.** The non-old-contact cycle branch now
retains its physical transient/stable laps and two-state phase law. -/
theorem ManufacturedReflector.union_first_contact_shrinks_or_dynamic_cycle_or_compatible
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage}
    {finish : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hApaths :
      PathGrooves A.toSupported.paths A.activatedState)
    (htrace :
      PhysicalTrace w (e, A.activatedState) fresh finish)
    (hnonsimple :
      ¬ SwitchSimple (A.exploration ++ fresh)) :
    Nonempty (UnionOldTrackedShrink w N A fresh finish) ∨
      Nonempty (UnionFreshDynamicCycle A fresh) ∨
      Nonempty (UnionFreshCompatiblePair A fresh) := by
  obtain ⟨R⟩ := first_repeat_against_union
    A.exploration fresh A.exploration_simple hnonsimple
  rcases R.old_or_internal with hold | hinternal
  · left
    have hRange :
        ∀ passage, passage ∈ A.exploration →
          passageSwitch passage < N := by
      intro passage hpassage
      exact A.exploration_trace.switch_lt
        hN passage hpassage
    obtain ⟨S⟩ := htrace.union_old_contact_shrink
      R hRange hold
    exact ⟨{
      selection := R
      raw := S
    }⟩
  · have hout := htrace.internal_union_repeat_dynamic_exact
      R hinternal (w.symm _ _ A.entryEdge)
    rcases hout with hcycle | hreflector
    · right
      left
      obtain ⟨C⟩ := hcycle
      exact ⟨{
        selection := R
        internal := hinternal
        result := C
      }⟩
    · right
      right
      obtain ⟨B⟩ := hreflector
      have hsimple :
          SwitchSimple
            (A.exploration ++ B.reflector.exploration) := by
        rw [B.exploration_eq]
        exact R.combinedSimple
      have hpreserves :
          ∀ j, j ∉ B.reflector.exploration.map passageSwitch →
            B.state j = A.activatedState j := by
        intro j hj
        apply B.preserves
        rw [← B.exploration_eq]
        exact hj
      have hOldPaths :=
        dynamic_old_support_grooves
          A B.reflector A.activatedState B.state
          hApaths hsimple hpreserves
      have hcompatible :=
        manufactured_pair_compatible_of_explorations_simple
          A B.reflector hsimple
      exact ⟨{
        selection := R
        internal := hinternal
        result := B
        oldPaths := hOldPaths
        compatible := ⟨hcompatible.1, hcompatible.2⟩
      }⟩

/-! ## The exact first manufacturing journey -/

/-- The literal passage sequence from the first reflector''s base boundary
to its activated far boundary: outward exploration, activating contact, and
the reverse runway. -/
def ManufacturedReflector.manufacturingPassages
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : List Passage :=
  A.exploration ++
    (A.preReturn.1, A.mouthConfig.1) :: reversePassages A.runway

theorem ManufacturedReflector.manufacturingPassages_length
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.manufacturingPassages.length =
      A.exploration.length + A.runway.length + 1 := by
  simp [ManufacturedReflector.manufacturingPassages,
    reversePassages_length]
  omega

/-- The complete manufacturing journey is one physical trace, not merely an
endpoint equality. Retaining this list permits exact writer accounting
across the construction/cycle boundary. -/
theorem ManufacturedReflector.manufacturing_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState) :
    PhysicalTrace w (g, A.baseState) A.manufacturingPassages
      (e, A.activatedState) := by
  have hback := physicalTrace_contact_retraces_prefix
    A.runway_trace (A.runway_grooved hpaths)
    A.entryEdge A.return_arrive_mouth
  unfold ManufacturedReflector.manufacturingPassages
  exact A.exploration_trace.append hback

/-- Every switch visited on the complete out-and-back construction already
occurs in the switch-simple outward exploration. The reverse runway only
reverses old passages, and the activating contact is at the old mouth
switch. -/
theorem ManufacturedReflector.manufacturing_switch_mem_exploration
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    {passage : Passage}
    (hpassage : passage ∈ A.manufacturingPassages) :
    passageSwitch passage ∈ A.exploration.map passageSwitch := by
  unfold ManufacturedReflector.manufacturingPassages at hpassage
  rcases List.mem_append.mp hpassage with hout | hreturn
  · exact List.mem_map.mpr ⟨passage, hout, rfl⟩
  · rcases List.mem_cons.mp hreturn with hcontact | hreverse
    · subst passage
      have hswitch :
          A.preReturn.1 / 3 = A.mouthConfig.1 / 3 := by
        have hs := arrive_exit_switch A.preReturn.2 A.preReturn.1
        rw [A.return_arrive_mouth] at hs
        exact hs.symm
      rw [show passageSwitch
          (A.preReturn.1, A.mouthConfig.1) =
            A.mouthConfig.1 / 3 by
        simp [passageSwitch, hswitch]]
      cases A <;>
        simp [ManufacturedReflector.exploration,
          ManufacturedReflector.mouthConfig, passageSwitch]
    · have hmapped :
          passageSwitch passage ∈
            (reversePassages A.runway).map passageSwitch :=
        List.mem_map.mpr ⟨passage, hreverse, rfl⟩
      rw [map_passageSwitch_reversePassages A.runway_trace] at hmapped
      have hrunway :
          passageSwitch passage ∈ A.runway.map passageSwitch :=
        List.mem_reverse.mp hmapped
      cases A with
      | stay R =>
          simp only [ManufacturedReflector.runway] at hrunway
          change passageSwitch passage ∈
            (R.runway ++ [(R.mouth, R.arm)]).map passageSwitch
          rw [List.map_append]
          exact List.mem_append_left _ hrunway
      | flip R =>
          simp only [ManufacturedReflector.runway] at hrunway
          change passageSwitch passage ∈
            (R.runway ++ (R.mouth, R.firstArm) :: R.candy).map passageSwitch
          rw [List.map_append]
          exact List.mem_append_left _ hrunway

/-! ## Fresh-prefix writers are globally first -/

private theorem rawProductiveAt_pre_isSome
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (hprod : RawProductiveAt w N start k) :
    (stepN w k start).isSome := by
  obtain ⟨post, hpost⟩ := Option.isSome_iff_exists.mp hprod.1
  obtain ⟨pre, hpre⟩ := stepN_prefix_some
    (d := k) (K := k + 1) (by omega) hpost
  rw [hpre]
  simp

/-- A productive write in a fresh switch-simple continuation is globally its
writer''s first write. Earlier construction writers lie in the old
exploration; later earlier writers lie in the simple continuation itself.
The union simplicity excludes the former and local simplicity excludes the
latter. -/
theorem ManufacturedReflector.fresh_productive_is_global_first
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    {fresh : List Passage} {finish : Nat × Tongues}
    (htrace :
      PhysicalTrace w (e, A.activatedState) fresh finish)
    (hunion : SwitchSimple (A.exploration ++ fresh))
    {k : Nat} (hk : k < fresh.length)
    (hprod : RawProductiveAt w N (g, A.baseState)
      (A.exploration.length + A.runway.length + 1 + k)) :
    RawFirstWriterAt w N (g, A.baseState)
      (A.exploration.length + A.runway.length + 1 + k) := by
  let J := A.exploration.length + A.runway.length + 1
  have hmanufacturing := A.manufacturing_trace hpaths
  have hreach :
      stepN w J (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [J, A.manufacturingPassages_length] using
      hmanufacturing.sound
  have hprodAt :
      RawProductiveAt w N (g, A.baseState) (J + k) := by
    simpa [J] using hprod
  have hlocalProd :
      RawProductiveAt w N (e, A.activatedState) k :=
    rawProductiveAt_sub_of_reach hreach hprodAt
  have hfreshSimple : SwitchSimple fresh := by
    unfold SwitchSimple at hunion ⊢
    rw [List.map_append] at hunion
    exact (List.nodup_append.mp hunion).2.1
  have hlocalFirst :
      RawFirstWriterAt w N (e, A.activatedState) k :=
    htrace.rawProductiveAt_first_of_switchSimple
      hfreshSimple hk hlocalProd
  have hkLive :
      (stepN w k (e, A.activatedState)).isSome :=
    rawProductiveAt_pre_isSome hlocalProd
  have hshiftK :
      rawWriterAt w (g, A.baseState) (J + k) =
        rawWriterAt w (e, A.activatedState) k :=
    rawWriterAt_add_of_reach hreach hkLive
  refine ⟨hprodAt, ?_⟩
  intro j hj hprodJ
  by_cases hjBefore : j < J
  · intro heq
    have hjManufacturing :
        j < A.manufacturingPassages.length := by
      rw [A.manufacturingPassages_length]
      exact hjBefore
    have hjMem :=
      hmanufacturing.rawWriterAt_mem_passageSwitches
        hjManufacturing
    obtain ⟨oldPassage, holdPassage, holdWriter⟩ :=
      List.mem_map.mp hjMem
    have holdMem :
        rawWriterAt w (g, A.baseState) j ∈
          A.exploration.map passageSwitch := by
      rw [← holdWriter]
      exact A.manufacturing_switch_mem_exploration holdPassage
    have hkLocalMem :
        rawWriterAt w (e, A.activatedState) k ∈
          fresh.map passageSwitch :=
      htrace.rawWriterAt_mem_passageSwitches hk
    have hkMem :
        rawWriterAt w (g, A.baseState) (J + k) ∈
          fresh.map passageSwitch := by
      rw [hshiftK]
      exact hkLocalMem
    unfold SwitchSimple at hunion
    rw [List.map_append] at hunion
    have hcross := (List.nodup_append.mp hunion).2.2
    exact (hcross _ holdMem _ hkMem) heq
  · intro heq
    have hjLower : J ≤ j := Nat.le_of_not_gt hjBefore
    let d := j - J
    have hjEq : j = J + d := by
      dsimp [d]
      omega
    have hdLt : d < k := by
      dsimp [d]
      omega
    have hprodJShift :
        RawProductiveAt w N (g, A.baseState) (J + d) := by
      rw [← hjEq]
      exact hprodJ
    have hlocalProdJ :
        RawProductiveAt w N (e, A.activatedState) d :=
      rawProductiveAt_sub_of_reach hreach hprodJShift
    have hdLive :
        (stepN w d (e, A.activatedState)).isSome :=
      rawProductiveAt_pre_isSome hlocalProdJ
    have hshiftD :
        rawWriterAt w (g, A.baseState) (J + d) =
          rawWriterAt w (e, A.activatedState) d :=
      rawWriterAt_add_of_reach hreach hdLive
    have hneLocal :=
      hlocalFirst.2 d hdLt hlocalProdJ
    apply hneLocal
    calc
      rawWriterAt w (e, A.activatedState) d =
          rawWriterAt w (g, A.baseState) (J + d) := hshiftD.symm
      _ = rawWriterAt w (g, A.baseState) j := by rw [hjEq]
      _ = rawWriterAt w (g, A.baseState) (J + k) := heq
      _ = rawWriterAt w (e, A.activatedState) k := hshiftK

/-- Every vector through the fresh simple prefix is either the activated
boundary vector or a globally first-writer post-vector. This is the exact
history cover needed before the repeated passage starts the cycle. -/
theorem ManufacturedReflector.fresh_prefix_mem_rawHistory_one_extra
    {w : Wiring} {N H g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    {fresh : List Passage} {finish : Nat × Tongues}
    (htrace :
      PhysicalTrace w (e, A.activatedState) fresh finish)
    (hunion : SwitchSimple (A.exploration ++ fresh))
    (horizon :
      A.exploration.length + A.runway.length + 1 +
        fresh.length ≤ H) :
    ∀ k, k ≤ fresh.length →
      restrictedTonguesAt w N (g, A.baseState)
          (A.exploration.length + A.runway.length + 1 + k) ∈
        rawFirstWriterHistory w N (g, A.baseState) H ++
          [VectorCount.restrict N A.activatedState] := by
  let J := A.exploration.length + A.runway.length + 1
  let start : Nat × Tongues := (g, A.baseState)
  let history := rawFirstWriterHistory w N start H
  have hmanufacturing := A.manufacturing_trace hpaths
  have hreach :
      stepN w J start = some (e, A.activatedState) := by
    simpa [J, start, A.manufacturingPassages_length] using
      hmanufacturing.sound
  have main : ∀ k, k ≤ fresh.length →
      restrictedTonguesAt w N start (J + k) ∈
        history ++ [VectorCount.restrict N A.activatedState] := by
    intro k
    induction k with
    | zero =>
        intro _hk
        apply List.mem_append_right history
        have hvector :
            restrictedTonguesAt w N start J =
              VectorCount.restrict N A.activatedState := by
          simp [restrictedTonguesAt, tonguesAt, hreach]
        simp [hvector]
    | succ n ih =>
        intro hsucc
        have hnLt : n < fresh.length := by omega
        have hnLe : n ≤ fresh.length := Nat.le_of_lt hnLt
        have hprevious := ih hnLe
        obtain ⟨post, hpostLocal⟩ := stepN_prefix_some
          (d := n + 1) (K := fresh.length) hsucc htrace.sound
        have hpostGlobal :
            stepN w (J + (n + 1)) start = some post := by
          rw [stepN_add, hreach]
          exact hpostLocal
        have hpostLive :
            (stepN w (J + n + 1) start).isSome := by
          simpa [Nat.add_assoc] using
            (show (stepN w (J + (n + 1)) start).isSome by
              rw [hpostGlobal]
              simp)
        by_cases hprod :
            RawProductiveAt w N start (J + n)
        · have hfirstFull :=
            A.fresh_productive_is_global_first
              (N := N) hpaths htrace hunion hnLt
              (hprod := by simpa [J, start] using hprod)
          have hfirst :
              RawFirstWriterAt w N start (J + n) := by
            simpa [J, start] using hfirstFull
          apply List.mem_append_left
          unfold history rawFirstWriterHistory
          apply List.mem_cons_of_mem
          apply List.mem_map.mpr
          refine ⟨J + n, ?_, rfl⟩
          apply mem_rawFirstWriterTimes_iff.mpr
          exact ⟨by
            omega, hfirst⟩
        · have hsame :
              restrictedTonguesAt w N start (J + n + 1) =
                restrictedTonguesAt w N start (J + n) := by
            apply Classical.byContradiction
            intro hne
            exact hprod ⟨hpostLive, hne⟩
          rw [show J + (n + 1) = J + n + 1 by omega,
            hsame]
          exact hprevious
  intro k hk
  simpa [J, start, history] using main k hk

/-! ## Exact all-time cycle phase -/

/-- The reached cycle has only its repeat state and settled state at every
later time. The proof uses its exact transient lap followed by the exact
stable lap; no opaque eventual-periodicity witness is used. -/
theorem DynamicReachedSimpleCycle.all_time_phase
    {w : Wiring} {atRepeat : Nat × Tongues}
    (C : DynamicReachedSimpleCycle w atRepeat) :
    ∀ d, ∃ port state,
      stepN w d atRepeat = some (port, state) ∧
        (state = atRepeat.2 ∨ state = C.settled) := by
  have hpositive : 0 < C.cycle.length := by
    cases hcycle : C.cycle with
    | nil => exact (C.nonempty hcycle).elim
    | cons head tail => simp
  have hperiod :
      stepN w C.cycle.length (atRepeat.1, C.settled) =
        some (atRepeat.1, C.settled) :=
    C.stable.sound
  have hgrooved : PassagesGrooved C.settled C.cycle :=
    C.stable.grooved_of_switchSimple C.simple
  have hsettledAll : ∀ d, ∃ port,
      stepN w d (atRepeat.1, C.settled) =
        some (port, C.settled) := by
    intro d
    have hwindow : ∀ r, r ≤ C.cycle.length → ∃ port state,
        stepN w r (atRepeat.1, C.settled) =
            some (port, state) ∧
          (state = C.settled ∨ state = C.settled) := by
      intro r hr
      obtain ⟨port, hrun⟩ :=
        C.stable.grooved_prefix_tongues C.settled hgrooved hr
      exact ⟨port, C.settled, hrun, Or.inl rfl⟩
    obtain ⟨port, state, hrun, hstate⟩ :=
      periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow d
    have hstateEq : state = C.settled :=
      Or.elim hstate id id
    subst state
    exact ⟨port, hrun⟩
  intro d
  by_cases hd : d ≤ C.cycle.length
  · exact C.phase d hd
  · let r := d - C.cycle.length
    have hdEq : d = C.cycle.length + r := by
      dsimp [r]
      omega
    obtain ⟨port, hrun⟩ := hsettledAll r
    have habsolute :
        stepN w d atRepeat = some (port, C.settled) := by
      rw [hdEq, stepN_add, C.transient.sound]
      simpa using hrun
    exact ⟨port, C.settled, habsolute, Or.inr rfl⟩

/-! ## Direct sharp accounting for the cycle branch -/

/-- The first turnaround followed by the canonical fresh-prefix simple cycle
spends at most two repeated-writer novelties at every horizon. One exceptional
vector is the first reflector''s activated boundary; the only other possible
exception is the settled cycle vector. All productive writers in the selected
fresh prefix are charged as globally first.

This is a direct raw-trajectory theorem and is intended as the cycle branch
consumed by the strong-recursion assembly. -/
theorem UnionFreshDynamicCycle.first_turnaround_repeatedWriterNovelty_le_two
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage}
    (C : UnionFreshDynamicCycle A fresh)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hApaths :
      PathGrooves A.toSupported.paths A.activatedState) :
    ∀ H,
      (rawRepeatedWriterNovelTimes w N
        (g, A.baseState) H).length ≤ 2 := by
  intro H
  let J := A.exploration.length + A.runway.length + 1
  let L := J + C.selection.before.length
  let K := max H L
  let start : Nat × Tongues := (g, A.baseState)
  let history := rawFirstWriterHistory w N start K
  let times := rawRepeatedWriterPostTimes w N start K
  let activated := VectorCount.restrict N A.activatedState
  let settled := VectorCount.restrict N C.result.cycle.settled
  have hHK : H ≤ K := Nat.le_max_left _ _
  have hLK : L ≤ K := Nat.le_max_right _ _
  have hmanufacturing := A.manufacturing_trace hApaths
  have hreachA :
      stepN w J start = some (e, A.activatedState) := by
    simpa [J, start, A.manufacturingPassages_length] using
      hmanufacturing.sound
  have hreachRepeat :
      stepN w L start = some C.result.atRepeat := by
    dsimp [L]
    rw [stepN_add, hreachA]
    exact C.result.reached
  have hexplorationK : A.exploration.length ≤ K := by
    dsimp [J, L] at hLK
    omega
  have hprefixK :
      A.exploration.length + A.runway.length + 1 +
        C.selection.before.length ≤ K := by
    simpa [J, L] using hLK
  have widen : ∀ {v : List Bool},
      v ∈ history ++ [activated] →
        v ∈ history ++ [activated, settled] := by
    intro v hv
    rcases List.mem_append.mp hv with hh | ha
    · exact List.mem_append_left _ hh
    · apply List.mem_append_right history
      have hva : v = activated := by simpa using ha
      simp [hva]
  have hcover :
      NoveltyCoverOn w N start times history 2 := by
    refine ⟨[activated, settled], by simp, ?_⟩
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
    have hkData := mem_rawRepeatedWriterNovelTimes_iff.mp hk
    have hpostK : k + 1 ≤ K := by omega
    by_cases hmanufactured : k + 1 ≤ J
    · have hm :=
        A.manufacturing_journey_mem_rawHistory_one_extra
          (N := N) (K := K) hApaths hexplorationK
          (k + 1) (by
            dsimp [J] at hmanufactured
            exact hmanufactured)
      apply widen
      simpa [start, history, activated] using hm
    · by_cases hprefix : k + 1 ≤ L
      · let d := k + 1 - J
        have htime : k + 1 = J + d := by
          dsimp [d]
          omega
        have hdLe : d ≤ C.selection.before.length := by
          dsimp [d, L] at hprefix
          omega
        have hm :=
          A.fresh_prefix_mem_rawHistory_one_extra
            (N := N) (H := K) hApaths
            C.result.prefixTrace C.selection.combinedSimple
            hprefixK d hdLe
        apply widen
        rw [htime]
        simpa [J, start, history, activated] using hm
      · let d := k + 1 - L
        have htime : k + 1 = L + d := by
          dsimp [d]
          omega
        obtain ⟨port, state, hlocal, hphase⟩ :=
          C.result.cycle.all_time_phase d
        have hglobal :
            stepN w (k + 1) start = some (port, state) := by
          rw [htime, stepN_add, hreachRepeat]
          exact hlocal
        have hvector :
            restrictedTonguesAt w N start (k + 1) =
              VectorCount.restrict N state := by
          simp [restrictedTonguesAt, tonguesAt, hglobal]
        rw [hvector]
        rcases hphase with hrepeat | hsettled
        · rw [hrepeat]
          apply widen
          have hm :=
            A.fresh_prefix_mem_rawHistory_one_extra
              (N := N) (H := K) hApaths
              C.result.prefixTrace C.selection.combinedSimple
              hprefixK C.selection.before.length (Nat.le_refl _)
          have hend :
              restrictedTonguesAt w N start L =
                VectorCount.restrict N C.result.atRepeat.2 := by
            simp [restrictedTonguesAt, tonguesAt, hreachRepeat]
          simpa [J, L, start, history, activated, hend] using hm
        · apply List.mem_append_right history
          simp [settled, hsettled]
  have hnew : ∀ t ∈ times,
      restrictedTonguesAt w N start t ∉ history := by
    simpa [times, history, start] using
      repeatedWriterPostTimes_avoid_firstHistory
        (w := w) (N := N) hN start K
  have hnd :
      (times.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [times]
    rw [map_repeatedWriterPostTimes_eq_fresh]
    exact rawRepeatedWriterFresh_nodup w N start K
  have hcount :=
    noveltyCoverOn_fresh_distinct_count hcover hnew hnd
  have hK :
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 2 := by
    simpa [times, rawRepeatedWriterPostTimes] using hcount
  have hmono :=
    rawRepeatedWriterNovelTimes_length_mono
      (w := w) (N := N) (start := start) hHK
  simpa [start] using Nat.le_trans hmono hK

/-- **Direct dynamic-residual trichotomy.** The old-contact branch retains its
strict tracked shrink; the exact cycle branch is discharged immediately by
the all-horizon bound two; and the compatible-pair branch is retained for the
existing pair theorem. This is the form required by the strong-recursion
assembly. -/
theorem ManufacturedReflector.union_first_contact_shrinks_or_cycle_le_two_or_compatible
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage}
    {finish : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hApaths :
      PathGrooves A.toSupported.paths A.activatedState)
    (htrace :
      PhysicalTrace w (e, A.activatedState) fresh finish)
    (hnonsimple :
      ¬ SwitchSimple (A.exploration ++ fresh)) :
    Nonempty (UnionOldTrackedShrink w N A fresh finish) ∨
      (∀ H,
        (rawRepeatedWriterNovelTimes w N
          (g, A.baseState) H).length ≤ 2) ∨
      Nonempty (UnionFreshCompatiblePair A fresh) := by
  have hout :=
    A.union_first_contact_shrinks_or_dynamic_cycle_or_compatible
      hN hApaths htrace hnonsimple
  rcases hout with hold | hcycle | hpair
  · exact Or.inl hold
  · right
    left
    obtain ⟨C⟩ := hcycle
    exact C.first_turnaround_repeatedWriterNovelty_le_two
      A hN hApaths
  · exact Or.inr (Or.inr hpair)

end GeneralN
