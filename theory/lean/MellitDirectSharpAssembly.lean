import MellitDirectStateBound
import MellitGlobalIncompatibleClosure
import ShrinkingCurveFinal

/-!
# Direct Mellit union-first-repeat assembly

This file retains exact physical traces for the first repetition selected
against an old manufactured exploration plus a fresh trace. It is entirely
general in the number of switches.
-/

namespace GeneralN

/-! ## An exact activated first-revisit normal form -/

/-- The activated reflector returned by a concrete first revisit, with the
identity of its outward exploration retained. The older constructor keeps
all dynamic data but hides this final definitional equality behind an
existential. -/
structure ExactActivatedFirstRevisit
    (w : Wiring) (start : Nat × Tongues)
    (runway path : List Passage) (p x q e : Nat)
    (u : Tongues) : Type where
  reflector : ManufacturedReflector w start.1 e
  state : Tongues
  paths :
    PathGrooves reflector.toSupported.paths state
  base : reflector.baseState = start.2
  activated : state = reflector.activatedState
  back :
    stepN w (runway.length + 1) (q, u) = some (e, state)
  preserves :
    ∀ j, j ∉ (runway ++ (p, x) :: path).map passageSwitch →
      state j = start.2 j
  exploration_eq :
    reflector.exploration = runway ++ (p, x) :: path

/-! ## Exact physical first-revisit extraction -/

/-- Strengthened rich first-revisit normal form. Unlike
`first_revisit_cycle_or_activated_manufactured_reflector`, the reflector
branch records that its exploration is exactly the switch-simple prefix
which precedes the repeated passage. -/
private theorem first_revisit_cycle_or_activated_exact
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
    SettlesOnSimpleCycle w (q, u) ∨
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
    have hp := hexcursion.simple_return_period hsimpleExcursion
    exact ⟨((p, x) :: path).length, u, by simp, hp, hp⟩
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
    have hcycle := hexcursion.simple_same_exit_enters_period
      hsimpleExcursion hrepeat
    exact ⟨((q, x) :: path).length, v, by simp,
      hcycle.1, hcycle.2⟩

/-! ## Lifting an internal union repeat through the physical trace -/

/-- The simple-cycle branch of an internal first union repetition. -/
structure UnionInternalCycleResult
    (w : Wiring) (start : Nat × Tongues)
    (before : List Passage) : Type where
  atRepeat : Nat × Tongues
  reached :
    stepN w before.length start = some atRepeat
  settles :
    SettlesOnSimpleCycle w atRepeat

/-- The reflector branch of an internal first union repetition.  Every
control-flow witness is retained, and the manufactured exploration is
identified with the selected fresh prefix. -/
structure UnionInternalReflectorResult
    (w : Wiring) (start : Nat × Tongues)
    (before : List Passage) (entryEdge : Nat) : Type where
  atRepeat : Nat × Tongues
  reached :
    stepN w before.length start = some atRepeat
  reflector : ManufacturedReflector w start.1 entryEdge
  state : Tongues
  backSteps : Nat
  paths :
    PathGrooves reflector.toSupported.paths state
  base : reflector.baseState = start.2
  activated : state = reflector.activatedState
  back :
    stepN w backSteps atRepeat = some (entryEdge, state)
  preserves :
    ∀ j, j ∉ before.map passageSwitch →
      state j = start.2 j
  exploration_eq :
    reflector.exploration = before

/-- If the union-selected repetition is internal to the fresh prefix, the
actual physical trace either settles on a simple cycle or manufactures the
opposite reflector with exploration exactly equal to that prefix. -/
private theorem PhysicalTrace.internal_union_repeat_exact
    {w : Wiring} {old fresh : List Passage}
    {start finish : Nat × Tongues} {entryEdge : Nat}
    (htrace : PhysicalTrace w start fresh finish)
    (R : UnionFirstRepeat old fresh)
    (hinternal :
      passageSwitch R.repeated ∈
        R.before.map passageSwitch)
    (hentry : w.link entryEdge = some start.1) :
    Nonempty
        (UnionInternalCycleResult w start R.before) ∨
      Nonempty
        (UnionInternalReflectorResult
          w start R.before entryEdge) := by
  rcases R with
    ⟨before, repeated, after, hsplit, hcombined, hrepeats⟩
  change passageSwitch repeated ∈
    before.map passageSwitch at hinternal
  change
    Nonempty (UnionInternalCycleResult w start before) ∨
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
  have hout := first_revisit_cycle_or_activated_exact w
    hrunway hexcursion hsimple hswitch hrepeat hentry
  rcases hout with hcycle | hreflector
  · left
    exact ⟨{
      atRepeat := (q, u)
      reached := by simpa using hreached
      settles := hcycle
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

/-! ## The union-first-contact trichotomy -/

/-- Exact agreement outside a switch-disjoint second exploration preserves
all support grooves of the first reflector. -/
private theorem old_support_grooves_of_exact_disjoint
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

/-- The canonical union repeat touches the old exploration before any repeat
inside the fresh prefix. This is now the only unresolved direct-Mellit
branch. -/
structure UnionOldSupportContact
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (fresh : List Passage) : Type where
  selection : UnionFirstRepeat A.exploration fresh
  hitsOld :
    passageSwitch selection.repeated ∈
      A.exploration.map passageSwitch

/-- The canonical union repeat is internal and settles on a simple cycle. -/
structure UnionFreshSimpleCycle
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (fresh : List Passage) : Type where
  selection : UnionFirstRepeat A.exploration fresh
  internal :
    passageSwitch selection.repeated ∈
      selection.before.map passageSwitch
  result :
    UnionInternalCycleResult
      w (e, A.activatedState) selection.before

/-- The canonical union repeat is internal and manufactures a compatible
opposite reflector. The old and new groove families hold simultaneously in
the returned activated state. -/
structure UnionFreshCompatiblePair
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (fresh : List Passage) : Type where
  selection : UnionFirstRepeat A.exploration fresh
  internal :
    passageSwitch selection.repeated ∈
      selection.before.map passageSwitch
  result :
    UnionInternalReflectorResult
      w (e, A.activatedState) selection.before g
  oldPaths :
    PathGrooves A.toSupported.paths result.state
  compatible :
    MellitPairCompatible A result.reflector

/-- **Direct union-first-repeat reduction.** For an actual second
exploration whose union with the old manufactured exploration is not simple,
the canonical first repeat has exactly three outcomes:

* it hits the old exploration at a concrete passage switch;
* it settles on a simple cycle; or
* it manufactures an opposite reflector with an exactly disjoint
  exploration, and hence a support-compatible pair.

No compatibility premise and no abstract support-intersection residue remain.
The first alternative is a strict old-support first contact and is the sole
case still requiring shrinking/recursion. -/
theorem ManufacturedReflector.union_first_contact_cycle_or_compatible
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage}
    {finish : Nat × Tongues}
    (hApaths :
      PathGrooves A.toSupported.paths A.activatedState)
    (htrace :
      PhysicalTrace w (e, A.activatedState) fresh finish)
    (hnonsimple :
      ¬ SwitchSimple (A.exploration ++ fresh)) :
    Nonempty (UnionOldSupportContact A fresh) ∨
      Nonempty (UnionFreshSimpleCycle A fresh) ∨
      Nonempty (UnionFreshCompatiblePair A fresh) := by
  obtain ⟨R⟩ := first_repeat_against_union
    A.exploration fresh A.exploration_simple hnonsimple
  rcases R.old_or_internal with hold | hinternal
  · left
    exact ⟨{
      selection := R
      hitsOld := hold
    }⟩
  · right
    have hout := htrace.internal_union_repeat_exact
      R hinternal (w.symm _ _ A.entryEdge)
    rcases hout with hcycle | hreflector
    · left
      obtain ⟨C⟩ := hcycle
      exact ⟨{
        selection := R
        internal := hinternal
        result := C
      }⟩
    · right
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
        old_support_grooves_of_exact_disjoint
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

/-! ## Sharp accounting on the compatible branch -/

/-- Once the union-selected internal repeat has manufactured its compatible
opposite reflector, the existing first-turnaround plus Gray-square theorem
gives the literal all-horizon bound five.  This theorem makes no claim about
the old-support-contact or simple-cycle branches of the trichotomy above. -/
theorem UnionFreshCompatiblePair.first_turnaround_repeatedWriterNovelty_le_five
    {w : Wiring} {h g e N : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage}
    (C : UnionFreshCompatiblePair A fresh)
    (P : ManufacturedReflector w h g)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hPpaths :
      PathGrooves P.toSupported.paths P.activatedState)
    (hJourney : stepN w
      (P.exploration.length + P.runway.length + 1)
      (h, P.baseState) = some (g, C.result.state)) :
    ∀ H,
      (rawRepeatedWriterNovelTimes w N
        (h, P.baseState) H).length ≤ 5 := by
  exact first_turnaround_then_compatible_pair_repeatedWriterNovelty_le_five
    P A C.result.reflector C.result.state hN hPpaths
    C.oldPaths C.result.paths C.compatible.1 C.compatible.2 hJourney

/-! ## Strict data in the remaining old-contact branch -/

/-- A canonical old-contact outcome exposes a genuinely shorter prefix of
the old exploration ending immediately before the contacted passage.  This
is the well-founded list measure needed by a shrinking recursion.  It does
not by itself assert that the shortened prefix is already a manufactured
reflector. -/
structure StrictUnionOldPrefix
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage}
    (C : UnionOldSupportContact A fresh) : Type where
  oldBefore : List Passage
  oldPassage : Passage
  oldAfter : List Passage
  split :
    A.exploration = oldBefore ++ oldPassage :: oldAfter
  sameSwitch :
    passageSwitch oldPassage =
      passageSwitch C.selection.repeated
  proper :
    oldBefore.length < A.exploration.length

/-- Every remaining old-contact branch carries an explicit strict prefix.
The selected fresh prefix is still retained in `C.selection`, together with
its exact trace split and combined simplicity. -/
theorem UnionOldSupportContact.strict_old_prefix
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage}
    (C : UnionOldSupportContact A fresh) :
    Nonempty (StrictUnionOldPrefix C) := by
  obtain ⟨oldPassage, hold, hsame⟩ :=
    List.mem_map.mp C.hitsOld
  obtain ⟨oldBefore, oldAfter, hsplit⟩ :=
    List.append_of_mem hold
  refine ⟨{
    oldBefore := oldBefore
    oldPassage := oldPassage
    oldAfter := oldAfter
    split := hsplit
    sameSwitch := hsame
    proper := ?_
  }⟩
  rw [hsplit]
  simp

/-! ## Quantitative old-contact shrink in the direct trichotomy -/

/-- The old-contact branch, upgraded with the physical trace split and both
strict tracked residual supports from `ShrinkingCurveFinal`. -/
structure UnionOldTrackedShrink
    (w : Wiring) (N : Nat)
    {g e : Nat} (A : ManufacturedReflector w g e)
    (fresh : List Passage) (finish : Nat × Tongues) : Type where
  selection : UnionFirstRepeat A.exploration fresh
  raw :
    RawUnionOldContactShrink w N A.exploration fresh selection
      (e, A.activatedState) finish

/-- **Sharp direct Mellit reduction with well-founded old contact.** Under
the ambient `N`-switch range hypothesis, the direct union-first-repeat
trichotomy has only these outcomes:

* a raw old-contact trace split whose two residual tracked supports both have
  strictly smaller support/contact rank;
* a reached simple cycle; or
* a compatible opposite-reflector pair, whose branch has the all-horizon
  repeated-writer novelty bound five above.

Thus abstract incompatibility and non-well-founded old-contact nesting are
both eliminated.  The remaining proof obligation for
`FiveRepeatedWriterNovelty` is dynamic: identify which strict residual
support represents the continuation, and attach sharp novelty accounting to
the simple-cycle branch. -/
theorem ManufacturedReflector.union_first_contact_shrinks_or_cycle_or_compatible
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
      Nonempty (UnionFreshSimpleCycle A fresh) ∨
      Nonempty (UnionFreshCompatiblePair A fresh) := by
  have hbase :=
    A.union_first_contact_cycle_or_compatible
      hApaths htrace hnonsimple
  rcases hbase with hold | hcycle | hpair
  · left
    obtain ⟨C⟩ := hold
    have hRange :
        ∀ passage, passage ∈ A.exploration →
          passageSwitch passage < N := by
      intro passage hpassage
      exact A.exploration_trace.switch_lt
        hN passage hpassage
    obtain ⟨S⟩ := htrace.union_old_contact_shrink
      C.selection hRange C.hitsOld
    exact ⟨{
      selection := C.selection
      raw := S
    }⟩
  · exact Or.inr (Or.inl hcycle)
  · exact Or.inr (Or.inr hpair)

end GeneralN
