import TwoHistoryUnionCharge
import MellitDynamicResidual
import ProtectedRepairFour

/-!
# Exact continuation at a canonical old-support contact

This file isolates the dynamic information retained by
`RawUnionOldContactShrink`.  The fresh prefix selected by
`UnionFirstRepeat` is disjoint from the whole old exploration, so it reaches
the contact without changing any reusable old groove.  At a genuine support
contact, degree three then forces the contacting passage to leave through
one of the two endpoints of the contacted old passage.  Those two endpoint
equalities are the canonical left/right selector; no selector is assumed.

There is one exact third structural outcome.  For a flip reflector the
manufacturing exploration contains its mouth passage, while the reusable
support contains only the runway and candy.  A contact with that mouth
passage is therefore not a contact with either residual support.  We retain
that outcome explicitly instead of incorrectly forcing it into the two-way
support selector.

`GeneralN.StateLaw` remains open.  Everything below is symbolic in `N`.
-/

namespace GeneralN

/-- The passage named by an old-contact split really occurs in the old
list.  This small explicit equality transport avoids rewriting the list
parameter on which the split certificate itself depends. -/
theorem UnionOldContactSplit.hit_mem_old
    {old fresh : List Passage} {R : UnionFirstRepeat old fresh}
    (S : UnionOldContactSplit old fresh R) : S.hit ∈ old := by
  have hmem : S.hit ∈ S.beforeHit ++ S.hit :: S.afterHit :=
    List.mem_append_right _ List.mem_cons_self
  exact Eq.mp
    (congrArg (fun passages => S.hit ∈ passages) S.split).symm hmem

/-- The selected fresh prefix reaches the exact contact configuration. -/
theorem UnionOldTrackedShrink.reaches_atContact
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    stepN w C.selection.before.length (e, A.activatedState) =
      some C.raw.atContact :=
  C.raw.beforeTrace.sound

/-- The port stored in the contact configuration is literally the entry of
the selected repeated passage. -/
theorem UnionOldTrackedShrink.atContact_port
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    C.raw.atContact.1 = C.selection.repeated.1 :=
  C.raw.fromContactTrace.head_arrive.1

/-- Trace-valued form of `reaches_atContact`, with the dependent contact
configuration normalized to the repeated passage's literal entry port. -/
theorem UnionOldTrackedShrink.beforeTrace_to_contact
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    PhysicalTrace w (e, A.activatedState) C.selection.before
      (C.selection.repeated.1, C.raw.atContact.2) := by
  have hcontactEq : C.raw.atContact =
      (C.selection.repeated.1, C.raw.atContact.2) := by
    apply Prod.ext
    · exact C.atContact_port
    · rfl
  rw [← hcontactEq]
  exact C.raw.beforeTrace

/-- The first step after the contact configuration is the selected repeated
passage, with its exact post-contact tongue vector retained. -/
theorem UnionOldTrackedShrink.contact_arrival
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    ∃ next,
      arrive C.raw.atContact.2 C.selection.repeated.1 =
        (C.selection.repeated.2, next) :=
  C.raw.fromContactTrace.head_arrive.2

/-- Every passage in the selected fresh prefix avoids every reusable support
switch of the old reflector.  This is stronger than merely avoiding the
contacted old passage. -/
theorem UnionOldTrackedShrink.before_avoids_support
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    ∀ newPassage ∈ C.selection.before,
      ∀ path ∈ A.toSupported.paths, ∀ oldPassage ∈ path,
        passageSwitch newPassage ≠ passageSwitch oldPassage := by
  have hsimple := C.selection.combinedSimple
  unfold SwitchSimple at hsimple
  rw [List.map_append] at hsimple
  have hcross := (List.nodup_append.mp hsimple).2.2
  intro newPassage hnew path hpath oldPassage hold hEq
  have hOld : passageSwitch oldPassage ∈
      A.exploration.map passageSwitch :=
    A.support_switch_mem_exploration hpath hold
  have hNew : passageSwitch newPassage ∈
      C.selection.before.map passageSwitch :=
    List.mem_map.mpr ⟨newPassage, hnew, rfl⟩
  exact (hcross (passageSwitch oldPassage) hOld
    (passageSwitch newPassage) hNew) hEq.symm

/-- Consequently all reusable grooves of the old reflector are still exact
at the contact state.  This is the rebase point needed for any continuation
argument; no construction prefix is replayed or charged a second time. -/
theorem UnionOldTrackedShrink.atContact_support_grooves
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState) :
    PathGrooves A.toSupported.paths C.raw.atContact.2 := by
  exact pathGrooves_preserved_by_foreign_trace
    C.raw.beforeTrace hApaths C.before_avoids_support

/-- The contact passage is new relative to the selected prefix.  Although it
repeats an old switch, `before ++ [repeated]` is itself switch-simple. -/
theorem UnionOldTrackedShrink.before_contact_simple
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    SwitchSimple (C.selection.before ++ [C.selection.repeated]) := by
  have hcombined := C.selection.combinedSimple
  unfold SwitchSimple at hcombined ⊢
  rw [List.map_append] at hcombined
  simp only [List.map_append, List.map_singleton]
  have hparts := List.nodup_append.mp hcombined
  apply List.nodup_append.mpr
  refine ⟨hparts.2.1, by simp, ?_⟩
  intro a ha b hb hEq
  simp only [List.mem_singleton] at hb
  have hHit : passageSwitch C.raw.split.hit ∈
      A.exploration.map passageSwitch := by
    exact List.mem_map.mpr
      ⟨C.raw.split.hit, C.raw.split.hit_mem_old, rfl⟩
  have hne := hparts.2.2
    (passageSwitch C.raw.split.hit) hHit a ha
  apply hne
  calc
    passageSwitch C.raw.split.hit =
        passageSwitch C.selection.repeated :=
      C.raw.split.sameSwitch
    _ = b := hb.symm
    _ = a := hEq.symm

/-- Every selected old hit is an actual member of the old manufacturing
exploration. -/
theorem UnionOldTrackedShrink.hit_mem_exploration
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    C.raw.split.hit ∈ A.exploration :=
  C.raw.split.hit_mem_old

/-- A manufacturing-exploration passage is reusable support, except for the
single mouth passage of a flip reflector.  This is the exact third outcome
missing from a naive two-residual-support selector. -/
theorem ManufacturedReflector.exploration_support_or_flip_mouth
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) {old : Passage}
    (hold : old ∈ A.exploration) :
    (∃ path ∈ A.toSupported.paths, old ∈ path) ∨
      ∃ R : ManufacturedFlipReflector w g e,
        A = .flip R ∧ old = (R.mouth, R.firstArm) := by
  cases A with
  | stay R =>
      left
      simp only [ManufacturedReflector.exploration,
        ManufacturedReflector.toSupported,
        ManufacturedStayReflector.toSupported] at hold ⊢
      rcases List.mem_append.mp hold with hrunway | hmouth
      · exact ⟨R.runway, by simp, hrunway⟩
      · have hEq : old = (R.mouth, R.arm) := by simpa using hmouth
        exact ⟨[(R.mouth, R.arm)], by simp, by simp [hEq]⟩
  | flip R =>
      simp only [ManufacturedReflector.exploration,
        ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported] at hold ⊢
      rcases List.mem_append.mp hold with hrunway | hpost
      · left
        exact ⟨R.runway, by simp, hrunway⟩
      · rcases List.mem_cons.mp hpost with hmouth | hcandy
        · right
          exact ⟨R, rfl, hmouth⟩
        · left
          exact ⟨R.candy, by simp, hcandy⟩

/-- Concrete data for the genuine support-contact branch. -/
structure UnionOldSupportReach
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) : Type where
  path : List Passage
  path_mem : path ∈ A.toSupported.paths
  hit_mem : C.raw.split.hit ∈ path

/-- Concrete data for the exact non-support third outcome. -/
structure UnionOldFlipMouthReach
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) : Type where
  reflector : ManufacturedFlipReflector w g e
  reflector_eq : A = .flip reflector
  hit_eq : C.raw.split.hit =
    (reflector.mouth, reflector.firstArm)

/-- Exact support-versus-mouth classification of an old contact. -/
theorem UnionOldTrackedShrink.support_or_flip_mouth
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    Nonempty (UnionOldSupportReach C) ∨
      Nonempty (UnionOldFlipMouthReach C) := by
  rcases A.exploration_support_or_flip_mouth
      C.hit_mem_exploration with hsupport | hmouth
  · left
    obtain ⟨path, hpath, hhit⟩ := hsupport
    exact ⟨{ path := path, path_mem := hpath, hit_mem := hhit }⟩
  · right
    obtain ⟨R, hA, hhit⟩ := hmouth
    exact ⟨{ reflector := R, reflector_eq := hA, hit_eq := hhit }⟩

/-- At a genuine support contact the physical exit itself selects one of the
two strict residual sides.  The theorem retains the exact post-contact state
and assumes neither a side nor an orientation. -/
theorem UnionOldSupportReach.contact_selects_endpoint
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    {C : UnionOldTrackedShrink w N A fresh finish}
    (D : UnionOldSupportReach C)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState) :
    ∃ next,
      arrive C.raw.atContact.2 C.selection.repeated.1 =
        (C.selection.repeated.2, next) ∧
      (C.selection.repeated.2 = C.raw.split.hit.1 ∨
        C.selection.repeated.2 = C.raw.split.hit.2) := by
  obtain ⟨next, harrive⟩ := C.contact_arrival
  have hpaths := C.atContact_support_grooves hApaths
  have hgroove := hpaths D.path D.path_mem
    C.raw.split.hit D.hit_mem
  have hswitch : C.raw.split.hit.1 / 3 =
      C.selection.repeated.1 / 3 := by
    simpa [passageSwitch] using C.raw.split.sameSwitch
  have hexit := grooved_contact_exits_on_old_passage
    hgroove harrive hswitch
  exact ⟨next, harrive, hexit⟩

/-- Two no-change passages through one switch use the same physical edge.
Their recorded orientations are therefore equal or reversed. -/
theorem grooved_same_switch_passages_eq_or_reverse
    {state : Tongues} {old new : Passage}
    (hold : arrive state old.2 = (old.1, state))
    (hnew : arrive state new.1 = (new.2, state))
    (hswitch : passageSwitch old = passageSwitch new) :
    new = old ∨ new = (old.2, old.1) := by
  have hswitch' : old.1 / 3 = new.1 / 3 := by
    simpa [passageSwitch] using hswitch
  have hexit := grooved_contact_exits_on_old_passage
    hold hnew hswitch'
  have hback := arrive_back state new.1
  rw [hnew] at hback
  rcases hexit with hentrySide | hexitSide
  · have hforward := groove_forward hold
    rw [hentrySide, hforward] at hback
    have hfirst : new.1 = old.2 := by
      exact (congrArg Prod.fst hback).symm
    right
    apply Prod.ext
    · exact hfirst
    · exact hentrySide
  · rw [hexitSide, hold] at hback
    have hfirst : new.1 = old.1 := by
      exact (congrArg Prod.fst hback).symm
    left
    apply Prod.ext
    · exact hfirst
    · exact hexitSide

/-- A state-changing genuine support contact is already classified by the
existing protected-contact theorem.  The route supplied to that theorem is
exactly `before ++ [repeated]`; its simplicity was proved above from union
first-contact minimality.  Thus a backward contact is periodic, while the
only remaining branch is the exact forward self-repairing lobe passage. -/
theorem UnionOldSupportReach.changed_periodic_or_forward
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    {C : UnionOldTrackedShrink w N A fresh finish}
    (D : UnionOldSupportReach C)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    {next : Tongues}
    (harrive :
      arrive C.raw.atContact.2 C.selection.repeated.1 =
        (C.selection.repeated.2, next))
    (hchanged : next (C.selection.repeated.1 / 3) ≠
      C.raw.atContact.2 (C.selection.repeated.1 / 3)) :
    EventuallyPeriodic w (e, A.activatedState) ∨
      ∃ oriented repaired,
        oriented ∈ A.orientedRoute C.raw.atContact.2 ∧
        arrive C.raw.atContact.2 oriented.2 =
          (oriented.1, C.raw.atContact.2) ∧
        passageSwitch oriented = C.selection.repeated.1 / 3 ∧
        C.selection.repeated.2 = oriented.2 ∧
        arrive next oriented.1 = (oriented.2, repaired) ∧
        arrive repaired oriented.2 = (oriented.1, repaired) := by
  have happroach : PhysicalTrace w
      (e, A.activatedState) C.selection.before
      (C.selection.repeated.1, C.raw.atContact.2) :=
    C.beforeTrace_to_contact
  have hpaths := C.atContact_support_grooves hApaths
  have hswitch : passageSwitch C.raw.split.hit =
      C.selection.repeated.1 / 3 := by
    simpa [passageSwitch] using C.raw.split.sameSwitch
  exact A.protected_changed_contact_periodic_or_forward
    (route := C.selection.before ++ [C.selection.repeated])
    (approach := C.selection.before) (suffix := [])
    (by simp) C.before_contact_simple happroach hpaths harrive
    D.path_mem D.hit_mem hswitch hchanged

/-- A no-change support contact is either the exact backward retrace/replay
lasso or is already the forward passage on the old reflector's selected
route.  This is the facing counterpart of
`changed_periodic_or_forward`, stated directly for the raw union contact. -/
theorem UnionOldSupportReach.facing_periodic_or_forward
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage} {finish : Nat × Tongues}
    {C : UnionOldTrackedShrink w N A fresh finish}
    (D : UnionOldSupportReach C)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (harrive :
      arrive C.raw.atContact.2 C.selection.repeated.1 =
        (C.selection.repeated.2, C.raw.atContact.2)) :
    EventuallyPeriodic w (e, A.activatedState) ∨
      C.selection.repeated ∈ A.orientedRoute C.raw.atContact.2 := by
  let state := C.raw.atContact.2
  have hpaths : PathGrooves A.toSupported.paths state := by
    simpa [state] using C.atContact_support_grooves hApaths
  have hgroove :
      arrive state C.raw.split.hit.2 =
        (C.raw.split.hit.1, state) :=
    hpaths D.path D.path_mem C.raw.split.hit D.hit_mem
  have hsameSwitch : passageSwitch C.raw.split.hit =
      passageSwitch C.selection.repeated :=
    C.raw.split.sameSwitch
  have hpassage : C.selection.repeated = C.raw.split.hit ∨
      C.selection.repeated =
        (C.raw.split.hit.2, C.raw.split.hit.1) := by
    apply grooved_same_switch_passages_eq_or_reverse hgroove
    · simpa [state] using harrive
    · exact hsameSwitch
  obtain ⟨oriented, horiented, horientation⟩ :=
    A.support_passage_on_orientedRoute state D.path_mem D.hit_mem
  have hbackward :
      C.selection.repeated = (oriented.2, oriented.1) →
        EventuallyPeriodic w (e, A.activatedState) := by
    intro hreverse
    obtain ⟨recorded, tail, hsplit⟩ := List.append_of_mem horiented
    have hroute := A.orientedRoute_trace state hpaths
    have hsimple := A.orientedRoute_simple state
    have hrouteGrooved := hroute.grooved_of_switchSimple hsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hroute hsplit hrouteGrooved hsimple
    have hrecorded := hprefixData.1
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hsimple ⊢
      rw [hsplit] at hsimple
      simp only [List.map_append, List.map_cons] at hsimple
      exact (List.nodup_append.mp hsimple).1
    have hrecordedGrooved : PassagesGrooved state recorded :=
      hrecorded.grooved_of_switchSimple hrecordedSimple
    have happroach := C.beforeTrace_to_contact
    have happroachSimple : SwitchSimple C.selection.before := by
      have hs := C.before_contact_simple
      unfold SwitchSimple at hs ⊢
      rw [List.map_append] at hs
      exact (List.nodup_append.mp hs).1
    have happroachGrooved :
        PassagesGrooved state C.selection.before := by
      exact happroach.grooved_of_switchSimple happroachSimple
    have hcontact : arrive state C.selection.repeated.1 =
        (oriented.1, state) := by
      simpa [hreverse, state] using harrive
    have hsettles := backward_contact_settles_grooved_cycle
      hrecorded hrecordedGrooved A.entryEdge hcontact
      happroach happroachGrooved
    exact eventuallyPeriodic_of_reaches_simple_cycle
      happroach.sound hsettles
  rcases hpassage with hsame | hreverse <;>
    rcases horientation with horientedSame | horientedReverse
  · right
    simpa [hsame, horientedSame] using horiented
  · left
    apply hbackward
    rw [hsame, horientedReverse]
  · left
    apply hbackward
    rw [hreverse, horientedSame]
  · right
    simpa [hreverse, horientedReverse] using horiented

/-- A changed passage in a switch-simple trace survives to the endpoint.

This is the converse accounting bridge to
`PhysicalTrace.changed_switch_has_changed_passage`: simplicity excludes the
changed switch from both sides of the displayed split, so the prefix and
suffix preserve that coordinate. -/
theorem PhysicalTrace.simple_changed_passage_survives_explicit_switch
    {w : Wiring} {start finish : Prod Nat Tongues}
    {passages before after : List Passage}
    {p x k : Nat} {u v : Tongues}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hsplit : passages = before ++ (p, x) :: after)
    (hbefore : PhysicalTrace w start before (p, u))
    (harrive : arrive u p = (x, v))
    (hswitch : passageSwitch (p, x) = k)
    (hchanged : Not (v k = u k)) :
    Not (finish.2 k = start.2 k) := by
  classical
  rw [hsplit] at htrace hsimple
  let middle := Classical.choose htrace.split_append
  have hsplitTrace := Classical.choose_spec htrace.split_append
  have hprefix := hsplitTrace.1
  have hrest := hsplitTrace.2
  have hmiddle : middle = (p, u) := by
    have hprefixSound := hprefix.sound
    have hbeforeSound := hbefore.sound
    rw [hprefixSound] at hbeforeSound
    exact Option.some.inj hbeforeSound
  have hrest' : PhysicalTrace w (p, u) ((p, x) :: after) finish := by
    exact Eq.mp
      (congrArg (fun c => PhysicalTrace w c ((p, x) :: after) finish) hmiddle)
      hrest
  cases hrest' with
  | @cons _ _ q _ v' _ _ harrive' hlink hafter =>
      have hv' : v' = v := by
        rw [harrive] at harrive'
        injection harrive' with _ hv
        exact hv.symm
      subst v'
      unfold SwitchSimple at hsimple
      simp only [List.map_append, List.map_cons] at hsimple
      have hparts := List.nodup_append.mp hsimple
      have hbeforeForeign :
          forall prior, List.Mem prior before ->
            Not (passageSwitch prior = k) := by
        intro prior hprior hEq
        have hpriorMap : List.Mem (passageSwitch prior)
            (List.map passageSwitch before) :=
          List.mem_map.mpr (Exists.intro prior (And.intro hprior rfl))
        have hheadMap : List.Mem (passageSwitch (p, x))
            (passageSwitch (p, x) :: List.map passageSwitch after) :=
          List.mem_cons_self
        have hne := hparts.2.2 (passageSwitch prior) hpriorMap
          (passageSwitch (p, x)) hheadMap
        apply hne
        rw [hEq, hswitch]
      have hafterForeign :
          forall later, List.Mem later after ->
            Not (passageSwitch later = k) := by
        have hheadTail := hparts.2.1
        rw [List.nodup_cons] at hheadTail
        intro later hlater hEq
        apply hheadTail.1
        apply List.mem_map.mpr
        exact Exists.intro later (And.intro hlater (by rw [hEq, hswitch]))
      have hu : u k = start.2 k :=
        hbefore.preserves k hbeforeForeign
      have hv : finish.2 k = v k :=
        hafter.preserves k hafterForeign
      intro hfinish
      apply hchanged
      exact hv.symm.trans (hfinish.trans hu.symm)

/-- If the endpoint tongue at the displayed passage's switch agrees with the
start tongue, then that passage was locally quiet. -/
theorem PhysicalTrace.simple_passage_quiet_of_endpoint_eq
    {w : Wiring} {start finish : Prod Nat Tongues}
    {passages before after : List Passage}
    {p x k : Nat} {u v : Tongues}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hsplit : passages = before ++ (p, x) :: after)
    (hbefore : PhysicalTrace w start before (p, u))
    (harrive : arrive u p = (x, v))
    (hswitch : passageSwitch (p, x) = k)
    (hsame : finish.2 k = start.2 k) :
    v k = u k := by
  classical
  apply Classical.byContradiction
  intro hchanged
  exact (htrace.simple_changed_passage_survives_explicit_switch hsimple hsplit hbefore
    harrive hswitch hchanged) hsame

/-- If the old support is grooved both before and after a switch-simple
manufacturing exploration, every exploration passage on an old reusable
switch is locally unproductive.  Therefore all productive construction
writes are outside the reusable old support. -/
theorem ManufacturedReflector.exploration_support_passage_quiet
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : PathGrooves A.toSupported.paths B.baseState)
    (hfinish : PathGrooves A.toSupported.paths B.preReturn.2)
    {before after : List Passage} {p x : Nat} {u v : Tongues}
    (hsplit : B.exploration = before ++ (p, x) :: after)
    (hbefore : PhysicalTrace w (e, B.baseState) before (p, u))
    (harrive : arrive u p = (x, v))
    (htouch : A.TouchesSupport (p, x)) :
    v (passageSwitch (p, x)) = u (passageSwitch (p, x)) := by
  classical
  let path := Classical.choose htouch
  have hpathData := Classical.choose_spec htouch
  have hpathMem : List.Mem path A.toSupported.paths := hpathData.1
  let old := Classical.choose hpathData.2
  have holdData := Classical.choose_spec hpathData.2
  have holdMem : List.Mem old path := holdData.1
  have holdSwitch : passageSwitch old = passageSwitch (p, x) :=
    holdData.2
  have hsameOld := same_groove_same_tongue
    (hbase path hpathMem old holdMem)
    (hfinish path hpathMem old holdMem)
  have hsame : B.preReturn.2 (passageSwitch (p, x)) =
      B.baseState (passageSwitch (p, x)) := by
    simpa [holdSwitch] using hsameOld.symm
  exact B.exploration_trace.simple_passage_quiet_of_endpoint_eq
    B.exploration_simple hsplit hbefore harrive rfl hsame

/-- In the endpoint-groove-preserved branch the two complete manufacturing
journeys have coefficient one, and the uniform protected-repair theorem
supplies the constant four-state tail. -/
theorem two_manufacturing_journeys_preserved_support_known_edge_le_N_add_six
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (A : ManufacturedReflector w start.1 e)
    (B : ManufacturedReflector w e start.1)
    (stateA stateB : Tongues)
    (hbaseA : A.baseState = start.2)
    (hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hgroovesA : PathGrooves A.toSupported.paths stateA)
    (hbaseB : B.baseState = stateA)
    (hactivatedB : stateB = B.activatedState)
    (hreachB : stepN w
      (B.exploration.length + B.runway.length + 1)
        (e, stateA) = some (start.1, stateB))
    (hgroovesB : PathGrooves B.toSupported.paths stateB)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : forall k, Membership.mem times k ->
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    Nat.le times.length (N + 6) := by
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    simpa [hbaseB] using hgroovesA
  have hBatActivated :
      PathGrooves B.toSupported.paths B.activatedState := by
    simpa [hactivatedB] using hgroovesB
  have htail : forall tailTimes : List Nat,
      (forall k, Membership.mem tailTimes k ->
        (stepN w k (start.1, stateB)).isSome) ->
      (tailTimes.map (restrictedTonguesAt w N
        (start.1, stateB))).Nodup ->
      Nat.le tailTimes.length 4 := by
    intro tailTimes htailLive htailNodup
    simpa [hactivatedB] using
      (manufactured_pair_protected_repair_distinct_le_four
        A B hAatBase hBatActivated tailTimes
          (by simpa [hactivatedB] using htailLive)
          (by simpa [hactivatedB] using htailNodup))
  exact two_manufacturing_journeys_preserved_support_then_four_tail_le_N_add_six
    hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
      hbaseB hactivatedB hreachB hgroovesB hpreGrooves htail
      times hlive hnd

/-- A first damaging old-support passage closes the complementary branch
without recursion.  Productive writers before the contact are charged only
when they lie outside the old reusable support.  The resulting compressed
history has size at most `N+3`, and the exact changing-contact continuation
adds at most two vectors. -/
theorem ManufacturedReflector.first_damaging_support_all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hbroken : Not (PathGrooves A.toSupported.paths B.preReturn.2))
    (times : List Nat)
    (hlive : forall k, Membership.mem times k ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    Nat.le times.length (N + 5) := by
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  obtain ⟨approach, p, x, suffix, u, v, path, old,
      hsplit, hprefix, hgrooves, harrive,
      hpath, hold, hswitch, hchanged, _hexit⟩ :=
    B.exploration_trace.first_changed_support_passage
      hbaseGrooves hbroken
  have hfull := B.exploration_trace
  rw [hsplit] at hfull
  obtain hparts := hfull.split_append
  let middle := Classical.choose hparts
  have hpartsSpec := Classical.choose_spec hparts
  have hbefore := hpartsSpec.1
  have hafter := hpartsSpec.2
  have hmiddle : middle = (p, u) := by
    have h1 := hbefore.sound
    have h2 := hprefix.sound
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  have hafter' :
      PhysicalTrace w (p, u) ((p, x) :: suffix) B.preReturn := by
    exact Eq.mp
      (congrArg
        (fun c => PhysicalTrace w c ((p, x) :: suffix) B.preReturn)
        hmiddle)
      hafter
  let C : SecondHistoryContactData w A B := {
    approach := approach
    fresh := (p, x)
    suffix := suffix
    contactState := u
    split := hsplit
    approach_trace := hprefix
    suffix_trace := hafter'
    old_grooves := hgrooves
    touches := Exists.intro path
      (And.intro hpath
        (Exists.intro old
          (And.intro hold (by
            simpa [passageSwitch] using hswitch))))
  }
  have harriveC :
      arrive C.contactState C.fresh.1 = (C.fresh.2, v) := by
    simpa [C] using harrive
  have hchangedC :
      Not (v (C.fresh.1 / 3) = C.contactState (C.fresh.1 / 3)) := by
    simpa [C] using hchanged
  let firstTravel := A.exploration.length + A.runway.length + 1
  let localTimes :=
    (times.filter (fun k => decide (firstTravel < k))).map
      (fun k => k - firstTravel)
  let history := C.damageContactHistory N v
  have hreachA :
      stepN w firstTravel (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hreachBoundary :
      stepN w firstTravel (g, A.baseState) =
        some (e, B.baseState) := by
    simpa [hbase] using hreachA
  have hlocalCover :
      NoveltyCoverOn w N (e, B.baseState) localTimes history 2 := by
    dsimp [localTimes, history]
    exact C.changed_contact_two_novelty_charged
      harriveC hchangedC _
  rcases hlocalCover with ⟨fresh, hfreshLength, hlocalMem⟩
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times history 2 := by
    refine Exists.intro fresh (And.intro hfreshLength ?_)
    intro k hk
    by_cases hprefixTime : k <= firstTravel
    · have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hA (j := k) (by
          simpa [firstTravel] using hprefixTime)
      apply List.mem_append_left
      dsimp [history]
      unfold SecondHistoryContactData.damageContactHistory
      exact List.mem_append_left _
        (A.mem_sharpHistoryCore_of_mem hm)
    · have hafterTime : firstTravel < k := by omega
      let q := k - firstTravel
      have hkEq : k = firstTravel + q := by
        dsimp [q]
        omega
      have hkFiltered :
          Membership.mem
            (times.filter (fun t => decide (firstTravel < t))) k := by
        apply List.mem_filter.mpr
        exact And.intro hk (by simp [hafterTime])
      have hqMem : Membership.mem localTimes q := by
        dsimp [localTimes]
        apply List.mem_map.mpr
        exact Exists.intro k (And.intro hkFiltered rfl)
      have hglobalLive := hlive k hk
      have hlocalLive :
          (stepN w q (e, B.baseState)).isSome := by
        rw [hkEq, stepN_add, hreachBoundary] at hglobalLive
        exact hglobalLive
      have hlocalReach :
          Exists fun finish =>
            stepN w q (e, B.baseState) = some finish := by
        cases hq : stepN w q (e, B.baseState) with
        | none => simp [hq] at hlocalLive
        | some finish => exact Exists.intro finish rfl
      have hshift :=
        tonguesAt_add_of_reaches hreachBoundary hlocalReach
      have hvector :
          restrictedTonguesAt w N (g, A.baseState) k =
            restrictedTonguesAt w N (e, B.baseState) q := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [hvector]
      exact hlocalMem q hqMem
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory : history.length <= N + 3 := by
    dsimp [history]
    exact C.damageContactHistory_length_le_N_add_three
      hN hbase hbaseGrooves v
  exact Nat.le_trans hcount (by omega)

/-- Exact all-time old-contact continuation for two opposite manufactured
reflectors.  Harmless old-support overlaps are free: either all old grooves
survive to pre-return and the verified four-state protected tail applies, or
the first damaging passage invokes the coefficient-one `N+5` theorem above.
No residual-support recursion or selector is assumed. -/
theorem two_manufacturing_journeys_first_damage_or_preserved_support_known_edge_le_N_add_six
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (A : ManufacturedReflector w start.1 e)
    (B : ManufacturedReflector w e start.1)
    (stateA stateB : Tongues)
    (hbaseA : A.baseState = start.2)
    (hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hgroovesA : PathGrooves A.toSupported.paths stateA)
    (hbaseB : B.baseState = stateA)
    (hactivatedB : stateB = B.activatedState)
    (hreachB : stepN w
      (B.exploration.length + B.runway.length + 1)
        (e, stateA) = some (start.1, stateB))
    (hgroovesB : PathGrooves B.toSupported.paths stateB)
    (times : List Nat)
    (hlive : forall k, Membership.mem times k ->
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    Nat.le times.length (N + 6) := by
  by_cases hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2
  · exact
      two_manufacturing_journeys_preserved_support_known_edge_le_N_add_six
        hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
          hbaseB hactivatedB hreachB hgroovesB hpreGrooves
          times hlive hnd
  · have hbase : B.baseState = A.activatedState :=
      hbaseB.trans hactivatedA
    have hA : PathGrooves A.toSupported.paths A.activatedState := by
      simpa [hactivatedA] using hgroovesA
    have hlive' : forall k, Membership.mem times k ->
        (stepN w k (start.1, A.baseState)).isSome := by
      simpa [hbaseA] using hlive
    have hnd' :
        (times.map (restrictedTonguesAt w N
          (start.1, A.baseState))).Nodup := by
      simpa [hbaseA] using hnd
    have hdamaged :=
      A.first_damaging_support_all_run_distinct_le_N_add_five
        hN B hbase hA hpreGrooves times hlive' hnd'
    exact Nat.le_trans hdamaged (by omega)

end GeneralN
