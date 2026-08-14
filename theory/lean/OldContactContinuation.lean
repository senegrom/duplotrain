import TwoHistoryUnionCharge
import ShrinkingCurveFinal
import JourneyReachesActivated
import FirstCycleCountSharp
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

structure UnionOldTrackedShrink
    (w : Wiring) (N : Nat)
    {g e : Nat} (A : ManufacturedReflector w g e)
    (fresh : List Passage) (finish : Nat × Tongues) : Type where
  selection : UnionFirstRepeat A.exploration fresh
  raw :
    RawUnionOldContactShrink w N A.exploration fresh selection
      (e, A.activatedState) finish


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

end GeneralN
