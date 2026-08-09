import MellitGlobalNoveltyBound

/-!
# Mellit's direct first/second-repeat state bound

This module works directly with finite `PhysicalTrace`s and manufactured
reflectors.  Its second repeat is selected against the union of the first
reflector's entire outward exploration and the fresh post-return prefix.
Consequently an internal repeat manufactures a reflector whose exploration
is switch-disjoint from the first one; compatibility is then a theorem, not
an additional premise.  A contact with the old exploration is retained for
the strictly-decreasing first-contact recursion developed below.

Everything is general in `N`.  No finite enumeration is used.
-/

namespace GeneralN

/-! ## First repetition against an old support plus a fresh prefix -/

/-- The canonical first repetition of `fresh` against the union of `old`
and the already inspected fresh prefix.  `combinedSimple` says that no
repetition occurred earlier. -/
structure UnionFirstRepeat (old fresh : List Passage) : Type where
  before : List Passage
  repeated : Passage
  after : List Passage
  split : fresh = before ++ repeated :: after
  combinedSimple : SwitchSimple (old ++ before)
  repeats : passageSwitch repeated ∈
    (old ++ before).map passageSwitch

/-- The source of a first union repetition is exact: it either hits the old
exploration or repeats a switch already used in the fresh prefix. -/
theorem UnionFirstRepeat.old_or_internal
    {old fresh : List Passage}
    (R : UnionFirstRepeat old fresh) :
      passageSwitch R.repeated ∈ old.map passageSwitch ∨
      passageSwitch R.repeated ∈ R.before.map passageSwitch := by
  have h := R.repeats
  rw [List.map_append] at h
  exact List.mem_append.mp h

private theorem simple_append_singleton
    {old : List Passage} {fresh : Passage}
    (hold : SwitchSimple old)
    (hfresh : passageSwitch fresh ∉ old.map passageSwitch) :
    SwitchSimple (old ++ [fresh]) := by
  unfold SwitchSimple at hold ⊢
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨hold, by simp, ?_⟩
  intro a ha b hb
  simp only [List.map_singleton, List.mem_singleton] at hb
  subst b
  exact fun hab => hfresh (hab ▸ ha)

private theorem union_first_repeat_aux :
    ∀ (old fresh : List Passage),
      SwitchSimple old →
      ¬ SwitchSimple (old ++ fresh) →
      Nonempty (UnionFirstRepeat old fresh) := by
  intro old fresh
  induction fresh generalizing old with
  | nil =>
      intro hold hbad
      exact (hbad (by simpa using hold)).elim
  | cons head tail ih =>
      intro hold hbad
      by_cases hhead :
          passageSwitch head ∈ old.map passageSwitch
      · exact ⟨{
          before := []
          repeated := head
          after := tail
          split := rfl
          combinedSimple := by simpa using hold
          repeats := by simpa using hhead
        }⟩
      · have holdHead : SwitchSimple (old ++ [head]) :=
          simple_append_singleton hold hhead
        have hbadTail :
            ¬ SwitchSimple ((old ++ [head]) ++ tail) := by
          simpa [List.append_assoc] using hbad
        obtain ⟨R⟩ := ih (old ++ [head]) holdHead hbadTail
        exact ⟨{
          before := head :: R.before
          repeated := R.repeated
          after := R.after
          split := by simp [R.split]
          combinedSimple := by
            simpa [List.append_assoc] using R.combinedSimple
          repeats := by
            simpa [List.append_assoc] using R.repeats
        }⟩

/-- Every nonsimple union with a simple old prefix has a canonical first
repetition in the fresh suffix. -/
theorem first_repeat_against_union
    (old fresh : List Passage)
    (hold : SwitchSimple old)
    (hbad : ¬ SwitchSimple (old ++ fresh)) :
    Nonempty (UnionFirstRepeat old fresh) :=
  union_first_repeat_aux old fresh hold hbad

/-! ## Switch-disjoint explorations force reflector compatibility -/

/-- Every retained support passage of a manufactured reflector occurs in
its outward exploration. -/
theorem ManufacturedReflector.support_switch_mem_exploration
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    {path : List Passage} {passage : Passage}
    (hpath : path ∈ A.toSupported.paths)
    (hpassage : passage ∈ path) :
    passageSwitch passage ∈ A.exploration.map passageSwitch := by
  cases A with
  | stay R =>
      simp only [ManufacturedReflector.toSupported,
        ManufacturedStayReflector.toSupported,
        ManufacturedReflector.exploration,
        List.mem_cons, List.not_mem_nil, or_false] at hpath ⊢
      rcases hpath with rfl | rfl
      · rw [List.map_append]
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨passage, hpassage, rfl⟩)
      · simp only [List.mem_singleton] at hpassage
        subst passage
        rw [List.map_append]
        exact List.mem_append_right _ (by simp [passageSwitch])
  | flip R =>
      simp only [ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported,
        ManufacturedReflector.exploration,
        List.mem_cons, List.not_mem_nil, or_false] at hpath ⊢
      rcases hpath with rfl | rfl
      · rw [List.map_append]
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨passage, hpassage, rfl⟩)
      · rw [List.map_append]
        exact List.mem_append_right _
          (List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨passage, hpassage, rfl⟩))

/-- The action switch of a nondegenerate manufactured reflector occurs in
its own exploration. -/
theorem ManufacturedFlipReflector.actionSwitch_mem_exploration
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    A.actionSwitch ∈
      (ManufacturedReflector.flip A).exploration.map passageSwitch := by
  simp [ManufacturedReflector.exploration,
    ManufacturedFlipReflector.actionSwitch, passageSwitch]

/-- **Compatibility from combined first-contact minimality.**  If the two
outward explorations are switch-simple as one concatenated list, then each
reflector's local action avoids every retained support passage of the other.
-/
theorem manufactured_pair_compatible_of_explorations_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hsimple : SwitchSimple (A.exploration ++ B.exploration)) :
    A.toSupported.action.Avoids B.toSupported.paths ∧
      B.toSupported.action.Avoids A.toSupported.paths := by
  unfold SwitchSimple at hsimple
  rw [List.map_append] at hsimple
  have hcross := (List.nodup_append.mp hsimple).2.2
  constructor
  · cases A with
    | stay A => trivial
    | flip A =>
        intro path hpath passage hpassage
        have haction := A.actionSwitch_mem_exploration
        have hsupport := B.support_switch_mem_exploration
          hpath hpassage
        exact (hcross A.actionSwitch haction
          (passageSwitch passage) hsupport).symm
  · cases B with
    | stay B => trivial
    | flip B =>
        intro path hpath passage hpassage
        have hsupport := A.support_switch_mem_exploration
          hpath hpassage
        have haction := B.actionSwitch_mem_exploration
        exact hcross (passageSwitch passage) hsupport
          B.actionSwitch haction

end GeneralN
