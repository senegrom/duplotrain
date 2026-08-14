import KoizumiCurveInvariant
import MellitDirectStateBound

/-!
# The well-founded shrinking-curve invariant

This file closes the purely combinatorial termination part of the
Koizumi/Mellit first-contact argument.

`UnionFirstRepeat old fresh` selects the first passage in `fresh` whose
switch has already occurred in `old` or in the preceding fresh prefix. If
that passage contacts `old`, its unique occurrence splits the switch-simple
old exploration into two residual supports. Both residual supports are
strict tracked subcurves. Thus either orientation has a strictly smaller
support/contact rank.

The final strong-recursion theorem is fully general in `N`: any construction
whose recursive calls are made only on strict tracked subcurves terminates.
No finite enumeration is used.

This does **not** prove `GeneralN.StateLaw`. The remaining dynamic bridge is
to show, from an arbitrary raw `Wiring.stepN` run after each turnaround, that
the next unresolved case supplies the `UnionFirstRepeat`/old-contact data
below and that its continuation is represented by one residual support.
Once that bridge is proved, infinite old-contact nesting is no longer open.
-/

namespace GeneralN

/-- The exact ordered split made when a first union-repeat contacts the old
exploration. -/
structure UnionOldContactSplit
    (old fresh : List Passage) (R : UnionFirstRepeat old fresh) : Type where
  hit : Passage
  beforeHit : List Passage
  afterHit : List Passage
  split : old = beforeHit ++ (hit :: afterHit)
  sameSwitch : passageSwitch hit = passageSwitch R.repeated

def UnionOldContactSplit.contactIndex
    {old fresh : List Passage} {R : UnionFirstRepeat old fresh}
    (S : UnionOldContactSplit old fresh R) : Nat :=
  S.beforeHit.length

theorem UnionOldContactSplit.contactIndex_lt
    {old fresh : List Passage} {R : UnionFirstRepeat old fresh}
    (S : UnionOldContactSplit old fresh R) :
    S.contactIndex < old.length := by
  unfold UnionOldContactSplit.contactIndex
  have hlen := congrArg List.length S.split
  simp only [List.length_append, List.length_cons] at hlen
  omega

theorem UnionOldContactSplit.after_length_lt
    {old fresh : List Passage} {R : UnionFirstRepeat old fresh}
    (S : UnionOldContactSplit old fresh R) :
    S.afterHit.length < old.length := by
  have hlen := congrArg List.length S.split
  simp only [List.length_append, List.length_cons] at hlen
  omega

theorem UnionOldContactSplit.exact_length_split
    {old fresh : List Passage} {R : UnionFirstRepeat old fresh}
    (S : UnionOldContactSplit old fresh R) :
    S.beforeHit.length + 1 + S.afterHit.length = old.length := by
  have hlen := congrArg List.length S.split
  simp only [List.length_append, List.length_cons] at hlen
  omega

/-- Contact with the old exploration produces an exact split. The uniqueness
of its switch occurrence follows from `R.combinedSimple`; the split itself
only needs the retained old-contact membership. -/
theorem UnionFirstRepeat.old_contact_split
    {old fresh : List Passage}
    (R : UnionFirstRepeat old fresh)
    (hOld : passageSwitch R.repeated ∈ old.map passageSwitch) :
    Nonempty (UnionOldContactSplit old fresh R) := by
  obtain ⟨hit, hhit, hsame⟩ := List.mem_map.mp hOld
  obtain ⟨beforeHit, afterHit, hsplit⟩ := List.append_of_mem hhit
  exact ⟨{
    hit := hit
    beforeHit := beforeHit
    afterHit := afterHit
    split := hsplit
    sameSwitch := hsame
  }⟩

/-- The tracked-curve form of the split. Both orientations are retained. -/
structure UnionOldContactShrink (N : Nat)
    {old fresh : List Passage} {R : UnionFirstRepeat old fresh}
    (S : UnionOldContactSplit old fresh R) : Type where
  outer : TrackedEndpointCurve N
  left : TrackedEndpointCurve N
  right : TrackedEndpointCurve N
  outer_switches : outer.switches = old.map passageSwitch
  left_switches : left.switches = S.beforeHit.map passageSwitch
  right_switches : right.switches = S.afterHit.map passageSwitch
  left_strict : StrictTrackedSubcurve left outer
  right_strict : StrictTrackedSubcurve right outer

def TrackedEndpointCurve.supportContactRank
    {N : Nat} (D : TrackedEndpointCurve N) : Nat :=
  D.switches.length

theorem UnionOldContactSplit.toTrackedShrink
    {N : Nat} {old fresh : List Passage}
    {R : UnionFirstRepeat old fresh}
    (S : UnionOldContactSplit old fresh R)
    (hRange : ∀ passage, passage ∈ old → passageSwitch passage < N) :
    Nonempty (UnionOldContactShrink N S) := by
  have hcombined :
      (old.map passageSwitch ++ R.before.map passageSwitch).Nodup := by
    simpa only [SwitchSimple, List.map_append] using R.combinedSimple
  have houterNodup : (old.map passageSwitch).Nodup :=
    (List.nodup_append.mp hcombined).1
  have hsplitNodup :
      (S.beforeHit.map passageSwitch ++
        passageSwitch S.hit :: S.afterHit.map passageSwitch).Nodup := by
    simpa only [S.split, List.map_append, List.map_cons] using houterNodup
  have hbeforeNodup : (S.beforeHit.map passageSwitch).Nodup :=
    (List.nodup_append.mp hsplitNodup).1
  have hafterNodup : (S.afterHit.map passageSwitch).Nodup :=
    (List.nodup_cons.mp (List.nodup_append.mp hsplitNodup).2.1).2
  have houterRange : ∀ C, C ∈ old.map passageSwitch → C < N := by
    intro C hC
    obtain ⟨passage, hp, rfl⟩ := List.mem_map.mp hC
    exact hRange passage hp
  have hbeforeRange :
      ∀ C, C ∈ S.beforeHit.map passageSwitch → C < N := by
    intro C hC
    apply houterRange C
    rw [S.split]
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
    exact Or.inl hC
  have hafterRange :
      ∀ C, C ∈ S.afterHit.map passageSwitch → C < N := by
    intro C hC
    apply houterRange C
    rw [S.split]
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
    exact Or.inr (Or.inr hC)
  let outer : TrackedEndpointCurve N := {
    switches := old.map passageSwitch
    simple := houterNodup
    inRange := houterRange
  }
  let left : TrackedEndpointCurve N := {
    switches := S.beforeHit.map passageSwitch
    simple := hbeforeNodup
    inRange := hbeforeRange
  }
  let right : TrackedEndpointCurve N := {
    switches := S.afterHit.map passageSwitch
    simple := hafterNodup
    inRange := hafterRange
  }
  have hleft : StrictTrackedSubcurve left outer := by
    constructor
    · intro C hC
      change C ∈ S.beforeHit.map passageSwitch at hC
      change C ∈ old.map passageSwitch
      rw [S.split]
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      exact Or.inl hC
    · dsimp [left, outer]
      simp only [List.length_map]
      exact S.contactIndex_lt
  have hright : StrictTrackedSubcurve right outer := by
    constructor
    · intro C hC
      change C ∈ S.afterHit.map passageSwitch at hC
      change C ∈ old.map passageSwitch
      rw [S.split]
      simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inr hC)
    · dsimp [right, outer]
      simp only [List.length_map]
      exact S.after_length_lt
  exact ⟨{
    outer := outer
    left := left
    right := right
    outer_switches := rfl
    left_switches := rfl
    right_switches := rfl
    left_strict := hleft
    right_strict := hright
  }⟩

/-- Raw trace data at the exact contact state. -/
structure RawUnionOldContactShrink
    (w : Wiring) (N : Nat) (old fresh : List Passage)
    (R : UnionFirstRepeat old fresh)
    (start finish : Nat × Tongues) : Type where
  atContact : Nat × Tongues
  beforeTrace : PhysicalTrace w start R.before atContact
  fromContactTrace : PhysicalTrace w atContact
    (R.repeated :: R.after) finish
  split : UnionOldContactSplit old fresh R
  shrink : UnionOldContactShrink N split

end GeneralN
