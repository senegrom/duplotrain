import TrackNormalForm

/-!
# The theta-intersection engine

This file studies the only obstruction left by the supported-reflector normal
form: one reflector flips a switch lying on the other reflector's grooved
support.  The local core is that a flipped groove has only two behaviours.
Approached trailing-first it repairs itself; approached facing-first it leaves
through the third arm.  For a manufactured lobe that third arm is precisely
the entrance into the older reflector, which is the theta capture.
-/

namespace GeneralN

/-! ## Equivariance away from the flipped switch -/

theorem pin_flip_other {u : Tongues} {p k : Nat}
    (hpk : p / 3 ≠ k) :
    pin (flipAt u k) p = flipAt (pin u p) k := by
  funext j
  unfold pin flipAt
  by_cases hjp : j = p / 3
  · subst j
    simp [hpk]
  · by_cases hjk : j = k
    · subst j
      simp [Ne.symm hpk]
    · simp [hjp, hjk]

/-- Flipping an unvisited switch commutes with one local lazy-point
traversal. -/
theorem arrive_flip_other {u v : Tongues} {p x k : Nat}
    (harrive : arrive u p = (x, v))
    (hpk : p / 3 ≠ k) :
    arrive (flipAt u k) p = (x, flipAt v k) := by
  unfold arrive at harrive ⊢
  by_cases hp : p % 3 = 0
  · rw [if_pos hp] at harrive ⊢
    injection harrive with hx hv
    subst x
    subst v
    simp [flipAt, hpk]
  · rw [if_neg hp] at harrive ⊢
    injection harrive with hx hv
    subst x
    rw [pin_flip_other hpk, hv]

/-- A passage which genuinely changes its switch is necessarily trailing:
its entry is a branch, its exit is the stem, and immediately re-entering
that stem follows the freshly selected branch back.  This is the local
algebra behind the forward theta splice. -/
theorem changed_arrival_is_trailing
    {u v : Tongues} {p x : Nat}
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    p % 3 ≠ 0 ∧ x = 3 * (p / 3) ∧ v = pin u p := by
  by_cases hp : p % 3 = 0
  · have hpair := harrive
    simp only [arrive, hp, if_pos] at hpair
    have hv : v = u := (congrArg Prod.snd hpair).symm
    exact (hchanged (by rw [hv])).elim
  · have hpair := harrive
    simp only [arrive, hp] at hpair
    have hx : x = 3 * (p / 3) := (congrArg Prod.fst hpair).symm
    have hv : v = pin u p := (congrArg Prod.snd hpair).symm
    exact ⟨hp, hx, hv⟩

theorem changed_arrival_eq_flipAt
    {u v : Tongues} {p x : Nat}
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    v = flipAt u (p / 3) := by
  obtain ⟨_hp, _hx, hv⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hpinValue : v (p / 3) = bval p := by
    rw [hv]
    simp [pin]
  have hopposite : bval p = !(u (p / 3)) := by
    cases hu : u (p / 3) <;> cases hb : bval p <;>
      simp_all
  exact hv.trans (pin_eq_flipAt rfl hopposite)

theorem trailing_arrive_exit_independent
    {u v : Tongues} {p : Nat} (hp : p % 3 ≠ 0) :
    (arrive u p).1 = (arrive v p).1 := by
  simp [arrive, hp]

theorem physicalTrace_passages_prefix_comparable
    {w : Wiring} {start finishA finishB : Nat × Tongues}
    {left right : List Passage}
    (hleft : PhysicalTrace w start left finishA)
    (hright : PhysicalTrace w start right finishB) :
    (∃ suffix, right = left ++ suffix) ∨
      (∃ suffix, left = right ++ suffix) := by
  induction hleft generalizing right finishB with
  | nil c =>
      exact Or.inl ⟨right, by simp⟩
  | @cons p x q u v rest finishA harrive hlink tail ih =>
      cases hright with
      | nil =>
          exact Or.inr ⟨(p, x) :: rest, by simp⟩
      | @cons _ x₂ q₂ _ v₂ right finishB harrive₂ hlink₂ tail₂ =>
          have hlocal : (x, v) = (x₂, v₂) :=
            harrive.symm.trans harrive₂
          injection hlocal with hx hv
          subst x₂
          subst v₂
          have hnext : q = q₂ := by
            rw [hlink] at hlink₂
            injection hlink₂
          subst q₂
          rcases ih tail₂ with hprefix | hprefix
          · obtain ⟨suffix, hsuffix⟩ := hprefix
            exact Or.inl ⟨suffix, by simp [hsuffix]⟩
          · obtain ⟨suffix, hsuffix⟩ := hprefix
            exact Or.inr ⟨suffix, by simp [hsuffix]⟩

theorem forward_contact_repairs_old_passage
    {u v : Tongues} {oldEntry oldExit freshEntry : Nat}
    (hold : arrive u oldExit = (oldEntry, u))
    (hfresh : arrive u freshEntry = (oldExit, v))
    (hswitch : oldEntry / 3 = freshEntry / 3) :
    ∃ repaired,
      arrive v oldEntry = (oldExit, repaired) ∧
      arrive repaired oldExit = (oldEntry, repaired) := by
  grind [arrive_back, arrive_exit_ne, arrive_exit_switch, trailing_arrive_exit_independent]

/-- Degree-three local contact law, stated early for the orientation package:
a fresh passage through a switch carrying an old groove must exit through one
of the two old passage ports. -/
theorem grooved_contact_exit_dichotomy
    {state next : Tongues}
    {oldEntry oldExit freshEntry freshExit : Nat}
    (hold : arrive state oldExit = (oldEntry, state))
    (hfresh : arrive state freshEntry = (freshExit, next))
    (hswitch : oldEntry / 3 = freshEntry / 3) :
    freshExit = oldEntry ∨ freshExit = oldExit := by
  grind [groove_forward, same_switch_passages_share_port]

/-- A complete physical trace can be replayed after flipping a switch absent
from the trace.  Every intermediate state is simply conjugated by that flip.
-/
theorem PhysicalTrace.flip_unvisited
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {k : Nat}
    (htrace : PhysicalTrace w start passages finish)
    (hforeign : ∀ passage ∈ passages,
      passageSwitch passage ≠ k) :
    PhysicalTrace w (start.1, flipAt start.2 k) passages
      (finish.1, flipAt finish.2 k) := by
  induction htrace with
  | nil c => exact PhysicalTrace.nil _
  | @cons p x q u v passages finish harrive hlink tail ih =>
      have hpk : p / 3 ≠ k := by
        simpa [passageSwitch] using
          hforeign (p, x) List.mem_cons_self
      have harrive' := arrive_flip_other harrive hpk
      apply PhysicalTrace.cons harrive' hlink
      apply ih
      intro passage hp
      exact hforeign passage (List.mem_cons_of_mem _ hp)

theorem physicalTrace_grooved_passages
    (w : Wiring) (u : Tongues) (p x q : Nat)
    (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hfinal : w.link (lastPassageExit x rest) = some q) :
    PhysicalTrace w (p, u) ((p, x) :: rest) (q, u) := by
  induction rest generalizing p x with
  | nil =>
      have hforward := groove_forward
        (hgrooved (p, x) List.mem_cons_self)
      exact PhysicalTrace.cons hforward hfinal (PhysicalTrace.nil _)
  | cons passage rest ih =>
      rcases passage with ⟨r, y⟩
      have hxy : w.link x = some r := hlinked.1
      have htailLinked : LinkedPassages w ((r, y) :: rest) := hlinked.2
      have htailGrooved : PassagesGrooved u ((r, y) :: rest) := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      have htailFinal : w.link (lastPassageExit y rest) = some q := by
        simpa [lastPassageExit] using hfinal
      have htail := ih r y htailLinked htailGrooved htailFinal
      have hforward := groove_forward
        (hgrooved (p, x) List.mem_cons_self)
      exact PhysicalTrace.cons hforward hxy htail

/-- Replay any recorded physical trace in a state that grooves all of its
passages.  The replay changes no tongue. -/
theorem PhysicalTrace.replay_grooved
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (state : Tongues)
    (hgrooved : PassagesGrooved state passages) :
    PhysicalTrace w (start.1, state) passages (finish.1, state) := by
  induction htrace with
  | nil c => exact PhysicalTrace.nil _
  | @cons p x q u v passages finish harrive hlink tail ih =>
      have hhead := groove_forward
        (hgrooved (p, x) List.mem_cons_self)
      have htail : PassagesGrooved state passages := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      exact PhysicalTrace.cons hhead hlink (ih htail)

/-- Passage list for traversing a stored path in the opposite direction. -/
def reversePassages : List Passage → List Passage
  | [] => []
  | passage :: rest =>
      reversePassages rest ++ [(passage.2, passage.1)]

theorem reversePassages_length (passages : List Passage) :
    (reversePassages passages).length = passages.length := by
  induction passages with
  | nil => rfl
  | cons passage rest ih =>
      simp [reversePassages, ih]

theorem reversePassages_append (left right : List Passage) :
    reversePassages (left ++ right) =
      reversePassages right ++ reversePassages left := by
  induction left with
  | nil => simp [reversePassages]
  | cons passage left ih =>
      simp [reversePassages, ih, List.append_assoc]

theorem reversePassage_mem {passage : Passage}
    {passages : List Passage} (hmem : passage ∈ passages) :
    (passage.2, passage.1) ∈ reversePassages passages := by
  induction passages with
  | nil => cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp [reversePassages]
      · exact List.mem_append_left _ (ih htail)

theorem reversePassages_grooved {state : Tongues}
    {passages : List Passage}
    (hgrooved : PassagesGrooved state passages) :
    PassagesGrooved state (reversePassages passages) := by
  induction passages with
  | nil =>
      intro passage hp
      cases hp
  | cons head rest ih =>
      intro passage hp
      simp only [reversePassages] at hp
      rcases List.mem_append.mp hp with htail | hhead
      · apply ih
        · intro old hold
          exact hgrooved old (List.mem_cons_of_mem _ hold)
        · exact htail
      · simp only [List.mem_singleton] at hhead
        subst passage
        exact groove_forward (hgrooved head List.mem_cons_self)

private theorem nodup_prefix_head_reverse_tail
    {pre tail : List Nat} {head : Nat}
    (hnd : (pre ++ head :: tail).Nodup) :
    (pre ++ head :: tail.reverse).Nodup := by grind

theorem PhysicalTrace.passage_exit_switch
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    ∀ passage ∈ passages,
      passage.2 / 3 = passageSwitch passage := by
  induction htrace with
  | nil =>
      intro passage hp
      cases hp
  | @cons p x q u v passages finish harrive hlink tail ih =>
      intro passage hp
      rcases List.mem_cons.mp hp with hhead | htail
      · subst passage
        have hs := arrive_exit_switch u p
        rw [harrive] at hs
        exact hs
      · exact ih passage htail

theorem map_passageSwitch_reversePassages
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    (reversePassages passages).map passageSwitch =
      (passages.map passageSwitch).reverse := by
  induction htrace with
  | nil => rfl
  | @cons p x q u v passages finish harrive hlink tail ih =>
      have hs := arrive_exit_switch u p
      rw [harrive] at hs
      simp [reversePassages, List.map_append, ih,
        passageSwitch, hs]

/-- A fresh local passage that exits through the entry of a recorded prefix
immediately traverses that prefix backwards and leaves over its incoming
boundary edge. -/
theorem physicalTrace_contact_retraces_prefix
    {w : Wiring} {g e p oldEntry : Nat}
    {base mouthState u v : Tongues}
    {recorded : List Passage}
    (hrecorded :
      PhysicalTrace w (g, base) recorded (oldEntry, mouthState))
    (hgrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v)) :
    PhysicalTrace w (p, u)
      ((p, oldEntry) :: reversePassages recorded) (e, v) := by
  induction recorded generalizing g base e with
  | nil =>
      cases hrecorded
      exact PhysicalTrace.cons hcontact (w.symm _ _ hentry) (PhysicalTrace.nil _)
  | cons passage rest ih =>
      cases hrecorded with
      | @cons _ x next _ middle _ _ _ hlink tail =>
          have hrest := ih tail
            (fun passage hp => hgrooved passage (List.mem_cons_of_mem _ hp)) hlink
          have hhead : PhysicalTrace w (x, v) [(x, g)] (e, v) :=
            PhysicalTrace.cons (hgrooved (g, x) List.mem_cons_self)
              (w.symm _ _ hentry) (PhysicalTrace.nil _)
          simpa [reversePassages] using hrest.append hhead


theorem linked_prefix_of_append {w : Wiring}
    {left right : List Passage}
    (hlinked : LinkedPassages w (left ++ right)) :
    LinkedPassages w left := by
  induction left with
  | nil => trivial
  | cons a tail ih =>
      cases tail with
      | nil => trivial
      | cons b rest =>
          change w.link a.2 = some b.1 ∧
            LinkedPassages w (b :: rest) at ⊢
          change w.link a.2 = some b.1 ∧
            LinkedPassages w ((b :: rest) ++ right) at hlinked
          exact ⟨hlinked.1, ih hlinked.2⟩

theorem linked_boundary_of_append {w : Wiring}
    {g a p x : Nat} {before after : List Passage}
    (hlinked : LinkedPassages w
      (((g, a) :: before) ++ (p, x) :: after)) :
    w.link (lastPassageExit a before) = some p := by
  induction before generalizing g a with
  | nil =>
      exact hlinked.1
  | cons passage before ih =>
      rcases passage with ⟨r, y⟩
      have htail : LinkedPassages w
          (((r, y) :: before) ++ (p, x) :: after) := hlinked.2
      simpa [lastPassageExit] using ih htail

/-- A nonempty prefix before an occurrence in a simple grooved path reaches
that occurrence without changing tongues, and does not visit its switch. -/
theorem simple_grooved_prefix_to_occurrence
    {w : Wiring} {u : Tongues}
    {g a p x : Nat} {before after : List Passage}
    (hlinked : LinkedPassages w
      (((g, a) :: before) ++ (p, x) :: after))
    (hgrooved : PassagesGrooved u
      (((g, a) :: before) ++ (p, x) :: after))
    (hsimple : SwitchSimple
      (((g, a) :: before) ++ (p, x) :: after)) :
    PhysicalTrace w (g, u) ((g, a) :: before) (p, u) ∧
      (∀ passage ∈ (g, a) :: before,
        passageSwitch passage ≠ passageSwitch (p, x)) := by
  have hprefixLinked : LinkedPassages w ((g, a) :: before) :=
    linked_prefix_of_append hlinked
  have hprefixGrooved : PassagesGrooved u ((g, a) :: before) := by
    intro passage hp
    exact hgrooved passage (List.mem_append_left _ hp)
  have hboundary : w.link (lastPassageExit a before) = some p :=
    linked_boundary_of_append hlinked
  have htrace := physicalTrace_grooved_passages w u g a p before
    hprefixLinked hprefixGrooved hboundary
  have hforeign : ∀ passage ∈ (g, a) :: before,
      passageSwitch passage ≠ passageSwitch (p, x) := by
    unfold SwitchSimple at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (p, x)) (by simp)
    exact hne hEq
  exact ⟨htrace, hforeign⟩

/-- Empty-prefix wrapper around `simple_grooved_prefix_to_occurrence`.  A
static trace supplies the path's starting port; the returned trace is rebased
to any tongue vector under which the path is grooved. -/
theorem simple_grooved_trace_prefix_to_occurrence
    {w : Wiring} {e : Nat} {base u : Tongues}
    {path before after : List Passage} {p x : Nat}
    {finish : Nat × Tongues}
    (hstatic : PhysicalTrace w (e, base) path finish)
    (hoccurs : path = before ++ (p, x) :: after)
    (hgrooved : PassagesGrooved u path)
    (hsimple : SwitchSimple path) :
    PhysicalTrace w (e, u) before (p, u) ∧
      (∀ passage ∈ before,
        passageSwitch passage ≠ passageSwitch (p, x)) := by
  have hlinked : LinkedPassages w
      (before ++ (p, x) :: after) := by
    rw [← hoccurs]
    exact hstatic.linked
  have hgrooved' : PassagesGrooved u
      (before ++ (p, x) :: after) := by
    rwa [← hoccurs]
  have hsimple' : SwitchSimple
      (before ++ (p, x) :: after) := by
    rwa [← hoccurs]
  cases before with
  | nil =>
      have htrace := hstatic
      rw [hoccurs] at htrace
      have hstart : e = p := htrace.head_arrive.1
      constructor
      · simpa [hstart] using (PhysicalTrace.nil (e, u))
      · intro passage hp
        cases hp
  | cons passage before =>
      rcases passage with ⟨g, a⟩
      have hdata := simple_grooved_prefix_to_occurrence
        hlinked hgrooved' hsimple'
      have htrace := hstatic
      rw [hoccurs] at htrace
      have hstart : e = g := htrace.head_arrive.1
      constructor
      · simpa [hstart] using hdata.1
      · exact hdata.2

/-! ## One deliberately broken groove -/

/-- If a grooved passage is entered trailing-first after its switch has been
flipped, the trailing move repairs the tongue and follows the old passage.
This is the self-healing half of the theta case. -/
theorem flipped_passage_forward_trailing
    {u : Tongues} {p x : Nat}
    (hforward : arrive u p = (x, u))
    (hpbranch : p % 3 ≠ 0) :
    arrive (flipAt u (p / 3)) p = (x, u) := by
  unfold arrive at hforward
  rw [if_neg hpbranch] at hforward
  injection hforward with hx hpin
  have hu : u (p / 3) = bval p := by
    simpa [pin] using (congrFun hpin (p / 3)).symm
  have hrestore : pin (flipAt u (p / 3)) p = u := by
    funext j
    unfold pin flipAt
    by_cases hj : j = p / 3
    · subst j
      simp [hu]
    · simp [hj]
  simp [arrive, hpbranch, hrestore, hx]

/-- After the crossed passage at a first revisit, every groove away from the
revisited switch survives.  In particular, the simple runway and the candy
interior are simultaneously grooved in the state in which the train starts
its forced retrace.  This is the activation invariant needed to manufacture
the next reflector from the far side. -/
theorem crossed_revisit_support_grooved
    {w : Wiring} {start : Nat × Tongues}
    {runway path : List Passage}
    {p x q y : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hsw : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v)) :
    PathGrooves [runway, path] v := by
  have hfull := hrunway.append hexcursion
  have hgrooved := hfull.grooved_of_switchSimple hsimple
  have hexit := hfull.passage_exit_switch
  have hparts :
      (runway.map passageSwitch).Nodup ∧
      (((p, x) :: path).map passageSwitch).Nodup ∧
      ∀ a ∈ runway.map passageSwitch,
        ∀ b ∈ ((p, x) :: path).map passageSwitch, a ≠ b := by
    unfold SwitchSimple at hsimple
    simp only [List.map_append] at hsimple
    exact List.nodup_append.mp hsimple
  apply pathGrooves_pair.mpr
  constructor
  · intro passage hp
    have hold := hgrooved passage (List.mem_append_left _ hp)
    have hforeign : passage.2 / 3 ≠ q / 3 := by
      rw [hexit passage (List.mem_append_left _ hp), ← hsw]
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (passageSwitch (p, x)) (by simp)
      simpa [passageSwitch] using hne
    exact groove_transfer hold
      (arrive_preserves_other hrepeat hforeign)
  · intro passage hp
    have hmem : passage ∈ runway ++ (p, x) :: path :=
      List.mem_append_right runway (List.mem_cons_of_mem _ hp)
    have hold := hgrooved passage hmem
    have htailNodup := hparts.2.1
    simp only [List.map_cons, List.nodup_cons] at htailNodup
    have hforeign : passage.2 / 3 ≠ q / 3 := by
      rw [hexit passage hmem, ← hsw]
      have hne : passageSwitch (p, x) ≠ passageSwitch passage := by
        intro hEq
        apply htailNodup.1
        rw [hEq]
        exact List.mem_map.mpr ⟨passage, hp, rfl⟩
      simpa [passageSwitch] using Ne.symm hne
    exact groove_transfer hold
      (arrive_preserves_other hrepeat hforeign)

/-! ## Retaining the construction data -/

/-- The nondegenerate reflector produced by a crossed first revisit, with
the runway and candy traces retained.  `SupportedReflector` is ideal for
composition, but deliberately forgets exactly this data; theta capture needs
it once, at the intersected mouth. -/
structure ManufacturedFlipReflector (w : Wiring) (g e : Nat) where
  base : Tongues
  mouthState : Tongues
  returnState : Tongues
  afterReturn : Tongues
  runway : List Passage
  candy : List Passage
  mouth : Nat
  firstArm : Nat
  secondArm : Nat
  runwayTrace :
    PhysicalTrace w (g, base) runway (mouth, mouthState)
  candyTrace :
    PhysicalTrace w (mouth, mouthState)
      ((mouth, firstArm) :: candy) (secondArm, returnState)
  simple : SwitchSimple (runway ++ (mouth, firstArm) :: candy)
  crossed : arrive returnState secondArm = (mouth, afterReturn)
  arms_ne : firstArm ≠ secondArm
  entryEdge : w.link e = some g

def ManufacturedFlipReflector.actionSwitch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) : Nat :=
  A.mouth / 3

def ManufacturedFlipReflector.toSupported
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    SupportedReflector w g e where
  travel := 2 * A.runway.length + A.candy.length + 2
  paths := [A.runway, A.candy]
  action := .flip A.actionSwitch
  run := by
    have href := crossed_revisit_full_reflector w A.runwayTrace
      A.candyTrace A.simple A.crossed A.arms_ne A.entryEdge
    intro state hs
    obtain ⟨hstep, hnext⟩ := href state (pathGrooves_pair.mp hs)
    exact ⟨hstep, pathGrooves_pair.mpr hnext⟩

section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedFlipReflector w g e)
include w g e A

/-- The mouth of every nondegenerate manufactured reflector is the stem of
its switch. -/
theorem ManufacturedFlipReflector.mouth_is_stem :
    A.mouth % 3 = 0 := by
  obtain ⟨oldAfter, hold⟩ := A.candyTrace.head_arrive.2
  have holdStem := arrive_stem_endpoint A.mouthState A.mouth
  rw [hold] at holdStem
  have hnewStem := arrive_stem_endpoint A.returnState A.secondArm
  rw [A.crossed] at hnewStem
  have hsecondSwitch :=
    arrive_exit_switch A.returnState A.secondArm
  rw [A.crossed] at hsecondSwitch
  by_cases hp : A.mouth % 3 = 0
  · exact hp
  · exfalso
    have hpne : A.mouth ≠ 3 * (A.mouth / 3) := by omega
    rcases holdStem with hpOld | hxStem
    · exact hpne hpOld
    · rcases hnewStem with hqStem | hpNew
      · apply A.arms_ne
        omega
      · apply hpne
        omega

theorem ManufacturedFlipReflector.firstArm_switch :
    A.firstArm / 3 = A.actionSwitch := by
  obtain ⟨after, hhead⟩ := A.candyTrace.head_arrive.2
  have hs := arrive_exit_switch A.mouthState A.mouth
  rw [hhead] at hs
  simpa [ManufacturedFlipReflector.actionSwitch] using hs

theorem ManufacturedFlipReflector.secondArm_switch :
    A.secondArm / 3 = A.actionSwitch := by
  have hs := arrive_exit_switch A.returnState A.secondArm
  rw [A.crossed] at hs
  simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm

theorem ManufacturedFlipReflector.firstArm_branch :
    A.firstArm % 3 ≠ 0 := by
  intro hstem
  have hne := arrive_exit_ne A.mouthState A.mouth
  obtain ⟨after, hhead⟩ := A.candyTrace.head_arrive.2
  rw [hhead] at hne
  have hm := A.mouth_is_stem
  have hs := A.firstArm_switch
  unfold ManufacturedFlipReflector.actionSwitch at hs
  apply hne
  omega

theorem ManufacturedFlipReflector.secondArm_branch :
    A.secondArm % 3 ≠ 0 := by
  intro hstem
  have hne := arrive_exit_ne A.returnState A.secondArm
  rw [A.crossed] at hne
  have hm := A.mouth_is_stem
  have hs := A.secondArm_switch
  unfold ManufacturedFlipReflector.actionSwitch at hs
  apply hne
  omega

theorem ManufacturedFlipReflector.selected_arm
    (state : Tongues) :
    state A.actionSwitch = bval A.firstArm ∨
      state A.actionSwitch = bval A.secondArm := by
  have hopp := branch_values_opposite A.firstArm_branch A.secondArm_branch
    (A.firstArm_switch.trans A.secondArm_switch.symm) A.arms_ne
  cases hs : state A.actionSwitch <;>
    cases hf : bval A.firstArm <;>
    cases hq : bval A.secondArm <;>
    simp_all

/-- Rebase the manufactured runway to any state satisfying its grooves. -/
theorem ManufacturedFlipReflector.runway_trace
    (state : Tongues)
    (hgrooved : PassagesGrooved state A.runway) :
    PhysicalTrace w (g, state) A.runway (A.mouth, state) := by
  exact A.runwayTrace.replay_grooved state hgrooved

/-- Candy traversal in its recorded direction, before the mouth switch is
pinned on the return arm. -/
theorem ManufacturedFlipReflector.candy_forward_trace
    (state : Tongues)
    (hselected : state A.actionSwitch = bval A.firstArm)
    (hgrooved : PassagesGrooved state A.candy) :
    PhysicalTrace w (A.mouth, state)
      ((A.mouth, A.firstArm) :: A.candy)
      (A.secondArm, state) := by
  have hfirstSwitch := A.firstArm_switch
  have hfirstBranch := A.firstArm_branch
  have hstem : 3 * (A.firstArm / 3) = A.mouth := by
    have hm := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at hfirstSwitch
    omega
  have hagree : state (A.firstArm / 3) = bval A.firstArm := by
    rw [hfirstSwitch]
    exact hselected
  have hpin : pin state A.firstArm = state := pin_of_agrees hagree
  have hheadGroove :
      arrive state A.firstArm = (A.mouth, state) := by
    simp [arrive, hfirstBranch, hstem, hpin]
  have hallGrooved :
      PassagesGrooved state ((A.mouth, A.firstArm) :: A.candy) := by
    intro passage hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadGroove
    · exact hgrooved passage htail
  exact physicalTrace_grooved_passages w state A.mouth A.firstArm
    A.secondArm A.candy A.candyTrace.linked hallGrooved
    A.candyTrace.last_link

/-- Candy traversal in the opposite direction, with the reverse passage
list retained explicitly. -/
theorem ManufacturedFlipReflector.candy_reverse_trace
    (state : Tongues)
    (hselected : state A.actionSwitch = bval A.secondArm)
    (hgrooved : PassagesGrooved state A.candy) :
    PhysicalTrace w (A.mouth, state)
      ((A.mouth, A.secondArm) :: reversePassages A.candy)
      (A.firstArm, state) := by
  have hsecondSwitch := A.secondArm_switch
  have hsecondBranch := A.secondArm_branch
  have hstem : 3 * (A.secondArm / 3) = A.mouth := by
    have hm := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at hsecondSwitch
    omega
  have hagree : state (A.secondArm / 3) = bval A.secondArm := by
    rw [hsecondSwitch]
    exact hselected
  have hpin : pin state A.secondArm = state := pin_of_agrees hagree
  have hsecondGroove :
      arrive state A.secondArm = (A.mouth, state) := by
    simp [arrive, hsecondBranch, hstem, hpin]
  have hmouthForward := groove_forward hsecondGroove
  cases A.candyTrace with
  | cons _ hentry tail =>
      exact physicalTrace_contact_retraces_prefix tail hgrooved hentry hmouthForward


theorem ManufacturedFlipReflector.reverse_support_simple :
    SwitchSimple
      (A.runway ++
        (A.mouth, A.secondArm) :: reversePassages A.candy) := by
  have hmap :
      (reversePassages A.candy).map passageSwitch =
        (A.candy.map passageSwitch).reverse := by
    have htrace := A.candyTrace
    cases htrace with
    | cons harrive hlink tail =>
        exact map_passageSwitch_reversePassages tail
  have hs := A.simple
  unfold SwitchSimple at hs ⊢
  simp only [List.map_append, List.map_cons] at hs ⊢
  rw [hmap]
  exact nodup_prefix_head_reverse_tail hs

/-- No-change prefix reaching the same candy occurrence when the candy is
traversed in the opposite direction. -/
theorem ManufacturedFlipReflector.reverse_prefix_to_candy_occurrence
    (state : Tongues)
    (hpaths : PathGrooves [A.runway, A.candy] state)
    (hselected : state A.actionSwitch = bval A.secondArm)
    {before after : List Passage} {p x : Nat}
    (hoccurs : A.candy = before ++ (p, x) :: after) :
    PhysicalTrace w (g, state)
      (A.runway ++
        (A.mouth, A.secondArm) :: reversePassages after)
      (x, state) ∧
      (∀ passage ∈
          A.runway ++
            (A.mouth, A.secondArm) :: reversePassages after,
        passageSwitch passage ≠ passageSwitch (x, p)) := by
  have hp := pathGrooves_pair.mp hpaths
  have hrun := A.runway_trace state hp.1
  have hcandy := A.candy_reverse_trace state hselected hp.2
  have hfull := hrun.append hcandy
  have hsimple := A.reverse_support_simple
  have hgrooved := hfull.grooved_of_switchSimple hsimple
  have hreverse : reversePassages A.candy =
      reversePassages after ++ (x, p) :: reversePassages before := by
    rw [hoccurs, reversePassages_append]
    simp [reversePassages, List.append_assoc]
  have hsplit :
      A.runway ++
          (A.mouth, A.secondArm) :: reversePassages A.candy =
        (A.runway ++
          (A.mouth, A.secondArm) :: reversePassages after) ++
            (x, p) :: reversePassages before := by
    rw [hreverse]
    simp [List.append_assoc]
  exact simple_grooved_trace_prefix_to_occurrence
    hfull hsplit hgrooved hsimple

/-- The lobe mouth is absent from both support paths; its flip is therefore
the unique possible support fault seen by another reflector. -/
theorem ManufacturedFlipReflector.support_foreign :
    ∀ path ∈ [A.runway, A.candy], ∀ passage ∈ path,
      passageSwitch passage ≠ A.actionSwitch := by
  intro path hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · intro passage hpassage hEq
    have hsimple := A.simple
    unfold SwitchSimple at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    have hcross := hparts.2.2
    have hne := hcross (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hpassage, rfl⟩)
      A.actionSwitch (by simp [ManufacturedFlipReflector.actionSwitch,
        passageSwitch])
    exact hne hEq
  · intro passage hpassage hEq
    have hsimpleCandy :
        SwitchSimple ((A.mouth, A.firstArm) :: A.candy) := by
      have hsimple := A.simple
      unfold SwitchSimple at hsimple ⊢
      simp only [List.map_append] at hsimple
      exact (List.nodup_append.mp hsimple).2.1
    unfold SwitchSimple at hsimpleCandy
    simp only [List.map_cons, List.nodup_cons] at hsimpleCandy
    apply hsimpleCandy.1
    apply List.mem_map.mpr
    exact ⟨passage, hpassage, hEq⟩

/-- Core capture, packaged on the retained manufactured-reflector data. -/
theorem ManufacturedFlipReflector.capture_from_mouth
    (state : Tongues)
    (hrunway : PassagesGrooved state A.runway)
    (hcandy : PassagesGrooved state A.candy) :
    stepN w (A.candy.length + 2 + A.runway.length)
      (A.mouth, flipAt state A.actionSwitch) = some (e, state) := by
  have hrunwayFlip := grooved_after_flip_other hrunway
    (A.support_foreign A.runway (by simp))
  have hcandyFlip := grooved_after_flip_other hcandy
    (A.support_foreign A.candy (by simp))
  have hwhole := (A.toSupported.run (flipAt state A.actionSwitch)
    (pathGrooves_pair.mpr ⟨hrunwayFlip, hcandyFlip⟩)).1
  change stepN w (2 * A.runway.length + A.candy.length + 2)
    (g, flipAt state A.actionSwitch) =
      some (e, flipAt (flipAt state A.actionSwitch) A.actionSwitch) at hwhole
  rw [flipAt_flipAt] at hwhole
  have hlen : 2 * A.runway.length + A.candy.length + 2 =
      A.runway.length + (A.candy.length + 2 + A.runway.length) := by omega
  rw [hlen, stepN_add, (A.runway_trace _ hrunwayFlip).sound] at hwhole
  exact hwhole

end

/-- Degenerate first-revisit reflector: a grooved arm is linked to itself.
The train traverses the arm out and back, then retraces the runway; its local
action is the identity. -/
structure ManufacturedStayReflector (w : Wiring) (g e : Nat) where
  base : Tongues
  mouthState : Tongues
  returnState : Tongues
  runway : List Passage
  mouth : Nat
  arm : Nat
  runwayTrace :
    PhysicalTrace w (g, base) runway (mouth, mouthState)
  coreTrace :
    PhysicalTrace w (mouth, mouthState) [(mouth, arm)]
      (arm, returnState)
  simple : SwitchSimple (runway ++ [(mouth, arm)])
  stemEndpoint :
    mouth = 3 * (mouth / 3) ∨ arm = 3 * (mouth / 3)
  selfLink : w.link arm = some arm
  entryEdge : w.link e = some g

def ManufacturedStayReflector.toSupported
    {w : Wiring} {g e : Nat}
    (A : ManufacturedStayReflector w g e) :
    SupportedReflector w g e where
  travel := 2 * A.runway.length + 2
  paths := [A.runway, [(A.mouth, A.arm)]]
  action := .stay
  run := by
    have hcoreAt (outside : Nat)
        (hmouth : w.link A.mouth = some outside) :=
      self_edge_groove_isReflector w A.selfLink hmouth
    cases hrunway : A.runway with
    | nil =>
        have htrace := A.runwayTrace
        rw [hrunway] at htrace
        have hs : (g, A.base) = (A.mouth, A.mouthState) := by
          simpa [stepN] using htrace.sound
        have hgm : g = A.mouth := congrArg Prod.fst hs
        have hmouth : w.link A.mouth = some e := by
          apply w.symm
          simpa [hgm] using A.entryEdge
        have hcore := hcoreAt e hmouth
        intro state hpaths
        have hp := pathGrooves_pair.mp hpaths
        obtain ⟨hstep, hnext⟩ := hcore state
          (passagesGrooved_singleton.mp hp.2)
        constructor
        · simpa [hrunway, hgm, LocalAction.apply] using hstep
        · exact pathGrooves_pair.mpr
            ⟨(by intro passage hmem; cases hmem),
              passagesGrooved_singleton.mpr hnext⟩
    | cons passage rest =>
        rcases passage with ⟨p, x⟩
        have htrace := A.runwayTrace
        rw [hrunway] at htrace
        have hstart : g = p := htrace.head_arrive.1
        have hlast :
            w.link (lastPassageExit x rest) = some A.mouth :=
          htrace.last_link
        have hmouth :
            w.link A.mouth = some (lastPassageExit x rest) :=
          w.symm _ _ hlast
        have hcore := hcoreAt (lastPassageExit x rest) hmouth
        have hsandwich := sandwich_nonempty_reflector w htrace.linked
          hlast (by simpa [hstart] using A.entryEdge) hcore
          (fun _ hg => hg)
        have hlen :
            (((p, x) :: rest).length + 2 +
                ((p, x) :: rest).length) =
              2 * ((p, x) :: rest).length + 2 := by omega
        rw [hlen] at hsandwich
        intro state hpaths
        have hp := pathGrooves_pair.mp hpaths
        obtain ⟨hstep, hnext⟩ := hsandwich state
          ⟨hp.1, passagesGrooved_singleton.mp hp.2⟩
        constructor
        · simpa [hrunway, hstart, LocalAction.apply] using hstep
        · exact pathGrooves_pair.mpr
            ⟨hnext.1, passagesGrooved_singleton.mpr hnext.2⟩

theorem ManufacturedStayReflector.runway_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedStayReflector w g e)
    (state : Tongues)
    (hgrooved : PassagesGrooved state A.runway) :
    PhysicalTrace w (g, state) A.runway (A.mouth, state) := by
  exact A.runwayTrace.replay_grooved state hgrooved

inductive ManufacturedReflector (w : Wiring) (g e : Nat) where
  | stay (A : ManufacturedStayReflector w g e)
  | flip (A : ManufacturedFlipReflector w g e)

/-- The switch-simple outward exploration that manufactured a reflector.
It includes the lobe mouth passage, unlike `SupportedReflector.paths`,
because that mouth is exactly the additional switch the construction may
change. -/
def ManufacturedReflector.exploration
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : List Passage :=
  match A with
  | .stay R => R.runway ++ [(R.mouth, R.arm)]
  | .flip R => R.runway ++ (R.mouth, R.firstArm) :: R.candy

def ManufacturedReflector.baseState
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Tongues :=
  match A with
  | .stay R => R.base
  | .flip R => R.base

def ManufacturedReflector.preReturn
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Nat × Tongues :=
  match A with
  | .stay R => (R.arm, R.returnState)
  | .flip R => (R.secondArm, R.returnState)

def ManufacturedReflector.activatedState
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Tongues :=
  match A with
  | .stay R => R.returnState
  | .flip R => R.afterReturn

def ManufacturedReflector.runway
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : List Passage :=
  match A with
  | .stay R => R.runway
  | .flip R => R.runway

def ManufacturedReflector.mouthConfig
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Nat × Tongues :=
  match A with
  | .stay R => (R.mouth, R.mouthState)
  | .flip R => (R.mouth, R.mouthState)

section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedReflector w g e)
include w g e A

theorem ManufacturedReflector.runway_trace :
    PhysicalTrace w (g, A.baseState) A.runway A.mouthConfig := by
  cases A with
  | stay R => exact R.runwayTrace
  | flip R => exact R.runwayTrace

theorem ManufacturedReflector.exploration_trace :
    PhysicalTrace w (g, A.baseState) A.exploration A.preReturn := by
  cases A with
  | stay R => exact R.runwayTrace.append R.coreTrace
  | flip R => exact R.runwayTrace.append R.candyTrace

/-- The local return passage of either manufactured-reflector constructor
contacts the retained runway at its mouth and produces the advertised
activated state. -/
theorem ManufacturedReflector.return_arrive_mouth :
    arrive A.preReturn.2 A.preReturn.1 =
      (A.mouthConfig.1, A.activatedState) := by
  cases A with
  | flip R =>
      exact R.crossed
  | stay R =>
      obtain ⟨after, hhead⟩ := R.coreTrace.head_arrive.2
      have hsound := R.coreTrace.sound
      have hafter : after = R.returnState := by
        simp [stepN, step, hhead, R.selfLink] at hsound
        exact hsound
      have hback := arrive_back R.mouthState R.mouth
      rw [hhead, hafter] at hback
      exact hback

/-- The local passage immediately following a manufactured exploration is
the repeated-switch passage that activates the reflector. -/
theorem ManufacturedReflector.return_arrive :
    ∃ exit, arrive A.preReturn.2 A.preReturn.1 =
      (exit, A.activatedState) :=
  ⟨A.mouthConfig.1, A.return_arrive_mouth⟩

theorem ManufacturedReflector.exploration_simple :
    SwitchSimple A.exploration := by
  cases A with
  | stay R => exact R.simple
  | flip R => exact R.simple

end

def ManufacturedReflector.toSupported
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : SupportedReflector w g e :=
  match A with
  | .stay R => R.toSupported
  | .flip R => R.toSupported

theorem ManufacturedReflector.runway_mem_support
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.runway ∈ A.toSupported.paths := by
  cases A <;> simp [ManufacturedReflector.runway,
    ManufacturedReflector.toSupported,
    ManufacturedStayReflector.toSupported,
    ManufacturedFlipReflector.toSupported]

/-- The actual switch-simple outward route selected by `state`.  A flip
reflector may traverse its candy in either orientation; normalizing that
choice here lets every later contact be classified relative to the route the
train really takes. -/
def ManufacturedReflector.orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues) :
    List Passage :=
  match A with
  | .stay R => R.runway ++ [(R.mouth, R.arm)]
  | .flip R =>
      if state R.actionSwitch = bval R.firstArm then
        R.runway ++ (R.mouth, R.firstArm) :: R.candy
      else
        R.runway ++
          (R.mouth, R.secondArm) :: reversePassages R.candy

def ManufacturedReflector.orientedFinish
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues) : Nat :=
  match A with
  | .stay R => R.arm
  | .flip R =>
      if state R.actionSwitch = bval R.firstArm then
        R.secondArm
      else
        R.firstArm

/-- The selected far candy arm is the opposite branch, so its trailing
arrival applies the reflector action. This local fact also supplies the
head of the full return trace. -/
theorem ManufacturedFlipReflector.oriented_finish_arrive
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues) :
    arrive state
      ((ManufacturedReflector.flip R).orientedFinish state) =
        (R.mouth, flipAt state R.actionSwitch) := by
  by_cases hselected :
      state R.actionSwitch = bval R.firstArm
  · have hopp : bval R.secondArm = !(state R.actionSwitch) := by
      rw [hselected]
      exact branch_values_opposite R.firstArm_branch
        R.secondArm_branch
        (R.firstArm_switch.trans R.secondArm_switch.symm)
        R.arms_ne
    have hpin : pin state R.secondArm =
        flipAt state R.actionSwitch :=
      pin_eq_flipAt R.secondArm_switch hopp
    have hstem : 3 * (R.secondArm / 3) = R.mouth := by
      have hm := R.mouth_is_stem
      have hs := R.secondArm_switch
      unfold ManufacturedFlipReflector.actionSwitch at hs
      omega
    simp [ManufacturedReflector.orientedFinish, hselected,
      arrive, R.secondArm_branch, hstem, hpin]
  · have hsecond :
        state R.actionSwitch = bval R.secondArm := by
      rcases R.selected_arm state with hfirst | hsecond
      · exact absurd hfirst hselected
      · exact hsecond
    have hopp : bval R.firstArm = !(state R.actionSwitch) := by
      rw [hsecond]
      exact branch_values_opposite R.secondArm_branch
        R.firstArm_branch
        (R.secondArm_switch.trans R.firstArm_switch.symm)
        (Ne.symm R.arms_ne)
    have hpin : pin state R.firstArm =
        flipAt state R.actionSwitch :=
      pin_eq_flipAt R.firstArm_switch hopp
    have hstem : 3 * (R.firstArm / 3) = R.mouth := by
      have hm := R.mouth_is_stem
      have hs := R.firstArm_switch
      unfold ManufacturedFlipReflector.actionSwitch at hs
      omega
    simp [ManufacturedReflector.orientedFinish, hselected,
      arrive, R.firstArm_branch, hstem, hpin]


theorem ManufacturedReflector.orientedRoute_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state) :
    PhysicalTrace w (g, state) (A.orientedRoute state)
      (A.orientedFinish state, state) := by
  cases A with
  | stay R =>
      change PathGrooves
        [R.runway, [(R.mouth, R.arm)]] state at hpaths
      have hp := pathGrooves_pair.mp hpaths
      have hrun := R.runway_trace state hp.1
      have hcoreBack := passagesGrooved_singleton.mp hp.2
      have hcoreForward := groove_forward hcoreBack
      have hcore : PhysicalTrace w (R.mouth, state)
          [(R.mouth, R.arm)] (R.arm, state) :=
        PhysicalTrace.cons hcoreForward R.selfLink
          (PhysicalTrace.nil _)
      simpa [ManufacturedReflector.orientedRoute,
        ManufacturedReflector.orientedFinish] using hrun.append hcore
  | flip R =>
      change PathGrooves [R.runway, R.candy] state at hpaths
      have hp := pathGrooves_pair.mp hpaths
      have hrun := R.runway_trace state hp.1
      by_cases hselected :
          state R.actionSwitch = bval R.firstArm
      · have hcandy := R.candy_forward_trace state hselected hp.2
        simpa [ManufacturedReflector.orientedRoute,
          ManufacturedReflector.orientedFinish, hselected] using
          hrun.append hcandy
      · have hsecond :
            state R.actionSwitch = bval R.secondArm := by
          rcases R.selected_arm state with hfirst | hsecond
          · exact absurd hfirst hselected
          · exact hsecond
        have hcandy := R.candy_reverse_trace state hsecond hp.2
        simpa [ManufacturedReflector.orientedRoute,
          ManufacturedReflector.orientedFinish, hselected] using
          hrun.append hcandy

theorem ManufacturedReflector.orientedRoute_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues) :
    SwitchSimple (A.orientedRoute state) := by
  cases A with
  | stay R =>
      simpa [ManufacturedReflector.orientedRoute] using R.simple
  | flip R =>
      by_cases hselected :
          state R.actionSwitch = bval R.firstArm
      · simpa [ManufacturedReflector.orientedRoute, hselected] using
          R.simple
      · simpa [ManufacturedReflector.orientedRoute, hselected] using
          R.reverse_support_simple

/-- Every reusable support passage occurs on the selected outward route,
possibly in the opposite orientation when the candy is traversed backwards.
-/
theorem ManufacturedReflector.support_passage_on_orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    {path : List Passage} (hpath : path ∈ A.toSupported.paths)
    {old : Passage} (hold : old ∈ path) :
    ∃ oriented ∈ A.orientedRoute state,
      oriented = old ∨ oriented = (old.2, old.1) := by
  cases A with
  | stay R =>
      change path ∈ [R.runway, [(R.mouth, R.arm)]] at hpath
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
      rcases hpath with rfl | rfl
      · exact ⟨old,
          (by
            simp only [ManufacturedReflector.orientedRoute]
            exact List.mem_append_left _ hold), Or.inl rfl⟩
      · simp only [List.mem_singleton] at hold
        subst old
        exact ⟨(R.mouth, R.arm), by
          simp [ManufacturedReflector.orientedRoute], Or.inl rfl⟩
  | flip R =>
      change path ∈ [R.runway, R.candy] at hpath
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
      rcases hpath with rfl | rfl
      · exact ⟨old,
          (by
            simp only [ManufacturedReflector.orientedRoute]
            split <;> exact List.mem_append_left _ hold), Or.inl rfl⟩
      · by_cases hselected :
            state R.actionSwitch = bval R.firstArm
        · exact ⟨old, by
            simp only [ManufacturedReflector.orientedRoute, hselected,
              if_pos]
            exact List.mem_append_right _
              (List.mem_cons_of_mem _ hold), Or.inl rfl⟩
        · exact ⟨(old.2, old.1), by
            simp only [ManufacturedReflector.orientedRoute, hselected]
            exact List.mem_append_right _
              (List.mem_cons_of_mem _ (reversePassage_mem hold)),
            Or.inr rfl⟩

/-- Orientation-normalized contact dichotomy.  At the instant a fresh
passage changes an old support switch, compare it with the passage on the
outward route the old reflector would actually take in that state.  The
fresh exit either points back into the already traversed prefix, or points
forward and is repaired by the old route's next trailing traversal. -/
theorem ManufacturedReflector.changed_contact_on_orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state next : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    {path : List Passage} (hpath : path ∈ A.toSupported.paths)
    {old : Passage} (hold : old ∈ path)
    {p x : Nat}
    (hswitch : passageSwitch old = p / 3)
    (hfresh : arrive state p = (x, next)) :
    ∃ oriented ∈ A.orientedRoute state,
      arrive state oriented.2 = (oriented.1, state) ∧
      passageSwitch oriented = p / 3 ∧
      (x = oriented.1 ∨
        (x = oriented.2 ∧
          ∃ repaired,
            arrive next oriented.1 = (oriented.2, repaired) ∧
            arrive repaired oriented.2 =
              (oriented.1, repaired))) := by
  obtain ⟨oriented, horiented, horient⟩ :=
    A.support_passage_on_orientedRoute state hpath hold
  have holdGroove := hpaths path hpath old hold
  have horientedGroove :
      arrive state oriented.2 = (oriented.1, state) := by
    rcases horient with hsame | hreverse
    · simpa [hsame] using holdGroove
    · simpa [hreverse] using groove_forward holdGroove
  have hOldSwitch : old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch state old.2
    rw [holdGroove] at hs
    exact hs.symm
  have horientedSwitch : passageSwitch oriented = p / 3 := by
    rcases horient with hsame | hreverse
    · simpa [hsame] using hswitch
    · simp only [hreverse, passageSwitch]
      rw [hOldSwitch]
      exact hswitch
  have hexit := grooved_contact_exit_dichotomy
    horientedGroove hfresh (by
      simpa [passageSwitch] using horientedSwitch)
  refine ⟨oriented, horiented, horientedGroove,
    horientedSwitch, ?_⟩
  rcases hexit with hback | hforward
  · exact Or.inl hback
  · right
    refine ⟨hforward, ?_⟩
    exact forward_contact_repairs_old_passage
      horientedGroove (by simpa [hforward] using hfresh)
      (by simpa [passageSwitch] using horientedSwitch)


theorem pathGrooves_after_arrive_without_support_change
    {u v : Tongues} {p x : Nat} {paths : List (List Passage)}
    (harrive : arrive u p = (x, v))
    (hgrooves : PathGrooves paths u)
    (hquiet : ∀ path ∈ paths, ∀ old ∈ path,
      passageSwitch old = p / 3 → v (p / 3) = u (p / 3)) :
    PathGrooves paths v := by
  intro path hp old hold
  have hgroove := hgrooves path hp old hold
  have hexit : old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch u old.2
    rw [hgroove] at hs
    exact hs.symm
  apply groove_transfer hgroove
  by_cases hsame : passageSwitch old = p / 3
  · rw [hexit, hsame]
    exact hquiet path hp old hold hsame
  · apply arrive_preserves_other harrive
    rw [hexit]
    exact hsame
theorem same_groove_same_tongue
    {u v : Tongues} {old : Passage}
    (hu : arrive u old.2 = (old.1, u))
    (hv : arrive v old.2 = (old.1, v)) :
    u (passageSwitch old) = v (passageSwitch old) := by
  rcases old with ⟨p, x⟩
  unfold passageSwitch
  change u (p / 3) = v (p / 3)
  have hswitchU := arrive_exit_switch u x
  rw [hu] at hswitchU
  simp only at hswitchU
  by_cases hx : x % 3 = 0
  · unfold arrive at hu hv
    rw [if_pos hx] at hu hv
    injection hu with hpu _
    injection hv with hpv _
    simp only at hpu hpv
    have hbp : branchPort (x / 3) (u (x / 3)) =
        branchPort (x / 3) (v (x / 3)) := hpu.trans hpv.symm
    have hval : u (x / 3) = v (x / 3) := by
      cases huval : u (x / 3) <;> cases hvval : v (x / 3) <;>
        simp [branchPort, huval, hvval] at hbp ⊢ <;> omega
    rw [hswitchU]
    exact hval
  · unfold arrive at hu hv
    rw [if_neg hx] at hu hv
    injection hu with _ hpinU
    injection hv with _ hpinV
    have hU := congrFun hpinU (x / 3)
    have hV := congrFun hpinV (x / 3)
    simp [pin] at hU hV
    rw [hswitchU]
    exact hU.symm.trans hV

theorem PhysicalTrace.changed_switch_has_changed_passage
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {j : Nat}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hchange : finish.2 j ≠ start.2 j) :
    ∃ before p x after u v,
      passages = before ++ (p, x) :: after ∧
      passageSwitch (p, x) = j ∧
      PhysicalTrace w start before (p, u) ∧
      arrive u p = (x, v) ∧
      u j = start.2 j ∧ finish.2 j = v j ∧ v j ≠ u j := by
  have hjmem : j ∈ passages.map passageSwitch := by
    apply Classical.byContradiction
    intro hnot
    apply hchange
    apply htrace.preserves
    intro passage hp hEq
    apply hnot
    exact List.mem_map.mpr ⟨passage, hp, hEq⟩
  obtain ⟨passage, hpassage, hswitch⟩ := List.mem_map.mp hjmem
  obtain ⟨before, after, hsplit⟩ := List.append_of_mem hpassage
  rcases passage with ⟨p, x⟩
  have htrace' := htrace
  have hsimple' := hsimple
  rw [hsplit] at htrace' hsimple'
  obtain ⟨middle, hbefore, hrest⟩ := htrace'.split_append
  cases hrest with
  | @cons _ _ q u v _ _ harrive hlink hafter =>
      have hprefixForeign :
          ∀ prior ∈ before, passageSwitch prior ≠ j := by
        unfold SwitchSimple at hsimple'
        simp only [List.map_append, List.map_cons] at hsimple'
        have hparts := List.nodup_append.mp hsimple'
        intro prior hprior hEq
        have hne := hparts.2.2 (passageSwitch prior)
          (List.mem_map.mpr ⟨prior, hprior, rfl⟩)
          (passageSwitch (p, x)) (by simp)
        apply hne
        rw [hEq, hswitch]
      have hsuffixForeign :
          ∀ later ∈ after, passageSwitch later ≠ j := by
        unfold SwitchSimple at hsimple'
        simp only [List.map_append, List.map_cons] at hsimple'
        have hparts := List.nodup_append.mp hsimple'
        have hheadTail := hparts.2.1
        rw [List.nodup_cons] at hheadTail
        intro later hlater hEq
        apply hheadTail.1
        apply List.mem_map.mpr
        exact ⟨later, hlater, by rw [hEq, hswitch]⟩
      have hu : u j = start.2 j :=
        hbefore.preserves j hprefixForeign
      have hv : finish.2 j = v j :=
        hafter.preserves j hsuffixForeign
      have hvu : v j ≠ u j := by
        intro hEq
        apply hchange
        rw [hv, hEq, hu]
      exact ⟨before, p, x, after, u, v, hsplit,
        hswitch, hbefore, harrive, hu, hv, hvu⟩

theorem PhysicalTrace.first_changed_support_passage
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {paths : List (List Passage)}
    (htrace : PhysicalTrace w start passages finish)
    (hbase : PathGrooves paths start.2)
    (hbroken : ¬ PathGrooves paths finish.2) :
    ∃ approach p x suffix u v path old,
      passages = approach ++ (p, x) :: suffix ∧
      PhysicalTrace w start approach (p, u) ∧
      PathGrooves paths u ∧
      arrive u p = (x, v) ∧
      path ∈ paths ∧ old ∈ path ∧
      passageSwitch old = p / 3 ∧
      v (p / 3) ≠ u (p / 3) := by
  induction htrace with
  | nil c =>
      exact absurd hbase hbroken
  | @cons p x q u v passages finish harrive hlink tail ih =>
      by_cases hhead : ∃ path ∈ paths, ∃ old ∈ path,
          passageSwitch old = p / 3 ∧ v (p / 3) ≠ u (p / 3)
      · obtain ⟨path, hp, old, hold, hswitch, hchanged⟩ := hhead
        exact ⟨[], p, x, passages, u, v, path, old,
          rfl, PhysicalTrace.nil _, hbase, harrive,
          hp, hold, hswitch, hchanged⟩
      · have hquiet : ∀ path ∈ paths, ∀ old ∈ path,
            passageSwitch old = p / 3 →
              v (p / 3) = u (p / 3) := by
          intro path hp old hold hswitch
          apply Classical.byContradiction
          intro hchanged
          apply hhead
          exact ⟨path, hp, old, hold, hswitch, hchanged⟩
        have hbaseTail : PathGrooves paths v :=
          pathGrooves_after_arrive_without_support_change
            harrive hbase hquiet
        obtain ⟨approach, p₂, x₂, suffix, u₂, v₂, path, old,
            hsplit, hprefix, hgrooves, hlocal,
            hp, hold, hswitch, hchanged⟩ :=
          ih hbaseTail hbroken
        refine ⟨(p, x) :: approach, p₂, x₂, suffix,
          u₂, v₂, path, old, ?_, ?_, hgrooves, hlocal,
          hp, hold, hswitch, hchanged⟩
        · simp [hsplit]
        · exact PhysicalTrace.cons harrive hlink hprefix


theorem ManufacturedReflector.entryEdge
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    w.link e = some g := by
  cases A with
  | stay R => exact R.entryEdge
  | flip R => exact R.entryEdge



theorem contact_of_not_avoids_flip
    {paths : List (List Passage)} {k : Nat}
    (hnot : ¬ (LocalAction.flip k).Avoids paths) :
    ∃ path ∈ paths, ∃ passage ∈ path,
      passageSwitch passage = k := by
  by_cases hcontact : ∃ path ∈ paths, ∃ passage ∈ path,
      passageSwitch passage = k
  · exact hcontact
  · exfalso
    apply hnot
    intro path hp passage hpass hEq
    apply hcontact
    exact ⟨path, hp, passage, hpass, hEq⟩

theorem ManufacturedReflector.travel_pos
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    0 < A.toSupported.travel := by
  cases A with
  | stay R =>
      change 0 < 2 * R.runway.length + 2
      omega
  | flip R =>
      change 0 < 2 * R.runway.length + R.candy.length + 2
      omega

end GeneralN
