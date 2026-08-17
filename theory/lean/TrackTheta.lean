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
    (hswitch : oldEntry / 3 = freshEntry / 3)
    (hchanged : v (freshEntry / 3) ≠ u (freshEntry / 3)) :
    ∃ repaired,
      arrive v oldEntry = (oldExit, repaired) ∧
      arrive repaired oldExit = (oldEntry, repaired) := by
  obtain ⟨hfreshBranch, hstem, _hv⟩ :=
    changed_arrival_is_trailing hfresh hchanged
  have holdSwitch : oldExit / 3 = oldEntry / 3 := by
    have hs := arrive_exit_switch u oldExit
    rw [hold] at hs
    exact hs.symm
  have hOldBranch : oldEntry % 3 ≠ 0 := by
    intro hOldStem
    have hsame : oldEntry = oldExit := by omega
    exact (arrive_exit_ne u oldExit) (by rw [hold]; exact hsame)
  have holdForward := groove_forward hold
  let repaired := (arrive v oldEntry).2
  have hrepair : arrive v oldEntry = (oldExit, repaired) := by
    apply Prod.ext
    · calc
        (arrive v oldEntry).1 = (arrive u oldEntry).1 :=
          trailing_arrive_exit_independent hOldBranch
        _ = oldExit := congrArg Prod.fst holdForward
    · rfl
  have hback := arrive_back v oldEntry
  rw [hrepair] at hback
  exact ⟨repaired, hrepair, hback⟩

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
  have holdSwitch : oldExit / 3 = oldEntry / 3 := by
    have hs := arrive_exit_switch state oldExit
    rw [hold] at hs
    exact hs.symm
  have hshare := same_switch_passages_share_port
    state state oldExit freshEntry (holdSwitch.trans hswitch)
  rw [hold, hfresh] at hshare
  rcases hshare with hsameEntry | hOldExit | hOldEntry | hsameExit
  · have hcmp := hold
    rw [hsameEntry, hfresh] at hcmp
    injection hcmp with hExit _
    exact Or.inl hExit
  · exact Or.inr hOldExit.symm
  · have hforward := groove_forward hold
    change oldEntry = freshEntry at hOldEntry
    rw [hOldEntry, hfresh] at hforward
    injection hforward with hExit _
    exact Or.inr hExit
  · exact Or.inl hsameExit.symm

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

theorem mem_reverse_nat {x : Nat} {xs : List Nat} :
    x ∈ xs.reverse ↔ x ∈ xs := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      simp [ih, or_comm]

theorem nodup_reverse_nat {xs : List Nat}
    (hnd : xs.Nodup) : xs.reverse.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.reverse_cons]
      apply List.nodup_append.mpr
      refine ⟨ih hnd.2, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      intro hax
      apply hnd.1
      rw [← hax]
      exact mem_reverse_nat.mp ha

private theorem nodup_prefix_head_reverse_tail
    {pre tail : List Nat} {head : Nat}
    (hnd : (pre ++ head :: tail).Nodup) :
    (pre ++ head :: tail.reverse).Nodup := by
  have hparts := List.nodup_append.mp hnd
  have hheadTail := hparts.2.1
  rw [List.nodup_cons] at hheadTail
  apply List.nodup_append.mpr
  refine ⟨hparts.1, ?_, ?_⟩
  · rw [List.nodup_cons]
    constructor
    · intro hmem
      apply hheadTail.1
      exact mem_reverse_nat.mp hmem
    · exact nodup_reverse_nat hheadTail.2
  · intro a ha b hb
    rcases List.mem_cons.mp hb with hbh | hbt
    · subst b
      exact hparts.2.2 a ha head List.mem_cons_self
    · exact hparts.2.2 a ha b
        (List.mem_cons_of_mem _ (mem_reverse_nat.mp hbt))

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

/-- Trace-valued arbitrary-path retrace.  This strengthens the existing
`retrace_linked_passages` endpoint theorem by retaining the reversed passage
list, which lets the theta proof locate its first mouth contact. -/
theorem physicalTrace_retrace_linked_passages
    (w : Wiring) (u : Tongues) (p x ell : Nat)
    (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hentry : w.link ell = some p) :
    PhysicalTrace w (lastPassageExit x rest, u)
      (reversePassages ((p, x) :: rest)) (ell, u) := by
  induction rest generalizing p x ell with
  | nil =>
      have hback : w.link p = some ell := w.symm _ _ hentry
      have hgroove := hgrooved (p, x) List.mem_cons_self
      exact PhysicalTrace.cons hgroove hback (PhysicalTrace.nil _)
  | cons passage rest ih =>
      rcases passage with ⟨q, y⟩
      have hxy : w.link x = some q := hlinked.1
      have htailLinked : LinkedPassages w ((q, y) :: rest) := hlinked.2
      have htailGrooved : PassagesGrooved u ((q, y) :: rest) := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      have htail := ih q y x htailLinked htailGrooved hxy
      have hback : w.link p = some ell := w.symm _ _ hentry
      have hheadGroove := hgrooved (p, x) List.mem_cons_self
      have hhead : PhysicalTrace w (x, u) [(x, p)] (ell, u) :=
        PhysicalTrace.cons hheadGroove hback (PhysicalTrace.nil _)
      exact htail.append hhead

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
  cases hrecordedList : recorded with
  | nil =>
      have htrace := hrecorded
      rw [hrecordedList] at htrace
      have hEq : (g, base) = (oldEntry, mouthState) := by
        simpa [stepN] using htrace.sound
      have hgo : g = oldEntry := congrArg Prod.fst hEq
      have hback : w.link oldEntry = some e := by
        apply w.symm
        simpa [hgo] using hentry
      simpa [reversePassages] using
        (PhysicalTrace.cons hcontact hback (PhysicalTrace.nil (e, v)))
  | cons passage rest =>
      rcases passage with ⟨a, b⟩
      have htrace := hrecorded
      rw [hrecordedList] at htrace
      have hgrooved' : PassagesGrooved v ((a, b) :: rest) := by
        simpa [hrecordedList] using hgrooved
      have hstart : g = a := htrace.head_arrive.1
      have hlast : w.link (lastPassageExit b rest) = some oldEntry :=
        htrace.last_link
      have hback : w.link oldEntry = some (lastPassageExit b rest) :=
        w.symm _ _ hlast
      have hhead : PhysicalTrace w (p, u) [(p, oldEntry)]
          (lastPassageExit b rest, v) :=
        PhysicalTrace.cons hcontact hback (PhysicalTrace.nil _)
      have hreverse := physicalTrace_retrace_linked_passages w v
        a b e rest htrace.linked hgrooved'
        (by simpa [hstart] using hentry)
      simpa [reversePassages] using hhead.append hreverse

theorem backward_contact_settles_grooved_cycle
    {w : Wiring} {g e p oldEntry : Nat}
    {oldBase oldEnd base u v : Tongues}
    {recorded approach : List Passage}
    (hrecorded :
      PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, base) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach) :
    SettlesOnSimpleCycle w (p, u) := by
  have hback := physicalTrace_contact_retraces_prefix
    hrecorded hrecordedGrooved hentry hcontact
  have hforward := happroach.replay_grooved v happroachGrooved
  let cycle := (p, oldEntry) ::
    reversePassages recorded ++ approach
  have hcycle : PhysicalTrace w (p, u) cycle (p, v) := by
    dsimp [cycle]
    simpa [List.append_assoc] using hback.append hforward
  have hheadGrooved : arrive v oldEntry = (p, v) := by
    have hbackLocal := arrive_back u p
    rwa [hcontact] at hbackLocal
  have hallGrooved : PassagesGrooved v cycle := by
    intro passage hp
    dsimp [cycle] at hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadGrooved
    · rcases List.mem_append.mp htail with hold | hnew
      · exact reversePassages_grooved hrecordedGrooved passage hold
      · exact happroachGrooved passage hnew
  have hperiod : stepN w cycle.length (p, v) = some (p, v) := by
    dsimp [cycle]
    exact run_grooved_passages w v p oldEntry p
      (reversePassages recorded ++ approach)
      hcycle.linked hallGrooved hcycle.last_link
  exact ⟨cycle.length, v, by simp [cycle], hcycle.sound, hperiod⟩

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

theorem linked_after_occurrence {w : Wiring}
    {p x q y : Nat} {before after : List Passage}
    (hlinked : LinkedPassages w
      (before ++ (p, x) :: (q, y) :: after)) :
    w.link x = some q := by
  induction before with
  | nil => exact hlinked.1
  | cons passage before ih =>
      rcases passage with ⟨r, s⟩
      cases before with
      | nil => exact hlinked.2.1
      | cons passage before => exact ih hlinked.2

theorem lastPassageExit_append_cons
    (z p x : Nat) (before after : List Passage) :
    lastPassageExit z (before ++ (p, x) :: after) =
      lastPassageExit x after := by
  induction before generalizing z with
  | nil => rfl
  | cons passage before ih =>
      simpa [lastPassageExit] using ih passage.2

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

theorem crossed_revisit_capture_from_mouth
    (w : Wiring) {g e p x q : Nat}
    {base u₀ u v : Tongues} {runway path : List Passage}
    (hrunway : PhysicalTrace w (g, base) runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hrepeat : arrive u q = (p, v))
    (hxq : x ≠ q)
    (hentry : w.link e = some g)
    (state : Tongues)
    (hrunwayGrooved : PassagesGrooved state runway)
    (hpathGrooved : PassagesGrooved state path) :
    stepN w (path.length + 2 + runway.length)
      (p, flipAt state (p / 3)) = some (e, state) := by
  have hsimpleExcursion : SwitchSimple ((p, x) :: path) := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).2.1
  have hsimpleExcursion' := hsimpleExcursion
  unfold SwitchSimple at hsimpleExcursion'
  simp only [List.map_cons, List.nodup_cons] at hsimpleExcursion'
  have hpathForeign : ∀ passage ∈ path,
      passageSwitch passage ≠ p / 3 := by
    intro passage hp hEq
    apply hsimpleExcursion'.1
    apply List.mem_map.mpr
    exact ⟨passage, hp, hEq⟩
  have hpathFlipped :
      PassagesGrooved (flipAt state (p / 3)) path :=
    grooved_after_flip_other hpathGrooved hpathForeign
  cases runway with
  | nil =>
      cases hrunway
      have hmouth : w.link g = some e := w.symm _ _ hentry
      have hcore := crossed_excursion_core_reflector w hexcursion
        hsimpleExcursion hrepeat hxq hmouth
      obtain ⟨hstep, _⟩ := hcore (flipAt state (g / 3)) hpathFlipped
      simpa [flipAt_flipAt] using hstep
  | cons passage rest =>
      rcases passage with ⟨a, b⟩
      have hg : g = a := hrunway.head_arrive.1
      have hlast : w.link (lastPassageExit b rest) = some p :=
        hrunway.last_link
      have hmouth : w.link p = some (lastPassageExit b rest) :=
        w.symm _ _ hlast
      have hcore := crossed_excursion_core_reflector w hexcursion
        hsimpleExcursion hrepeat hxq hmouth
      obtain ⟨hstep, _⟩ := hcore (flipAt state (p / 3)) hpathFlipped
      have hback := retrace_linked_passages w state a b e rest
        hrunway.linked hrunwayGrooved (by simpa [hg] using hentry)
      rw [stepN_add, hstep]
      simpa [flipAt_flipAt] using hback

/-! ## Splicing a first contact into the capture -/

/-- A trace prefix which does not visit `k` is unchanged by flipping `k`;
if its endpoint is the old lobe's mouth, append the mouth-capture and obtain
an exact return to the prefix's starting port. -/
theorem theta_capture_after_unvisited_prefix
    {w : Wiring} {e p k cap : Nat} {u : Tongues}
    {before : List Passage}
    (hprefix : PhysicalTrace w (e, u) before (p, u))
    (hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ k)
    (hcapture : stepN w cap (p, flipAt u k) = some (e, u)) :
    stepN w (before.length + cap) (e, flipAt u k) =
      some (e, u) := by
  have hprefixFlip := hprefix.flip_unvisited hforeign
  rw [stepN_add, hprefixFlip.sound]
  exact hcapture

theorem flipped_prefix_trailing_then
    {w : Wiring} {e p x q k tailSteps : Nat}
    {u : Tongues} {before : List Passage}
    {finish : Nat × Tongues}
    (hprefix : PhysicalTrace w (e, u) before (p, u))
    (hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ k)
    (hk : p / 3 = k)
    (hpbranch : p % 3 ≠ 0)
    (hgroove : arrive u p = (x, u))
    (hlink : w.link x = some q)
    (hsuffix : stepN w tailSteps (q, u) = some finish) :
    stepN w (before.length + 1 + tailSteps)
      (e, flipAt u k) = some finish := by
  have hprefixFlip := hprefix.flip_unvisited hforeign
  have hrepair : arrive (flipAt u k) p = (x, u) := by
    rw [← hk]
    exact flipped_passage_forward_trailing hgroove hpbranch
  have hone : stepN w 1 (p, flipAt u k) = some (q, u) := by
    simp [stepN, step, hrepair, hlink]
  have hlen : before.length + 1 + tailSteps =
      before.length + (1 + tailSteps) := by omega
  rw [hlen]
  rw [stepN_add, hprefixFlip.sound]
  simp only [Option.bind_some]
  rw [stepN_add, hone]
  exact hsuffix

theorem suffix_after_physical_prefix
    {w : Wiring} {start middle finish : Nat × Tongues}
    {passages : List Passage} {total tail : Nat}
    (hprefix : PhysicalTrace w start passages middle)
    (hlen : total = passages.length + tail)
    (hfull : stepN w total start = some finish) :
    stepN w tail middle = some finish := by
  rw [hlen, stepN_add, hprefix.sound] at hfull
  exact hfull

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

/-- The mouth of every nondegenerate manufactured reflector is the stem of
its switch. -/
theorem ManufacturedFlipReflector.mouth_is_stem
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
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

theorem ManufacturedFlipReflector.firstArm_switch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    A.firstArm / 3 = A.actionSwitch := by
  obtain ⟨after, hhead⟩ := A.candyTrace.head_arrive.2
  have hs := arrive_exit_switch A.mouthState A.mouth
  rw [hhead] at hs
  simpa [ManufacturedFlipReflector.actionSwitch] using hs

theorem ManufacturedFlipReflector.secondArm_switch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
    A.secondArm / 3 = A.actionSwitch := by
  have hs := arrive_exit_switch A.returnState A.secondArm
  rw [A.crossed] at hs
  simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm

theorem ManufacturedFlipReflector.firstArm_branch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
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

theorem ManufacturedFlipReflector.secondArm_branch
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
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
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
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
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hgrooved : PassagesGrooved state A.runway) :
    PhysicalTrace w (g, state) A.runway (A.mouth, state) := by
  cases hrunway : A.runway with
  | nil =>
      have htrace := A.runwayTrace
      rw [hrunway] at htrace
      have hs : (g, A.base) = (A.mouth, A.mouthState) := by
        simpa [stepN] using htrace.sound
      have hgm : g = A.mouth := congrArg Prod.fst hs
      simpa [hrunway, hgm] using (PhysicalTrace.nil (g, state))
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace := A.runwayTrace
      rw [hrunway] at htrace
      have hgrooved' :
          PassagesGrooved state ((p, x) :: rest) := by
        simpa [hrunway] using hgrooved
      have hstart : g = p := htrace.head_arrive.1
      have htrace := physicalTrace_grooved_passages w state p x
        A.mouth rest htrace.linked hgrooved' htrace.last_link
      simpa [hrunway, hstart] using htrace

/-- Candy traversal in its recorded direction, before the mouth switch is
pinned on the return arm. -/
theorem ManufacturedFlipReflector.candy_forward_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
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
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
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
  cases hcandy : A.candy with
  | nil =>
      have htrace := A.candyTrace
      rw [hcandy] at htrace
      have hlast := htrace.last_link
      have hback : w.link A.secondArm = some A.firstArm :=
        w.symm _ _ (by simpa [lastPassageExit] using hlast)
      simpa [hcandy, reversePassages] using
        (PhysicalTrace.cons hmouthForward hback (PhysicalTrace.nil _))
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace := A.candyTrace
      rw [hcandy] at htrace
      have hgrooved' : PassagesGrooved state ((p, x) :: rest) := by
        simpa [hcandy] using hgrooved
      have hfirstLink : w.link A.firstArm = some p :=
        htrace.linked.1
      have hlast :
          w.link (lastPassageExit x rest) = some A.secondArm := by
        simpa [lastPassageExit] using htrace.last_link
      have hback :
          w.link A.secondArm = some (lastPassageExit x rest) :=
        w.symm _ _ hlast
      have hhead : PhysicalTrace w (A.mouth, state)
          [(A.mouth, A.secondArm)]
          (lastPassageExit x rest, state) :=
        PhysicalTrace.cons hmouthForward hback (PhysicalTrace.nil _)
      have hreverse := physicalTrace_retrace_linked_passages w state
        p x A.firstArm rest htrace.linked.2
        hgrooved' hfirstLink
      simpa [hcandy, reversePassages] using hhead.append hreverse

theorem ManufacturedFlipReflector.reverse_support_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
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

/-- No-change prefix reaching a recorded-direction candy occurrence. -/
theorem ManufacturedFlipReflector.forward_prefix_to_candy_occurrence
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hpaths : PathGrooves [A.runway, A.candy] state)
    (hselected : state A.actionSwitch = bval A.firstArm)
    {before after : List Passage} {p x : Nat}
    (hoccurs : A.candy = before ++ (p, x) :: after) :
    PhysicalTrace w (g, state)
      (A.runway ++ (A.mouth, A.firstArm) :: before) (p, state) ∧
      (∀ passage ∈
          A.runway ++ (A.mouth, A.firstArm) :: before,
        passageSwitch passage ≠ passageSwitch (p, x)) := by
  have hp := pathGrooves_pair.mp hpaths
  have hrun := A.runway_trace state hp.1
  have hcandy := A.candy_forward_trace state hselected hp.2
  have hfull := hrun.append hcandy
  have hgrooved := hfull.grooved_of_switchSimple A.simple
  have hsplit :
      A.runway ++ (A.mouth, A.firstArm) :: A.candy =
        (A.runway ++ (A.mouth, A.firstArm) :: before) ++
          (p, x) :: after := by
    rw [hoccurs]
    simp [List.append_assoc]
  exact simple_grooved_trace_prefix_to_occurrence
    hfull hsplit hgrooved A.simple

/-- No-change prefix reaching the same candy occurrence when the candy is
traversed in the opposite direction. -/
theorem ManufacturedFlipReflector.reverse_prefix_to_candy_occurrence
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
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
theorem ManufacturedFlipReflector.support_foreign
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e) :
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
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hrunway : PassagesGrooved state A.runway)
    (hcandy : PassagesGrooved state A.candy) :
    stepN w (A.candy.length + 2 + A.runway.length)
      (A.mouth, flipAt state A.actionSwitch) = some (e, state) := by
  exact crossed_revisit_capture_from_mouth w A.runwayTrace A.candyTrace
    A.simple A.crossed A.arms_ne A.entryEdge state hrunway hcandy

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
  cases hrunway : A.runway with
  | nil =>
      have htrace := A.runwayTrace
      rw [hrunway] at htrace
      have hs : (g, A.base) = (A.mouth, A.mouthState) := by
        simpa [stepN] using htrace.sound
      have hgm : g = A.mouth := congrArg Prod.fst hs
      simpa [hrunway, hgm] using (PhysicalTrace.nil (g, state))
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace := A.runwayTrace
      rw [hrunway] at htrace
      have hgrooved' :
          PassagesGrooved state ((p, x) :: rest) := by
        simpa [hrunway] using hgrooved
      have hstart : g = p := htrace.head_arrive.1
      have hrebased := physicalTrace_grooved_passages w state p x
        A.mouth rest htrace.linked hgrooved' htrace.last_link
      simpa [hrunway, hstart] using hrebased

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

theorem ManufacturedReflector.runway_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    PhysicalTrace w (g, A.baseState) A.runway A.mouthConfig := by
  cases A with
  | stay R => exact R.runwayTrace
  | flip R => exact R.runwayTrace

theorem ManufacturedReflector.runway_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    SwitchSimple A.runway := by
  cases A with
  | stay R =>
      have hs := R.simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).1
  | flip R =>
      have hs := R.simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).1

theorem ManufacturedReflector.exploration_trace
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    PhysicalTrace w (g, A.baseState) A.exploration A.preReturn := by
  cases A with
  | stay R => exact R.runwayTrace.append R.coreTrace
  | flip R => exact R.runwayTrace.append R.candyTrace

/-- The local return passage of either manufactured-reflector constructor
contacts the retained runway at its mouth and produces the advertised
activated state. -/
theorem ManufacturedReflector.return_arrive_mouth
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
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
theorem ManufacturedReflector.return_arrive
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    ∃ exit, arrive A.preReturn.2 A.preReturn.1 =
      (exit, A.activatedState) :=
  ⟨A.mouthConfig.1, A.return_arrive_mouth⟩

theorem ManufacturedReflector.exploration_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    SwitchSimple A.exploration := by
  cases A with
  | stay R => exact R.simple
  | flip R => exact R.simple

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
    (hfresh : arrive state p = (x, next))
    (hchanged : next (p / 3) ≠ state (p / 3)) :
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
      (by simpa [passageSwitch] using horientedSwitch) hchanged


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
  classical
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
  classical
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


theorem manufactured_runway_theta_capture
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    {before after : List Passage} {x : Nat}
    (hoccurs :
      B.runway = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hAcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  have hlinked : LinkedPassages w
      (before ++ (A.mouth, x) :: after) := by
    rw [← hoccurs]
    exact B.runwayTrace.linked
  have hgrooved : PassagesGrooved state
      (before ++ (A.mouth, x) :: after) := by
    rw [← hoccurs]
    exact (pathGrooves_pair.mp hB).1
  have hsimpleRunway : SwitchSimple B.runway := by
    have hs := B.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hsimple : SwitchSimple
      (before ++ (A.mouth, x) :: after) := by
    rwa [← hoccurs]
  cases before with
  | nil =>
      have htrace := B.runwayTrace
      rw [hoccurs] at htrace
      have hstart : e = A.mouth := htrace.head_arrive.1
      refine ⟨A.candy.length + 2 + A.runway.length, ?_⟩
      simpa [hstart] using hAcapture
  | cons passage before =>
      rcases passage with ⟨r, y⟩
      have hprefixData := simple_grooved_prefix_to_occurrence
        hlinked hgrooved hsimple
      have htrace := B.runwayTrace
      rw [hoccurs] at htrace
      have hstart : e = r := htrace.head_arrive.1
      have hprefix :
          PhysicalTrace w (e, state) ((r, y) :: before)
            (A.mouth, state) := by
        simpa [hstart] using hprefixData.1
      have hforeign : ∀ passage ∈ (r, y) :: before,
          passageSwitch passage ≠ A.actionSwitch := by
        intro passage hp
        have hne := hprefixData.2 passage hp
        simpa [passageSwitch,
          ManufacturedFlipReflector.actionSwitch] using hne
      refine ⟨((r, y) :: before).length +
        (A.candy.length + 2 + A.runway.length), ?_⟩
      exact theta_capture_after_unvisited_prefix hprefix hforeign hAcapture

/-- If the same mouth occurrence is oriented the other way on the new
runway, it is met trailing-first.  The passage then repairs the old flip and
the new reflector completes exactly as it would have from the unflipped
state. -/
theorem manufactured_runway_theta_repairs
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hB : PathGrooves [B.runway, B.candy] state)
    {before after : List Passage} {p : Nat}
    (hoccurs :
      B.runway = before ++ (p, A.mouth) :: after) :
    stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, flipAt state A.actionSwitch) =
        some (g, flipAt state B.actionSwitch) := by
  have hsimpleRunway : SwitchSimple B.runway := by
    have hs := B.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hrunwayGrooved : PassagesGrooved state B.runway :=
    (pathGrooves_pair.mp hB).1
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    B.runwayTrace hoccurs hrunwayGrooved hsimpleRunway
  have hmem : (p, A.mouth) ∈ B.runway := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgrooveBack : arrive state A.mouth = (p, state) :=
    hrunwayGrooved (p, A.mouth) hmem
  have hforward : arrive state p = (A.mouth, state) :=
    groove_forward hgrooveBack
  have hpk : p / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state p
    rw [hforward] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hpbranch : p % 3 ≠ 0 := by
    intro hp
    have hne := arrive_exit_ne state p
    rw [hforward] at hne
    have hmouthStem := A.mouth_is_stem
    have hpk' : p / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hpk
    apply hne
    omega
  have hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch, hpk] using hne
  have hlinked : LinkedPassages w
      (before ++ (p, A.mouth) :: after) := by
    rw [← hoccurs]
    exact B.runwayTrace.linked
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases after with
    | nil =>
        have htrace := B.runwayTrace
        rw [hoccurs] at htrace
        obtain ⟨middle, hbeforeTrace, htargetTrace⟩ :=
          htrace.split_append
        have hlast := htargetTrace.last_link
        exact ⟨B.mouth, by simpa [lastPassageExit] using hlast⟩
    | cons passage rest =>
        rcases passage with ⟨q, y⟩
        exact ⟨q, linked_after_occurrence hlinked⟩
  have htarget :
      PhysicalTrace w (p, state) [(p, A.mouth)] (q, state) :=
    PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
  have hprefixTarget := hprefixData.1.append htarget
  have hprefixSound :
      stepN w (before.length + 1) (e, state) = some (q, state) := by
    simpa using hprefixTarget.sound
  have hBfull := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBfull
  have hRlen : B.runway.length =
      before.length + 1 + after.length := by
    rw [hoccurs]
    simp only [List.length_append, List.length_cons]
    omega
  let tailSteps := after.length + B.candy.length + 2 + B.runway.length
  have hlen : 2 * B.runway.length + B.candy.length + 2 =
      (before.length + 1) + tailSteps := by
    dsimp [tailSteps]
    omega
  have hsuffix :
      stepN w tailSteps (q, state) =
        some (g, flipAt state B.actionSwitch) := by
    rw [hlen, stepN_add, hprefixSound] at hBfull
    exact hBfull
  have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
    hpk hpbranch hforward hlink hsuffix
  simpa [tailSteps, hlen] using hrepair

/-- Orientation-free runway contact.  A visit to the old mouth switch on the
new runway is necessarily either the captured facing case or the self-healing
trailing case; degree three leaves no third possibility. -/
theorem manufactured_runway_fault_dichotomy
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (passage : Passage)
    (hmem : passage ∈ B.runway)
    (hsw : passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
  rcases passage with ⟨p, x⟩
  obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
  have hstem := B.runwayTrace.passage_stem_endpoint (p, x) hmem
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  change p / 3 = A.actionSwitch at hsw
  have hmouth : A.mouth = 3 * A.actionSwitch := by
    have hs := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  rcases hstem with hp | hx
  · have hpMouth : p = A.mouth := by
      omega
    subst p
    left
    exact manufactured_runway_theta_capture A B state hA hB hoccurs
  · have hxMouth : x = A.mouth := by
      omega
    right
    exact manufactured_runway_theta_repairs A B state hB
      (by simpa [hxMouth] using hoccurs)

/-! ## The first theta contact: candy case -/

theorem manufactured_candy_forward_theta_capture
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.firstArm)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.candy = before ++ (A.mouth, x) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hprefixData := B.forward_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hforeign : ∀ passage ∈
      B.runway ++ (B.mouth, B.firstArm) :: before,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hne
  have hcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  refine ⟨(B.runway ++
      (B.mouth, B.firstArm) :: before).length +
        (A.candy.length + 2 + A.runway.length), ?_⟩
  exact theta_capture_after_unvisited_prefix hprefixData.1
    hforeign hcapture

theorem manufactured_candy_reverse_theta_capture
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.secondArm)
    {before after : List Passage} {p : Nat}
    (hoccurs : B.candy = before ++ (p, A.mouth) :: after) :
    ∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) := by
  have hprefixData := B.reverse_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hforeign : ∀ passage ∈
      B.runway ++
        (B.mouth, B.secondArm) :: reversePassages after,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hne
  have hcapture := A.capture_from_mouth state
    (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
  refine ⟨(B.runway ++
      (B.mouth, B.secondArm) :: reversePassages after).length +
        (A.candy.length + 2 + A.runway.length), ?_⟩
  exact theta_capture_after_unvisited_prefix hprefixData.1
    hforeign hcapture

theorem manufactured_candy_forward_theta_repairs
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.firstArm)
    {before after : List Passage} {p : Nat}
    (hoccurs : B.candy = before ++ (p, A.mouth) :: after) :
    stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, flipAt state A.actionSwitch) =
        some (g, flipAt state B.actionSwitch) := by
  let pre := B.runway ++ (B.mouth, B.firstArm) :: before
  have hprefixData := B.forward_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hmem : (p, A.mouth) ∈ B.candy := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgrooveBack : arrive state A.mouth = (p, state) :=
    (pathGrooves_pair.mp hB).2 (p, A.mouth) hmem
  have hforward : arrive state p = (A.mouth, state) :=
    groove_forward hgrooveBack
  have hpk : p / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state p
    rw [hforward] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hpbranch : p % 3 ≠ 0 := by
    intro hp
    have hne := arrive_exit_ne state p
    rw [hforward] at hne
    have hm := A.mouth_is_stem
    have hpk' : p / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hpk
    apply hne
    omega
  have hforeign : ∀ passage ∈ pre,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [pre, passageSwitch, hpk] using hne
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases after with
    | nil =>
        have hlast := B.candyTrace.last_link
        rw [hoccurs, lastPassageExit_append_cons] at hlast
        exact ⟨B.secondArm, hlast⟩
    | cons passage rest =>
        rcases passage with ⟨q, y⟩
        have hcandyLinked : LinkedPassages w B.candy := by
          have htrace := B.candyTrace
          cases htrace with
          | cons harrive hheadLink candyTail =>
              exact candyTail.linked
        rw [hoccurs] at hcandyLinked
        exact ⟨q, linked_after_occurrence hcandyLinked⟩
  have htarget : PhysicalTrace w (p, state)
      [(p, A.mouth)] (q, state) :=
    PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
  have hprefixTarget := hprefixData.1.append htarget
  let tailSteps := after.length + 1 + B.runway.length
  have hClen : B.candy.length =
      before.length + 1 + after.length := by
    rw [hoccurs]
    simp only [List.length_append, List.length_cons]
    omega
  have hlen : 2 * B.runway.length + B.candy.length + 2 =
      (pre ++ [(p, A.mouth)]).length + tailSteps := by
    dsimp [pre, tailSteps]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hBfull := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBfull
  have hsuffix : stepN w tailSteps (q, state) =
      some (g, flipAt state B.actionSwitch) :=
    suffix_after_physical_prefix hprefixTarget hlen hBfull
  have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
    hpk hpbranch hforward hlink hsuffix
  have hrepairLen : pre.length + 1 + tailSteps =
      2 * B.runway.length + B.candy.length + 2 := by
    dsimp [pre, tailSteps]
    simp only [List.length_append, List.length_cons]
    omega
  rwa [hrepairLen] at hrepair

theorem manufactured_candy_reverse_theta_repairs
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hselected : state B.actionSwitch = bval B.secondArm)
    {before after : List Passage} {x : Nat}
    (hoccurs : B.candy = before ++ (A.mouth, x) :: after) :
    stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, flipAt state A.actionSwitch) =
        some (g, flipAt state B.actionSwitch) := by
  let pre := B.runway ++
    (B.mouth, B.secondArm) :: reversePassages after
  have hprefixData := B.reverse_prefix_to_candy_occurrence
    state hB hselected hoccurs
  have hmem : (A.mouth, x) ∈ B.candy := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hgroove : arrive state x = (A.mouth, state) :=
    (pathGrooves_pair.mp hB).2 (A.mouth, x) hmem
  have hxk : x / 3 = A.actionSwitch := by
    have hs := arrive_exit_switch state x
    rw [hgroove] at hs
    simpa [ManufacturedFlipReflector.actionSwitch] using hs.symm
  have hxbranch : x % 3 ≠ 0 := by
    intro hx
    have hne := arrive_exit_ne state x
    rw [hgroove] at hne
    have hm := A.mouth_is_stem
    have hxk' : x / 3 = A.mouth / 3 := by
      simpa [ManufacturedFlipReflector.actionSwitch] using hxk
    apply hne
    omega
  have hforeign : ∀ passage ∈ pre,
      passageSwitch passage ≠ A.actionSwitch := by
    intro passage hp
    have hne := hprefixData.2 passage hp
    simpa [pre, passageSwitch, hxk] using hne
  have hcandyLinked : LinkedPassages w B.candy := by
    have htrace := B.candyTrace
    cases htrace with
    | cons harrive hheadLink candyTail => exact candyTail.linked
  obtain ⟨q, hlink⟩ : ∃ q, w.link A.mouth = some q := by
    cases before with
    | nil =>
        have htrace := B.candyTrace
        rw [hoccurs] at htrace
        cases htrace with
        | @cons p₀ x₀ q₀ u₀ v₀ passages finish
            harrive hheadLink candyTail =>
            have hstart : q₀ = A.mouth := candyTail.head_arrive.1
            rw [hstart] at hheadLink
            exact ⟨B.firstArm, w.symm _ _ hheadLink⟩
    | cons passage rest =>
        rcases passage with ⟨r, y⟩
        have hcandyLinked' := hcandyLinked
        rw [hoccurs] at hcandyLinked'
        have hboundary := linked_boundary_of_append hcandyLinked'
        exact ⟨lastPassageExit y rest, w.symm _ _ hboundary⟩
  have htarget : PhysicalTrace w (x, state)
      [(x, A.mouth)] (q, state) :=
    PhysicalTrace.cons hgroove hlink (PhysicalTrace.nil _)
  have hprefixTarget := hprefixData.1.append htarget
  let tailSteps := before.length + 1 + B.runway.length
  have hClen : B.candy.length =
      before.length + 1 + after.length := by
    rw [hoccurs]
    simp only [List.length_append, List.length_cons]
    omega
  have hlen : 2 * B.runway.length + B.candy.length + 2 =
      (pre ++ [(x, A.mouth)]).length + tailSteps := by
    dsimp [pre, tailSteps]
    simp only [List.length_append, List.length_cons, List.length_nil,
      reversePassages_length]
    omega
  have hBfull := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBfull
  have hsuffix : stepN w tailSteps (q, state) =
      some (g, flipAt state B.actionSwitch) :=
    suffix_after_physical_prefix hprefixTarget hlen hBfull
  have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
    hxk hxbranch hgroove hlink hsuffix
  have hrepairLen : pre.length + 1 + tailSteps =
      2 * B.runway.length + B.candy.length + 2 := by
    dsimp [pre, tailSteps]
    simp only [List.length_append, List.length_cons,
      reversePassages_length]
    omega
  rwa [hrepairLen] at hrepair

/-- Orientation-free candy contact.  The selected candy arm determines
whether the recorded path is traversed forward or backward; in either
direction degree three again leaves exactly capture or self-repair. -/
theorem manufactured_candy_fault_dichotomy
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (passage : Passage)
    (hmem : passage ∈ B.candy)
    (hsw : passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
  rcases passage with ⟨p, x⟩
  obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
  have hstem := B.candyTrace.passage_stem_endpoint (p, x)
    (List.mem_cons_of_mem _ hmem)
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  change p / 3 = A.actionSwitch at hsw
  have hmouth : A.mouth = 3 * A.actionSwitch := by
    have hs := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  rcases B.selected_arm state with hforward | hreverse
  · rcases hstem with hp | hx
    · have hpMouth : p = A.mouth := by omega
      subst p
      left
      exact manufactured_candy_forward_theta_capture A B state
        hA hB hforward hoccurs
    · have hxMouth : x = A.mouth := by omega
      right
      exact manufactured_candy_forward_theta_repairs A B state
        hB hforward (by simpa [hxMouth] using hoccurs)
  · rcases hstem with hp | hx
    · have hpMouth : p = A.mouth := by omega
      right
      exact manufactured_candy_reverse_theta_repairs A B state
        hB hreverse (by simpa [hpMouth] using hoccurs)
    · have hxMouth : x = A.mouth := by omega
      left
      exact manufactured_candy_reverse_theta_capture A B state
        hA hB hreverse (by simpa [hxMouth] using hoccurs)

theorem manufactured_support_fault_dichotomy
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, flipAt state A.actionSwitch) =
          some (g, flipAt state B.actionSwitch) := by
  obtain ⟨path, hp, passage, hmem, hsw⟩ := hcontact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact manufactured_runway_fault_dichotomy A B state hA hB
      passage hmem hsw
  · exact manufactured_candy_fault_dichotomy A B state hA hB
      passage hmem hsw

/-- One complete macro-step in the one-sided theta case.  Whether the new
reflector self-repairs or is captured, starting at the old reflector's front
returns to that same front with exactly the new reflector's action applied.
-/
theorem manufactured_theta_half
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    ∃ travel, 0 < travel ∧
      stepN w travel (g, state) =
        some (g, flipAt state B.actionSwitch) := by
  have hArun := (A.toSupported.run state hA).1
  have hBrun := (B.toSupported.run state hB).1
  change stepN w (2 * A.runway.length + A.candy.length + 2)
      (g, state) = some (e, flipAt state A.actionSwitch) at hArun
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBrun
  have hfault := manufactured_support_fault_dichotomy
    A B state hA hB hcontact
  rcases hfault with hcapture | hrepair
  · obtain ⟨captureTravel, hcapture⟩ := hcapture
    refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      captureTravel +
        (2 * B.runway.length + B.candy.length + 2), by omega, ?_⟩
    have hlen :
        (2 * A.runway.length + A.candy.length + 2) +
            captureTravel +
              (2 * B.runway.length + B.candy.length + 2) =
          (2 * A.runway.length + A.candy.length + 2) +
            (captureTravel +
              (2 * B.runway.length + B.candy.length + 2)) := by omega
    rw [hlen, stepN_add, hArun]
    simp only [Option.bind_some]
    rw [stepN_add, hcapture]
    exact hBrun
  · refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      (2 * B.runway.length + B.candy.length + 2), by omega, ?_⟩
    rw [stepN_add, hArun]
    exact hrepair

/-- If only `A`'s mouth lies on `B`'s support, the theta macro-step can be
run twice.  `B`'s local action preserves `A`'s support, and its second
application restores the original tongue vector. -/
theorem manufactured_one_sided_theta_period
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : (LocalAction.flip B.actionSwitch).Avoids
      [A.runway, A.candy]) :
    ∃ travel, 0 < travel ∧
      stepN w travel (g, state) = some (g, state) := by
  obtain ⟨firstTravel, hfirstPos, hfirst⟩ :=
    manufactured_theta_half A B state hA hB hcontact
  have hA' : PathGrooves [A.runway, A.candy]
      (flipAt state B.actionSwitch) :=
    hA.after_avoiding_action hBA
  have hB' : PathGrooves [B.runway, B.candy]
      (flipAt state B.actionSwitch) :=
    (B.toSupported.run state hB).2
  obtain ⟨secondTravel, hsecondPos, hsecond⟩ :=
    manufactured_theta_half A B
      (flipAt state B.actionSwitch) hA' hB' hcontact
  refine ⟨firstTravel + secondTravel, by omega, ?_⟩
  rw [stepN_add, hfirst]
  simp only [Option.bind_some]
  rw [hsecond, flipAt_flipAt]

/-- If both lobe mouths lie on the opposite support, the first macro-step
reaches `flip B state`; from there the symmetric theta fault and the original
one form a closed cycle.  Thus mutual intersection is not a third dynamical
component: it is absorbed after one macro-step. -/
theorem manufactured_two_sided_theta_settles
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hAB : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : ∃ path ∈ [A.runway, A.candy],
      ∃ passage ∈ path,
        passageSwitch passage = B.actionSwitch) :
    ∃ lead period, 0 < period ∧
      stepN w lead (g, state) =
        some (g, flipAt state B.actionSwitch) ∧
      stepN w period (g, flipAt state B.actionSwitch) =
        some (g, flipAt state B.actionSwitch) := by
  obtain ⟨lead, hleadPos, hlead⟩ :=
    manufactured_theta_half A B state hA hB hAB
  have hreverseFault := manufactured_support_fault_dichotomy
    B A state hB hA hBA
  have hforwardFault := manufactured_support_fault_dichotomy
    A B state hA hB hAB
  have hBrun := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBrun
  rcases hreverseFault with hreverseCapture | hreverseRepair
  · obtain ⟨reverseTravel, hreverseCapture⟩ := hreverseCapture
    refine ⟨lead, reverseTravel + lead, by omega, hlead, ?_⟩
    rw [stepN_add, hreverseCapture]
    exact hlead
  · rcases hforwardFault with hforwardCapture | hforwardRepair
    · obtain ⟨forwardTravel, hforwardCapture⟩ := hforwardCapture
      refine ⟨lead,
        (2 * A.runway.length + A.candy.length + 2) +
        forwardTravel +
          (2 * B.runway.length + B.candy.length + 2), by omega,
            hlead, ?_⟩
      have hlen :
          (2 * A.runway.length + A.candy.length + 2) +
                forwardTravel +
                  (2 * B.runway.length + B.candy.length + 2) =
            (2 * A.runway.length + A.candy.length + 2) +
              (forwardTravel +
                (2 * B.runway.length + B.candy.length + 2)) := by omega
      rw [hlen, stepN_add, hreverseRepair]
      simp only [Option.bind_some]
      rw [stepN_add, hforwardCapture]
      exact hBrun
    · refine ⟨lead,
        (2 * A.runway.length + A.candy.length + 2) +
          (2 * B.runway.length + B.candy.length + 2), by omega,
            hlead, ?_⟩
      rw [stepN_add, hreverseRepair]
      exact hforwardRepair

/-! ## Degenerate identity reflector intersections -/

/-- Generic runway-fault engine.  It isolates the only data used by the
runway proofs above, so the same theta argument applies to the outward leg of
an identity reflector. -/
theorem runway_fault_dichotomy_general
    {w : Wiring} {g e total tailSteps : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    {base : Tongues} {runway : List Passage}
    {newFinish finish : Nat × Tongues}
    (htrace : PhysicalTrace w (e, base) runway newFinish)
    (hgrooved : PassagesGrooved state runway)
    (hsimple : SwitchSimple runway)
    (passage : Passage)
    {before after : List Passage}
    (hoccurs : runway = before ++ passage :: after)
    (hsw : passageSwitch passage = A.actionSwitch)
    (hdecomp : total = before.length + 1 + tailSteps)
    (hnormal : stepN w total (e, state) = some finish) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w total (e, flipAt state A.actionSwitch) = some finish := by
  rcases passage with ⟨p, x⟩
  have hmem : (p, x) ∈ runway := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    htrace hoccurs hgrooved hsimple
  have hstem := htrace.passage_stem_endpoint (p, x) hmem
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  change p / 3 = A.actionSwitch at hsw
  have hmouth : A.mouth = 3 * A.actionSwitch := by
    have hs := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  rcases hstem with hp | hx
  · have hpMouth : p = A.mouth := by omega
    subst p
    left
    have hforeign : ∀ passage ∈ before,
        passageSwitch passage ≠ A.actionSwitch := by
      intro passage hp
      have hne := hprefixData.2 passage hp
      simpa [passageSwitch,
        ManufacturedFlipReflector.actionSwitch] using hne
    have hcapture := A.capture_from_mouth state
      (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
    refine ⟨before.length +
      (A.candy.length + 2 + A.runway.length), ?_⟩
    exact theta_capture_after_unvisited_prefix hprefixData.1
      hforeign hcapture
  · have htargetMem : (p, x) ∈ runway := hmem
    have hgrooveBack : arrive state x = (p, state) :=
      hgrooved (p, x) htargetMem
    have hforward : arrive state p = (x, state) :=
      groove_forward hgrooveBack
    have hpbranch : p % 3 ≠ 0 := by
      intro hpmod
      have hne := arrive_exit_ne state p
      rw [hforward] at hne
      apply hne
      omega
    have hforeign : ∀ prior ∈ before,
        passageSwitch prior ≠ A.actionSwitch := by
      intro prior hprior
      have hne := hprefixData.2 prior hprior
      simpa [passageSwitch, hsw] using hne
    obtain ⟨q, hlink⟩ : ∃ q, w.link x = some q := by
      cases after with
      | nil =>
          have htrace' := htrace
          rw [hoccurs] at htrace'
          obtain ⟨middle, hbeforeTrace, htargetTrace⟩ :=
            htrace'.split_append
          have hlast := htargetTrace.last_link
          exact ⟨newFinish.1,
            by simpa [lastPassageExit] using hlast⟩
      | cons next rest =>
          rcases next with ⟨q, y⟩
          have hlinked : LinkedPassages w
              (before ++ (p, x) :: (q, y) :: rest) := by
            rw [← hoccurs]
            exact htrace.linked
          exact ⟨q, linked_after_occurrence hlinked⟩
    have htarget : PhysicalTrace w (p, state)
        [(p, x)] (q, state) :=
      PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
    have hprefixTarget := hprefixData.1.append htarget
    have hlen := hdecomp
    have hsuffix : stepN w tailSteps (q, state) = some finish := by
      have hprefixLen :
          (before ++ [(p, x)]).length = before.length + 1 := by simp
      apply suffix_after_physical_prefix hprefixTarget
      · simpa [hprefixLen] using hlen
      · exact hnormal
    right
    have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
      hsw hpbranch hforward hlink hsuffix
    rwa [← hlen] at hrepair

theorem manufactured_stay_support_fault_dichotomy
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
    (hcontact : ∃ path ∈ [B.runway, [(B.mouth, B.arm)]],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state)) ∨
      stepN w (2 * B.runway.length + 2)
        (e, flipAt state A.actionSwitch) = some (g, state) := by
  have hnormal := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + 2) (e, state) =
      some (g, state) at hnormal
  obtain ⟨path, hp, passage, hmem, hsw⟩ := hcontact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
    have hsimpleRunway : SwitchSimple B.runway := by
      have hs := B.simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).1
    have hRlen : B.runway.length =
        before.length + 1 + after.length := by
      rw [hoccurs]
      simp only [List.length_append, List.length_cons]
      omega
    let tailSteps := after.length + 2 + B.runway.length
    have hdecomp : 2 * B.runway.length + 2 =
        before.length + 1 + tailSteps := by
      dsimp [tailSteps]
      omega
    exact runway_fault_dichotomy_general
      (total := 2 * B.runway.length + 2)
      (tailSteps := tailSteps) A state hA B.runwayTrace
      (pathGrooves_pair.mp hB).1 hsimpleRunway passage
      hoccurs hsw hdecomp hnormal
  · simp only [List.mem_singleton] at hmem
    subst passage
    let route := B.runway ++ [(B.mouth, B.arm)]
    have hrun := B.runway_trace state (pathGrooves_pair.mp hB).1
    have hgrooveBack := passagesGrooved_singleton.mp
      (pathGrooves_pair.mp hB).2
    have hforward := groove_forward hgrooveBack
    have htarget : PhysicalTrace w (B.mouth, state)
        [(B.mouth, B.arm)] (B.arm, state) :=
      PhysicalTrace.cons hforward B.selfLink (PhysicalTrace.nil _)
    have hrouteTrace := hrun.append htarget
    have hrouteGrooved := hrouteTrace.grooved_of_switchSimple B.simple
    have hoccurs : route =
        B.runway ++ (B.mouth, B.arm) :: [] := by rfl
    have hdecomp : 2 * B.runway.length + 2 =
        B.runway.length + 1 + (B.runway.length + 1) := by omega
    exact runway_fault_dichotomy_general
      (total := 2 * B.runway.length + 2)
      (tailSteps := B.runway.length + 1) A state hA hrouteTrace
      hrouteGrooved B.simple (B.mouth, B.arm)
      hoccurs hsw hdecomp hnormal

/-- A flip reflector followed by a degenerate identity reflector always
closes after one theta macro-step, whether the supports are disjoint or meet.
-/
theorem manufactured_flip_then_stay_theta_period
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
    (hcontact : ∃ path ∈ [B.runway, [(B.mouth, B.arm)]],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    ∃ travel, 0 < travel ∧
      stepN w travel (g, state) = some (g, state) := by
  have hArun := (A.toSupported.run state hA).1
  change stepN w (2 * A.runway.length + A.candy.length + 2)
      (g, state) = some (e, flipAt state A.actionSwitch) at hArun
  have hBrun := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + 2)
      (e, state) = some (g, state) at hBrun
  have hfault := manufactured_stay_support_fault_dichotomy
    A B state hA hB hcontact
  rcases hfault with hcapture | hrepair
  · obtain ⟨captureTravel, hcapture⟩ := hcapture
    refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      captureTravel + (2 * B.runway.length + 2), by omega, ?_⟩
    have hlen :
        (2 * A.runway.length + A.candy.length + 2) +
              captureTravel + (2 * B.runway.length + 2) =
          (2 * A.runway.length + A.candy.length + 2) +
            (captureTravel + (2 * B.runway.length + 2)) := by omega
    rw [hlen, stepN_add, hArun]
    simp only [Option.bind_some]
    rw [stepN_add, hcapture]
    exact hBrun
  · refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      (2 * B.runway.length + 2), by omega, ?_⟩
    rw [stepN_add, hArun]
    exact hrepair

/-! ## Complete composition of two manufactured reflectors -/

theorem contact_of_not_avoids_flip
    {paths : List (List Passage)} {k : Nat}
    (hnot : ¬ (LocalAction.flip k).Avoids paths) :
    ∃ path ∈ paths, ∃ passage ∈ path,
      passageSwitch passage = k := by
  classical
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

/-- Eventual periodicity stated directly on raw train configurations. -/
def EventuallyPeriodic (w : Wiring) (start : Nat × Tongues) : Prop :=
  ∃ lead period settled,
    0 < period ∧
    stepN w lead start = some settled ∧
    stepN w period settled = some settled

/-- Eventual periodicity pulls back across any finite live prefix. -/
theorem EventuallyPeriodic.prepend
    {w : Wiring} {start middle : Nat × Tongues} {travel : Nat}
    (hprefix : stepN w travel start = some middle)
    (hperiodic : EventuallyPeriodic w middle) :
    EventuallyPeriodic w start := by
  obtain ⟨lead, period, settled, hpos, hlead, hperiod⟩ := hperiodic
  refine ⟨travel + lead, period, settled, hpos, ?_, hperiod⟩
  rw [stepN_add, hprefix]
  exact hlead

/-- Every live suffix of an eventually periodic deterministic run is itself
eventually periodic. -/
theorem EventuallyPeriodic.forward
    {w : Wiring} {start middle : Nat × Tongues} {travel : Nat}
    (hperiodic : EventuallyPeriodic w start)
    (hreach : stepN w travel start = some middle) :
    EventuallyPeriodic w middle := by
  obtain ⟨lead, period, settled, hpos, hlead, hperiod⟩ := hperiodic
  by_cases hle : travel ≤ lead
  · let remaining := lead - travel
    have hlen : lead = travel + remaining := by
      dsimp [remaining]
      omega
    have hmiddleSettled :
        stepN w remaining middle = some settled := by
      rw [hlen, stepN_add, hreach] at hlead
      exact hlead
    exact ⟨remaining, period, settled, hpos,
      hmiddleSettled, hperiod⟩
  · let offset := travel - lead
    have hlen : travel = lead + offset := by
      dsimp [offset]
      omega
    have hsettledMiddle :
        stepN w offset settled = some middle := by
      rw [hlen, stepN_add, hlead] at hreach
      exact hreach
    have hcycle : stepN w period middle = some middle := by
      have hround :
          stepN w (period + offset) settled = some middle := by
        rw [stepN_add, hperiod]
        exact hsettledMiddle
      have hcomm : period + offset = offset + period := by omega
      rw [hcomm, stepN_add, hsettledMiddle] at hround
      exact hround
    exact ⟨0, period, middle, hpos, by simp [stepN], hcycle⟩

/-- Reaching a configuration that settles on a tongue-stable simple cycle
is enough for raw eventual periodicity of the original run. -/
theorem eventuallyPeriodic_of_reaches_simple_cycle
    {w : Wiring} {start atRepeat : Nat × Tongues} {travel : Nat}
    (hprefix : stepN w travel start = some atRepeat)
    (hcycle : SettlesOnSimpleCycle w atRepeat) :
    EventuallyPeriodic w start := by
  obtain ⟨period, settled, hpos, honce, hfixed⟩ := hcycle
  apply EventuallyPeriodic.prepend hprefix
  exact ⟨period, period, (atRepeat.1, settled), hpos,
    honce, hfixed⟩


theorem manufactured_pair_period_of_avoids
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths) :
    stepN w (2 * (A.toSupported.travel + B.toSupported.travel))
      (g, state) = some (g, state) :=
  A.toSupported.paired_period B.toSupported hAB hBA state hA hB

theorem eventuallyPeriodic_of_period
    {w : Wiring} {start : Nat × Tongues} {period : Nat}
    (hpos : 0 < period)
    (hperiod : stepN w period start = some start) :
    EventuallyPeriodic w start := by
  exact ⟨0, period, start, hpos, by simp [stepN], hperiod⟩

theorem manufactured_pair_eventuallyPeriodic_of_avoids
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths) :
    EventuallyPeriodic w (g, state) := by
  have hperiod := manufactured_pair_period_of_avoids
    A B state hA hB hAB hBA
  apply eventuallyPeriodic_of_period
    (period := 2 * (A.toSupported.travel + B.toSupported.travel))
  · have hAp := A.travel_pos
    have hBp := B.travel_pos
    omega
  · exact hperiod

/-- **Complete theta theorem for two first-revisit components.**  Any two
opposite manufactured reflectors—identity or one-switch flip, disjoint or
intersecting in either direction—lead to a genuine periodic raw train
configuration.  No planarity or small-`N` argument occurs. -/
theorem manufactured_pair_eventually_periodic
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state) :
    EventuallyPeriodic w (g, state) := by
  classical
  cases A with
  | stay SA =>
      cases B with
      | stay SB =>
          exact manufactured_pair_eventuallyPeriodic_of_avoids
            (.stay SA) (.stay SB) state hA hB (by trivial) (by trivial)
      | flip FB =>
          change PathGrooves [SA.runway, [(SA.mouth, SA.arm)]] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
              [SA.runway, [(SA.mouth, SA.arm)]]
          · exact manufactured_pair_eventuallyPeriodic_of_avoids
              (.stay SA) (.flip FB) state hA hB (by trivial) hBA
          · have hcontact := contact_of_not_avoids_flip hBA
            obtain ⟨period, hpos, hperiod⟩ :=
              manufactured_flip_then_stay_theta_period
                FB SA state hB hA hcontact
            have hlead := (SA.toSupported.run state hA).1
            change stepN w (2 * SA.runway.length + 2) (g, state) =
              some (e, state) at hlead
            exact ⟨2 * SA.runway.length + 2, period, (e, state),
              hpos, hlead, hperiod⟩
  | flip FA =>
      cases B with
      | stay SB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [SB.runway, [(SB.mouth, SB.arm)]] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [SB.runway, [(SB.mouth, SB.arm)]]
          · exact manufactured_pair_eventuallyPeriodic_of_avoids
              (.flip FA) (.stay SB) state hA hB hAB (by trivial)
          · have hcontact := contact_of_not_avoids_flip hAB
            obtain ⟨period, hpos, hperiod⟩ :=
              manufactured_flip_then_stay_theta_period
                FA SB state hA hB hcontact
            exact eventuallyPeriodic_of_period hpos hperiod
      | flip FB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [FB.runway, FB.candy]
          · by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · exact manufactured_pair_eventuallyPeriodic_of_avoids
                (.flip FA) (.flip FB) state hA hB hAB hBA
            · have hcontactBA := contact_of_not_avoids_flip hBA
              have hArun := (FA.toSupported.run state hA)
              have hA' : PathGrooves [FA.runway, FA.candy]
                  (flipAt state FA.actionSwitch) := hArun.2
              have hB' : PathGrooves [FB.runway, FB.candy]
                  (flipAt state FA.actionSwitch) :=
                hB.after_avoiding_action hAB
              obtain ⟨period, hpos, hperiod⟩ :=
                manufactured_one_sided_theta_period FB FA
                  (flipAt state FA.actionSwitch) hB' hA'
                  hcontactBA hAB
              have hArunResult := hArun.1
              change stepN w (2 * FA.runway.length + FA.candy.length + 2)
                  (g, state) =
                    some (e, flipAt state FA.actionSwitch) at hArunResult
              exact ⟨2 * FA.runway.length + FA.candy.length + 2,
                period, (e, flipAt state FA.actionSwitch),
                hpos, hArunResult, hperiod⟩
          · have hcontactAB := contact_of_not_avoids_flip hAB
            by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · obtain ⟨period, hpos, hperiod⟩ :=
                manufactured_one_sided_theta_period FA FB state
                  hA hB hcontactAB hBA
              exact eventuallyPeriodic_of_period hpos hperiod
            · have hcontactBA := contact_of_not_avoids_flip hBA
              obtain ⟨lead, period, hpos, hlead, hperiod⟩ :=
                manufactured_two_sided_theta_settles FA FB state
                  hA hB hcontactAB hcontactBA
              exact ⟨lead, period,
                (g, flipAt state FB.actionSwitch),
                hpos, hlead, hperiod⟩

end GeneralN
