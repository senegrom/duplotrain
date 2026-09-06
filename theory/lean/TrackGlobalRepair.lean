import TrackTheta

/-!
# Global repair of a damaged manufactured reflector

The theta reduction leaves an old manufactured reflector whose support was
changed by the construction of a new reflector.  This file packages the
whole-route repair step.  A switch-simple grooved reference route, replayed
from an arbitrary tongue vector, has only two possibilities:

* some broken reference groove is first approached facing (through its stem);
* every broken groove is approached trailing, so the complete route repairs
  itself and restores all of its reusable support.

The second alternative then completes the reflector from the repaired route's
far endpoint.  Thus the remaining global obstruction is an explicit
facing-first theta diversion, rather than an unspecified damaged support.
-/

namespace GeneralN

/-- Split a list at its first element satisfying `P`.  The retained negative
prefix is what lets a damaged route be replayed up to its *first* facing
obstruction, rather than merely naming some obstruction somewhere on the
route. -/
theorem exists_first_satisfying_split
    {α : Type} (P : α → Prop) :
    ∀ xs : List α, (∃ x ∈ xs, P x) →
      ∃ before x after,
        xs = before ++ x :: after ∧
        (∀ y ∈ before, ¬ P y) ∧ P x := by
  intro xs hexists
  induction xs with
  | nil =>
      obtain ⟨x, hx, _⟩ := hexists
      cases hx
  | cons head tail ih =>
      by_cases hhead : P head
      · exact ⟨[], head, tail, rfl,
          (by intro y hy; cases hy), hhead⟩
      · have htail : ∃ x ∈ tail, P x := by
          obtain ⟨x, hx, hPx⟩ := hexists
          rcases List.mem_cons.mp hx with rfl | hx
          · exact absurd hPx hhead
          · exact ⟨x, hx, hPx⟩
        obtain ⟨before, x, after, hsplit, hbefore, hx⟩ := ih htail
        refine ⟨head :: before, x, after, ?_, ?_, hx⟩
        · rw [hsplit]
          simp
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hhead
          · exact hbefore y hy

/-- A split at an element absent from the prefix must occur in the suffix.
This list fact needs no uniqueness or switch-count argument. -/
theorem split_after_prefix_of_not_mem {α : Type}
    {lead rest before after : List α} {x : α}
    (hsplit : lead ++ rest = before ++ x :: after)
    (habsent : x ∉ lead) :
    ∃ middle, rest = middle ++ x :: after := by
  induction lead generalizing before with
  | nil => exact ⟨before, hsplit⟩
  | cons a lead ih =>
      cases before with
      | nil =>
          have heq : a = x := (List.cons.inj hsplit).1
          exact (habsent (heq ▸ List.mem_cons_self)).elim
      | cons b before =>
          exact ih (List.cons.inj hsplit).2
            (fun h => habsent (List.mem_cons_of_mem _ h))

/-- Two members of a switch-simple route that use the same switch are the
same recorded passage. -/
theorem SwitchSimple.passage_eq_of_mem
    {route : List Passage} (hsimple : SwitchSimple route)
    {left right : Passage}
    (hleft : left ∈ route) (hright : right ∈ route)
    (hswitch : passageSwitch left = passageSwitch right) :
    left = right := by
  unfold SwitchSimple at hsimple
  induction route generalizing left right with
  | nil => cases hleft
  | cons head tail ih =>
      simp only [List.map_cons] at hsimple
      rw [List.nodup_cons] at hsimple
      rcases List.mem_cons.mp hleft with hleftHead | hleftTail
      · rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · exact hleftHead.trans hrightHead.symm
        · exfalso
          apply hsimple.1
          have hmem : passageSwitch right ∈ tail.map passageSwitch :=
            List.mem_map.mpr ⟨right, hrightTail, rfl⟩
          rw [← hleftHead, hswitch]
          exact hmem
      · rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · exfalso
          apply hsimple.1
          have hmem : passageSwitch left ∈ tail.map passageSwitch :=
            List.mem_map.mpr ⟨left, hleftTail, rfl⟩
          rw [← hrightHead, ← hswitch]
          exact hmem
        · exact ih hsimple.2 hleftTail hrightTail hswitch

/-- A switch-simple route cannot contain both orientations of one genuine
passage. -/
theorem SwitchSimple.not_both_orientations
    {route : List Passage} (hsimple : SwitchSimple route)
    {p x : Nat}
    (hforward : (p, x) ∈ route)
    (hreverse : (x, p) ∈ route)
    (hswitch : p / 3 = x / 3)
    (hne : p ≠ x) : False := by
  have hEq := hsimple.passage_eq_of_mem hforward hreverse (by
    simp only [passageSwitch]
    exact hswitch)
  exact hne (congrArg Prod.fst hEq)

theorem PhysicalTrace.repair_preserving_paths_until_conflict
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {guardPaths : List (List Passage)}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PassagesGrooved start.2 passages)
    (state : Tongues)
    (hprotected : PathGrooves guardPaths state) :
    (∃ approach p x suffix contact other,
      passages = approach ++ (p, x) :: suffix ∧
      PhysicalTrace w (start.1, state) approach (p, contact) ∧
      PathGrooves guardPaths contact ∧
      p % 3 = 0 ∧
      arrive contact p = (other, contact) ∧ other ≠ x) ∨
    (∃ approach p x suffix u v path old,
      passages = approach ++ (p, x) :: suffix ∧
      PhysicalTrace w (start.1, state) approach (p, u) ∧
      PathGrooves guardPaths u ∧
      arrive u p = (x, v) ∧
      path ∈ guardPaths ∧ old ∈ path ∧
      passageSwitch old = p / 3 ∧
      v (p / 3) ≠ u (p / 3)) ∨
    ∃ finalState,
      PhysicalTrace w (start.1, state) passages
        (finish.1, finalState) ∧
      PassagesGrooved finalState passages ∧
      PathGrooves guardPaths finalState := by
  induction htrace generalizing state with
  | nil c =>
      exact Or.inr (Or.inr ⟨state, PhysicalTrace.nil _,
        (by intro passage hp; cases hp), hprotected⟩)
  | @cons p x q base nextBase rest finish harriveBase hlink tail ih =>
      unfold SwitchSimple at hsimple
      simp only [List.map_cons] at hsimple
      rw [List.nodup_cons] at hsimple
      have htailSimple : SwitchSimple rest := hsimple.2
      have htailForeign : ∀ passage ∈ rest,
          passageSwitch passage ≠ p / 3 := by
        intro passage hp hEq
        apply hsimple.1
        exact List.mem_map.mpr ⟨passage, hp, hEq⟩
      have htailBase : PassagesGrooved nextBase rest := by
        intro passage hp
        have hgrooveBase := hbase passage
          (List.mem_cons_of_mem _ hp)
        have hexitSwitch : passage.2 / 3 =
            passageSwitch passage := by
          have hs := arrive_exit_switch base passage.2
          rw [hgrooveBase] at hs
          exact hs.symm
        apply groove_transfer hgrooveBase
        rw [hexitSwitch]
        exact arrive_preserves_other harriveBase
          (htailForeign passage hp)
      let other := (arrive state p).1
      let next := (arrive state p).2
      have harrive : arrive state p = (other, next) := by
        exact Prod.ext rfl rfl
      by_cases hfollow : other = x
      · have harriveX : arrive state p = (x, next) := by
          simpa [hfollow] using harrive
        by_cases hcontact : ∃ path ∈ guardPaths, ∃ old ∈ path,
            passageSwitch old = p / 3 ∧
              next (p / 3) ≠ state (p / 3)
        · obtain ⟨path, hpath, old, hold, hswitch, hchanged⟩ :=
            hcontact
          exact Or.inr (Or.inl ⟨[], p, x, rest, state, next,
            path, old, rfl, PhysicalTrace.nil _, hprotected,
            harriveX, hpath, hold, hswitch, hchanged⟩)
        · have hquiet : ∀ path ∈ guardPaths, ∀ old ∈ path,
              passageSwitch old = p / 3 →
                next (p / 3) = state (p / 3) := by
            intro path hpath old hold hswitch
            apply Classical.byContradiction
            intro hchanged
            exact hcontact ⟨path, hpath, old, hold,
              hswitch, hchanged⟩
          have hprotectedNext : PathGrooves guardPaths next :=
            pathGrooves_after_arrive_without_support_change
              harriveX hprotected hquiet
          rcases ih htailSimple htailBase next hprotectedNext with
            hfacing | hrest
          · obtain ⟨approach, p₂, x₂, suffix, contact, diverted,
                hsplit, hprefix, hprotectedContact, hp₂, hlocal,
                hne⟩ := hfacing
            exact Or.inl ⟨(p, x) :: approach, p₂, x₂, suffix,
              contact, diverted, by simp [hsplit],
              PhysicalTrace.cons harriveX hlink hprefix,
              hprotectedContact, hp₂, hlocal, hne⟩
          · rcases hrest with hchanged | hcomplete
            · obtain ⟨approach, p₂, x₂, suffix, u, v, path, old,
                  hsplit, hprefix, hprotectedU, hlocal,
                  hpath, hold, hswitch, hchange⟩ := hchanged
              exact Or.inr (Or.inl
                ⟨(p, x) :: approach, p₂, x₂, suffix, u, v,
                  path, old, by simp [hsplit],
                  PhysicalTrace.cons harriveX hlink hprefix,
                  hprotectedU, hlocal, hpath, hold,
                  hswitch, hchange⟩)
            · obtain ⟨finalState, htailTrace,
                  htailGrooved, hprotectedFinal⟩ := hcomplete
              have hsameSwitch : x / 3 = p / 3 := by
                have hs := arrive_exit_switch state p
                rw [harriveX] at hs
                exact hs
              have hback : arrive next x = (p, next) := by
                have hb := arrive_back state p
                rw [harriveX] at hb
                exact hb
              have hpreserved : finalState (x / 3) =
                  next (x / 3) := by
                rw [hsameSwitch]
                exact htailTrace.preserves (p / 3) htailForeign
              have hheadGrooved : arrive finalState x =
                  (p, finalState) :=
                groove_transfer hback hpreserved
              have hallGrooved : PassagesGrooved finalState
                  ((p, x) :: rest) := by
                intro passage hp
                rcases List.mem_cons.mp hp with hhead | htailMem
                · simpa [hhead] using hheadGrooved
                · exact htailGrooved passage htailMem
              exact Or.inr (Or.inr ⟨finalState,
                PhysicalTrace.cons harriveX hlink htailTrace,
                hallGrooved, hprotectedFinal⟩)
      · have hp : p % 3 = 0 := by
          apply Classical.byContradiction
          intro hbranch
          apply hfollow
          dsimp [other]
          calc
            (arrive state p).1 = (arrive base p).1 :=
              trailing_arrive_exit_independent hbranch
            _ = x := congrArg Prod.fst harriveBase
        have hnext : next = state := by
          unfold arrive at harrive
          rw [if_pos hp] at harrive
          exact (Prod.mk.inj harrive).2.symm
        have harriveFacing : arrive state p = (other, state) := by
          simpa [hnext] using harrive
        exact Or.inl ⟨[], p, x, rest, state, other,
          rfl, PhysicalTrace.nil _, hprotected, hp,
          harriveFacing, hfollow⟩

theorem physicalTrace_prefix_comparable_with_endpoints
    {w : Wiring} {start finishA finishB : Nat × Tongues}
    {left right : List Passage}
    (hleft : PhysicalTrace w start left finishA)
    (hright : PhysicalTrace w start right finishB) :
    (∃ suffix,
      right = left ++ suffix ∧
      PhysicalTrace w finishA suffix finishB) ∨
    (∃ suffix,
      left = right ++ suffix ∧
      PhysicalTrace w finishB suffix finishA) := by
  rcases physicalTrace_passages_prefix_comparable hleft hright with
      hleftPrefix | hrightPrefix
  · obtain ⟨suffix, hsplit⟩ := hleftPrefix
    have hright' := hright
    rw [hsplit] at hright'
    obtain ⟨middle, hprefix, htail⟩ := hright'.split_append
    have hmiddle : middle = finishA := by
      have h₁ := hprefix.sound
      have h₂ := hleft.sound
      rw [h₂] at h₁
      exact (Option.some.inj h₁).symm
    subst middle
    exact Or.inl ⟨suffix, hsplit, htail⟩
  · obtain ⟨suffix, hsplit⟩ := hrightPrefix
    have hleft' := hleft
    rw [hsplit] at hleft'
    obtain ⟨middle, hprefix, htail⟩ := hleft'.split_append
    have hmiddle : middle = finishB := by
      have h₁ := hprefix.sound
      have h₂ := hright.sound
      rw [h₂] at h₁
      exact (Option.some.inj h₁).symm
    subst middle
    exact Or.inr ⟨suffix, hsplit, htail⟩

/-- Two deterministic traces which first arrive at the same avoided switch
must arrive through the same port.  Prefix comparability leaves an unmatched
suffix only if its first passage visits that switch, contradicting avoidance.
This is the endpoint form of "merge until the first named switch". -/
theorem physicalTrace_endpoints_eq_before_avoided_switch
    {w : Wiring} {start finishA finishB : Nat × Tongues}
    {left right : List Passage} {k : Nat}
    (hleft : PhysicalTrace w start left finishA)
    (hright : PhysicalTrace w start right finishB)
    (hfinishA : finishA.1 / 3 = k)
    (hfinishB : finishB.1 / 3 = k)
    (hleftForeign : ∀ passage ∈ left,
      passageSwitch passage ≠ k)
    (hrightForeign : ∀ passage ∈ right,
      passageSwitch passage ≠ k) :
    finishA = finishB := by
  rcases physicalTrace_prefix_comparable_with_endpoints hleft hright with
      ⟨suffix, hrightEq, htail⟩ | ⟨suffix, hleftEq, htail⟩
  · cases suffix with
    | nil =>
        cases htail
        rfl
    | cons passage rest =>
        have hstart := htail.head_arrive.1
        have hpassageMem : passage ∈ right := by
          rw [hrightEq]
          exact List.mem_append_right left List.mem_cons_self
        exfalso
        apply (hrightForeign passage hpassageMem).elim
        rcases passage with ⟨p, x⟩
        simp only at hstart
        simp [passageSwitch, ← hstart, hfinishA]
  · cases suffix with
    | nil =>
        cases htail
        rfl
    | cons passage rest =>
        have hstart := htail.head_arrive.1
        have hpassageMem : passage ∈ left := by
          rw [hleftEq]
          exact List.mem_append_right right List.mem_cons_self
        exfalso
        apply (hleftForeign passage hpassageMem).elim
        rcases passage with ⟨p, x⟩
        simp only at hstart
        simp [passageSwitch, ← hstart, hfinishB]

theorem source_of_mem_reversePassages
    {passage : Passage} {passages : List Passage}
    (hmem : passage ∈ reversePassages passages) :
    ∃ old ∈ passages, passage = (old.2, old.1) := by
  induction passages with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [reversePassages] at hmem
      rcases List.mem_append.mp hmem with hrest | hhead
      · obtain ⟨old, hold, hEq⟩ := ih hrest
        exact ⟨old, List.mem_cons_of_mem _ hold, hEq⟩
      · simp only [List.mem_singleton] at hhead
        exact ⟨head, List.mem_cons_self, hhead⟩

/-- The first candy arm is grooved whenever the action tongue selects it. -/
theorem ManufacturedFlipReflector.firstArm_groove_of_selected
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hselected : state A.actionSwitch = bval A.firstArm) :
    arrive state A.firstArm = (A.mouth, state) := by
  have hagree : state (A.firstArm / 3) = bval A.firstArm := by
    rw [A.firstArm_switch]
    exact hselected
  have hpin : pin state A.firstArm = state := pin_of_agrees hagree
  have hstem : 3 * (A.firstArm / 3) = A.mouth := by
    have hm := A.mouth_is_stem
    have hs := A.firstArm_switch
    unfold ManufacturedFlipReflector.actionSwitch at hs
    omega
  simp [arrive, A.firstArm_branch, hstem, hpin]

/-- The second candy arm is grooved whenever the action tongue selects it. -/
theorem ManufacturedFlipReflector.secondArm_groove_of_selected
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hselected : state A.actionSwitch = bval A.secondArm) :
    arrive state A.secondArm = (A.mouth, state) := by
  have hagree : state (A.secondArm / 3) = bval A.secondArm := by
    rw [A.secondArm_switch]
    exact hselected
  have hpin : pin state A.secondArm = state := pin_of_agrees hagree
  have hstem : 3 * (A.secondArm / 3) = A.mouth := by
    have hm := A.mouth_is_stem
    have hs := A.secondArm_switch
    unfold ManufacturedFlipReflector.actionSwitch at hs
    omega
  simp [arrive, A.secondArm_branch, hstem, hpin]

theorem ManufacturedReflector.support_grooves_of_orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (selector state : Tongues)
    (hroute : PassagesGrooved state (A.orientedRoute selector)) :
    PathGrooves A.toSupported.paths state := by
  cases A with
  | stay R =>
      change PassagesGrooved state
        (R.runway ++ [(R.mouth, R.arm)]) at hroute
      change PathGrooves [R.runway, [(R.mouth, R.arm)]] state
      apply pathGrooves_pair.mpr
      constructor
      · intro passage hp
        exact hroute passage (List.mem_append_left _ hp)
      · intro passage hp
        exact hroute passage (List.mem_append_right _ hp)
  | flip R =>
      change PathGrooves [R.runway, R.candy] state
      apply pathGrooves_pair.mpr
      by_cases hselected :
          selector R.actionSwitch = bval R.firstArm
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          if_pos] at hroute
        constructor
        · intro passage hp
          exact hroute passage (List.mem_append_left _ hp)
        · intro passage hp
          exact hroute passage
            (List.mem_append_right _ (List.mem_cons_of_mem _ hp))
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          if_false] at hroute
        constructor
        · intro passage hp
          exact hroute passage (List.mem_append_left _ hp)
        · intro passage hp
          have hreverse :
              arrive state passage.1 = (passage.2, state) := by
            exact hroute (passage.2, passage.1)
              (List.mem_append_right _
                (List.mem_cons_of_mem _ (reversePassage_mem hp)))
          exact groove_forward hreverse

/-- Align only the reflector's private action tongue with an arbitrary current
state.  Its reusable support avoids that tongue, so the aligned reference
still grooves every support path and statically realizes exactly the route
that the current state selects. -/
theorem ManufacturedReflector.current_route_reference
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (base state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths base) :
    ∃ reference,
      PathGrooves A.toSupported.paths reference ∧
      A.orientedRoute reference = A.orientedRoute state ∧
      A.orientedFinish reference = A.orientedFinish state ∧
      PassagesGrooved reference (A.orientedRoute state) ∧
      (∀ j, reference j ≠ base j → reference j = state j) := by
  cases A with
  | stay R =>
      have htrace :=
        (ManufacturedReflector.stay R).orientedRoute_trace base hpaths
      have hgrooved := htrace.grooved_of_switchSimple
        ((ManufacturedReflector.stay R).orientedRoute_simple base)
      exact ⟨base, hpaths, rfl, rfl, hgrooved,
        (by intro j hj; exact (hj rfl).elim)⟩
  | flip R =>
      by_cases hsame :
          state R.actionSwitch = base R.actionSwitch
      · have hroute :
            (ManufacturedReflector.flip R).orientedRoute base =
              (ManufacturedReflector.flip R).orientedRoute state := by
          simp only [ManufacturedReflector.orientedRoute]
          rw [hsame]
        have hfinish :
            (ManufacturedReflector.flip R).orientedFinish base =
              (ManufacturedReflector.flip R).orientedFinish state := by
          simp only [ManufacturedReflector.orientedFinish]
          rw [hsame]
        have htrace :=
          (ManufacturedReflector.flip R).orientedRoute_trace base hpaths
        have hgrooved := htrace.grooved_of_switchSimple
          ((ManufacturedReflector.flip R).orientedRoute_simple base)
        rw [hroute] at hgrooved
        exact ⟨base, hpaths, hroute, hfinish, hgrooved,
          (by intro j hj; exact (hj rfl).elim)⟩
      · let reference := flipAt base R.actionSwitch
        have hrefAction :
            reference R.actionSwitch = state R.actionSwitch := by
          dsimp [reference]
          simp only [flipAt, if_pos]
          cases hb : base R.actionSwitch <;>
            cases hs : state R.actionSwitch <;> simp_all
        have hreferencePaths :
            PathGrooves
              (ManufacturedReflector.flip R).toSupported.paths
              reference := by
          change PathGrooves [R.runway, R.candy]
            (flipAt base R.actionSwitch)
          change PathGrooves [R.runway, R.candy] base at hpaths
          have havoid : (LocalAction.flip R.actionSwitch).Avoids
              [R.runway, R.candy] := R.support_foreign
          exact hpaths.after_avoiding_action havoid
        have hroute :
            (ManufacturedReflector.flip R).orientedRoute reference =
              (ManufacturedReflector.flip R).orientedRoute state := by
          simp only [ManufacturedReflector.orientedRoute]
          rw [hrefAction]
        have hfinish :
            (ManufacturedReflector.flip R).orientedFinish reference =
              (ManufacturedReflector.flip R).orientedFinish state := by
          simp only [ManufacturedReflector.orientedFinish]
          rw [hrefAction]
        have htrace :=
          (ManufacturedReflector.flip R).orientedRoute_trace
            reference hreferencePaths
        have hgrooved := htrace.grooved_of_switchSimple
          ((ManufacturedReflector.flip R).orientedRoute_simple reference)
        rw [hroute] at hgrooved
        have hguard : ∀ j, reference j ≠ base j →
            reference j = state j := by
          intro j hj
          by_cases hja : j = R.actionSwitch
          · subst j
            exact hrefAction
          · have heq : reference j = base j := by
              simp [reference, flipAt, hja]
            exact (hj heq).elim
        exact ⟨reference, hreferencePaths,
          hroute, hfinish, hgrooved, hguard⟩

/-- Replay the route currently selected by a damaged reflector while keeping
an arbitrary second groove family intact.  This is the reflector-level form
of `repair_preserving_paths_until_conflict`.

The facing branch additionally proves that the obstructing tongue differs
from the reflector's base state and that the contact state still carries the
initial damaging value.  Those equalities connect the obstruction to the
other reflector's exact activation passage. -/
theorem ManufacturedReflector.repair_current_route_preserving_until_conflict
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (base state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths base)
    {guardPaths : List (List Passage)}
    (hguardPaths : PathGrooves guardPaths state) :
    (∃ before p x after contact other,
      A.orientedRoute state = before ++ (p, x) :: after ∧
      PhysicalTrace w (g, state) before (p, contact) ∧
      PathGrooves guardPaths contact ∧
      p % 3 = 0 ∧
      state (passageSwitch (p, x)) ≠
        base (passageSwitch (p, x)) ∧
      contact (passageSwitch (p, x)) =
        state (passageSwitch (p, x)) ∧
      arrive contact p = (other, contact) ∧ other ≠ x) ∨
    (∃ approach p x suffix u v path old,
      A.orientedRoute state = approach ++ (p, x) :: suffix ∧
      PhysicalTrace w (g, state) approach (p, u) ∧
      PathGrooves guardPaths u ∧
      arrive u p = (x, v) ∧
      path ∈ guardPaths ∧ old ∈ path ∧
      passageSwitch old = p / 3 ∧
      v (p / 3) ≠ u (p / 3)) ∨
    ∃ finalState,
      PhysicalTrace w (g, state) (A.orientedRoute state)
        (A.orientedFinish state, finalState) ∧
      PathGrooves A.toSupported.paths finalState ∧
      PathGrooves guardPaths finalState := by
  obtain ⟨reference, hreferencePaths, hroute, hfinish,
      hreferenceGrooved, hreferenceGuard⟩ :=
    A.current_route_reference base state hpaths
  have hreferenceTrace :=
    A.orientedRoute_trace reference hreferencePaths
  rw [hroute, hfinish] at hreferenceTrace
  have hsimple := A.orientedRoute_simple state
  rcases hreferenceTrace.repair_preserving_paths_until_conflict
      hsimple hreferenceGrooved state hguardPaths with
    hfacing | hrest
  · obtain ⟨before, p, x, after, contact, other,
        hsplit, hprefix, hguardContact, hstem,
        harrive, hother⟩ := hfacing
    have hsimple' := hsimple
    rw [hsplit] at hsimple'
    have hprefixForeign : ∀ passage ∈ before,
        passageSwitch passage ≠ passageSwitch (p, x) := by
      unfold SwitchSimple at hsimple'
      simp only [List.map_append, List.map_cons] at hsimple'
      have hparts := List.nodup_append.mp hsimple'
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (passageSwitch (p, x)) (by simp)
      exact hne hEq
    have hcontactState : contact (passageSwitch (p, x)) =
        state (passageSwitch (p, x)) :=
      hprefix.preserves _ hprefixForeign
    have hreferenceGroove :
        arrive reference x = (p, reference) :=
      hreferenceGrooved (p, x) (by
        rw [hsplit]
        exact List.mem_append_right before List.mem_cons_self)
    have hswitch : x / 3 = passageSwitch (p, x) := by
      have hs := arrive_exit_switch reference x
      rw [hreferenceGroove] at hs
      exact hs.symm
    have hstateReference : state (passageSwitch (p, x)) ≠
        reference (passageSwitch (p, x)) := by
      intro heq
      have hcurrentGroove : arrive contact x = (p, contact) := by
        apply groove_transfer hreferenceGroove
        rw [hswitch, hcontactState]
        exact heq
      have hforward := groove_forward hcurrentGroove
      rw [harrive] at hforward
      exact hother (congrArg Prod.fst hforward)
    have hreferenceBase : reference (passageSwitch (p, x)) =
        base (passageSwitch (p, x)) := by
      by_cases heq : reference (passageSwitch (p, x)) =
          base (passageSwitch (p, x))
      · exact heq
      · exfalso
        exact hstateReference (hreferenceGuard _ heq).symm
    have hstateBase : state (passageSwitch (p, x)) ≠
        base (passageSwitch (p, x)) := by
      intro heq
      apply hstateReference
      exact heq.trans hreferenceBase.symm
    exact Or.inl ⟨before, p, x, after, contact, other,
      hsplit, hprefix, hguardContact, hstem, hstateBase,
      hcontactState, harrive, hother⟩
  · rcases hrest with hchanged | hcomplete
    · exact Or.inr (Or.inl hchanged)
    · obtain ⟨finalState, htrace, hrouteGrooved,
          hguardFinal⟩ := hcomplete
      exact Or.inr (Or.inr ⟨finalState, htrace,
        A.support_grooves_of_orientedRoute state finalState
          hrouteGrooved,
        hguardFinal⟩)

/-- If the route selected by `selector` is grooved both in `selector` and in
`state`, then the action-switch tongue agrees.  Consequently both vectors
select exactly the same outward route and the same far endpoint. -/
theorem ManufacturedReflector.oriented_data_eq_of_route_grooved
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (selector state : Tongues)
    (hselector : PassagesGrooved selector (A.orientedRoute selector))
    (hstate : PassagesGrooved state (A.orientedRoute selector)) :
    A.orientedRoute state = A.orientedRoute selector ∧
      A.orientedFinish state = A.orientedFinish selector := by
  cases A with
  | stay R =>
      exact ⟨rfl, rfl⟩
  | flip R =>
      by_cases hselected :
          selector R.actionSwitch = bval R.firstArm
      · have hmem : (R.mouth, R.firstArm) ∈
            (ManufacturedReflector.flip R).orientedRoute selector := by
          simp [ManufacturedReflector.orientedRoute, hselected]
        have htongue := same_groove_same_tongue
          (hselector (R.mouth, R.firstArm) hmem)
          (hstate (R.mouth, R.firstArm) hmem)
        have hstateSelected :
            state R.actionSwitch = bval R.firstArm := by
          calc
            state R.actionSwitch = selector R.actionSwitch := by
              simpa [passageSwitch,
                ManufacturedFlipReflector.actionSwitch] using htongue.symm
            _ = bval R.firstArm := hselected
        constructor <;>
          simp [ManufacturedReflector.orientedRoute,
            ManufacturedReflector.orientedFinish,
            hselected, hstateSelected]
      · have hmem : (R.mouth, R.secondArm) ∈
            (ManufacturedReflector.flip R).orientedRoute selector := by
          simp [ManufacturedReflector.orientedRoute, hselected]
        have htongue := same_groove_same_tongue
          (hselector (R.mouth, R.secondArm) hmem)
          (hstate (R.mouth, R.secondArm) hmem)
        have hstateNotSelected :
            state R.actionSwitch ≠ bval R.firstArm := by
          intro heq
          apply hselected
          calc
            selector R.actionSwitch = state R.actionSwitch := by
              simpa [passageSwitch,
                ManufacturedFlipReflector.actionSwitch] using htongue
            _ = bval R.firstArm := heq
        constructor <;>
          simp [ManufacturedReflector.orientedRoute,
            ManufacturedReflector.orientedFinish,
            hselected, hstateNotSelected]

theorem ManufacturedReflector.changed_exploration_passage_mem_support
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    {passage : Passage} {before after : Tongues}
    (hmem : passage ∈ A.exploration)
    (harrive : arrive before passage.1 = (passage.2, after))
    (hchanged : after (passageSwitch passage) ≠
      before (passageSwitch passage)) :
    ∃ path ∈ A.toSupported.paths, passage ∈ path := by
  cases A with
  | stay R =>
      change passage ∈ R.runway ++ [(R.mouth, R.arm)] at hmem
      change ∃ path ∈ [R.runway, [(R.mouth, R.arm)]], passage ∈ path
      rcases List.mem_append.mp hmem with hrunway | hcore
      · exact ⟨R.runway, by simp, hrunway⟩
      · exact ⟨[(R.mouth, R.arm)], by simp, hcore⟩
  | flip R =>
      change passage ∈
        R.runway ++ (R.mouth, R.firstArm) :: R.candy at hmem
      change ∃ path ∈ [R.runway, R.candy], passage ∈ path
      rcases List.mem_append.mp hmem with hrunway | hcore
      · exact ⟨R.runway, by simp, hrunway⟩
      · rcases List.mem_cons.mp hcore with hmouth | hcandy
        · subst passage
          have hstate : after = before := by
            unfold arrive at harrive
            rw [if_pos R.mouth_is_stem] at harrive
            exact (Prod.mk.inj harrive).2.symm
          exact (hchanged (by rw [hstate])).elim
        · exact ⟨R.candy, by simp, hcandy⟩

theorem ManufacturedReflector.activated_change_return_or_exploration
    {w : Wiring} {g e j : Nat}
    (A : ManufacturedReflector w g e)
    (hchange : A.activatedState j ≠ A.baseState j) :
    (j = A.preReturn.1 / 3 ∧
      A.activatedState j ≠ A.preReturn.2 j) ∨
      ∃ before p x after u v,
        A.exploration = before ++ (p, x) :: after ∧
        passageSwitch (p, x) = j ∧
        PhysicalTrace w (g, A.baseState) before (p, u) ∧
        arrive u p = (x, v) ∧
        u j = A.baseState j ∧ A.activatedState j = v j ∧
        v j ≠ u j := by
  by_cases hreturnChange :
      A.activatedState j ≠ A.preReturn.2 j
  · left
    obtain ⟨returnExit, hreturnArrive⟩ := A.return_arrive
    have hj : j = A.preReturn.1 / 3 := by
      by_cases hne : j ≠ A.preReturn.1 / 3
      · exact (hreturnChange
          (arrive_preserves_other hreturnArrive hne)).elim
      · exact Classical.not_not.mp hne
    exact ⟨hj, hreturnChange⟩
  · right
    have hpreChange : A.preReturn.2 j ≠ A.baseState j := by
      intro heq
      apply hchange
      exact (Classical.not_not.mp hreturnChange).trans heq
    obtain ⟨before, p, x, after, u, v,
        hsplit, hswitch, htrace, harrive,
        hbase, hpre, hchanged⟩ :=
      A.exploration_trace.changed_switch_has_changed_passage
        A.exploration_simple hpreChange
    exact ⟨before, p, x, after, u, v,
      hsplit, hswitch, htrace, harrive, hbase,
      (Classical.not_not.mp hreturnChange).trans hpre,
      hchanged⟩

/-- Match a facing obstruction with the exact earlier passage that set its
tongue.  Except at the final repeated mouth, the damaging exploration
passage is a reusable support passage `(fresh, stem)`.  Replaying the old
route reaches that stem with the passage's post-state still installed, so it
must leave through `fresh`.  This is the concrete backward-theta edge needed
for route shortening. -/
theorem ManufacturedReflector.facing_exit_matches_activation_passage
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    {stem other : Nat} {contact : Tongues}
    (hchange : A.activatedState (stem / 3) ≠
      A.baseState (stem / 3))
    (hcontact : contact (stem / 3) =
      A.activatedState (stem / 3))
    (hstem : stem % 3 = 0)
    (hexit : arrive contact stem = (other, contact)) :
    (stem / 3 = A.preReturn.1 / 3 ∧
      A.activatedState (stem / 3) ≠
        A.preReturn.2 (stem / 3)) ∨
      ∃ fresh path,
        path ∈ A.toSupported.paths ∧ (fresh, stem) ∈ path ∧
        other = fresh := by
  rcases A.activated_change_return_or_exploration hchange with
    hreturn | hchanged
  · exact Or.inl hreturn
  · right
    obtain ⟨approach, fresh, exit, suffix, u, v,
        hsplit, hswitch, _htrace, harrive,
        _hbase, hactivated, hchanged⟩ := hchanged
    have hentrySwitch : fresh / 3 = stem / 3 := by
      simpa [passageSwitch] using hswitch
    have hchangedFresh : v (fresh / 3) ≠ u (fresh / 3) := by
      rw [hentrySwitch]
      exact hchanged
    obtain ⟨_hfreshBranch, hexitStem, _hv⟩ :=
      changed_arrival_is_trailing harrive hchangedFresh
    have hexitEq : exit = stem := by
      omega
    rw [hexitEq] at hsplit harrive
    have hchangedPassage :
        v (passageSwitch (fresh, stem)) ≠
          u (passageSwitch (fresh, stem)) := by
      simpa [passageSwitch] using hchangedFresh
    obtain ⟨path, hpath, hfreshSupport⟩ :=
      A.changed_exploration_passage_mem_support
        (by rw [hsplit]; exact
          List.mem_append_right approach List.mem_cons_self)
        harrive hchangedPassage
    have hback := arrive_back u fresh
    rw [harrive] at hback
    have hcontactV : contact (stem / 3) = v (stem / 3) := by
      calc
        contact (stem / 3) = A.activatedState (stem / 3) := hcontact
        _ = v (stem / 3) := hactivated
    have hcontactExit : arrive contact stem = (fresh, contact) :=
      groove_transfer hback hcontactV
    have hother : other = fresh := by
      rw [hexit] at hcontactExit
      exact congrArg Prod.fst hcontactExit
    exact ⟨fresh, path, hpath, hfreshSupport, hother⟩

/-- The no-change forward merge left by protected pair repair. -/
def ManufacturedReflector.FacingForwardMerge
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) : Prop :=
  ∃ before p x after contact fresh path,
    A.orientedRoute B.activatedState =
      before ++ (p, x) :: after ∧
    PhysicalTrace w (g, B.activatedState) before (p, contact) ∧
    PathGrooves B.toSupported.paths contact ∧
    p % 3 = 0 ∧
    B.activatedState (p / 3) ≠ B.baseState (p / 3) ∧
    contact (p / 3) = B.activatedState (p / 3) ∧
    path ∈ B.toSupported.paths ∧ (fresh, p) ∈ path ∧
    arrive contact p = (fresh, contact) ∧ fresh ≠ x ∧
    (p, fresh) ∈ B.orientedRoute contact

/-- A no-change forward merge can occur only in the reversed candy of a
nondegenerate flip reflector.  Stay reflectors and runways retain their stored
orientation in every selected route, so containing both `(fresh,p)` and
`(p,fresh)` would violate switch simplicity. -/
theorem ManufacturedReflector.FacingForwardMerge.flip_candy
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.FacingForwardMerge B) :
    ∃ (R : ManufacturedFlipReflector w e g)
        (before : List Passage) (p x : Nat) (after : List Passage)
        (contact : Tongues) (fresh : Nat),
      B = .flip R ∧
      A.orientedRoute B.activatedState =
        before ++ (p, x) :: after ∧
      PhysicalTrace w (g, B.activatedState) before (p, contact) ∧
      PathGrooves [R.runway, R.candy] contact ∧
      (fresh, p) ∈ R.candy ∧
      contact R.actionSwitch = bval R.secondArm := by
  obtain ⟨before, p, x, after, contact, fresh, path,
      hsplit, hprefix, hpaths, hp, _hchange, _hcontact,
      hpath, hold, harrive, hne, hforward⟩ := hmerge
  have hsameSwitch : p / 3 = fresh / 3 := by
    have hs := arrive_exit_switch contact p
    rw [harrive] at hs
    exact hs.symm
  have hpfresh : p ≠ fresh := by
    have hneLocal := arrive_exit_ne contact p
    rw [harrive] at hneLocal
    exact hneLocal.symm
  cases B with
  | stay R =>
      change path ∈ [R.runway, [(R.mouth, R.arm)]] at hpath
      change PathGrooves [R.runway, [(R.mouth, R.arm)]] contact at hpaths
      change (p, fresh) ∈
        (ManufacturedReflector.stay R).orientedRoute contact at hforward
      have holdRoute : (fresh, p) ∈
          (ManufacturedReflector.stay R).orientedRoute contact := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
        rcases hpath with rfl | rfl
        · simp [ManufacturedReflector.orientedRoute, hold]
        · simp only [List.mem_singleton] at hold
          simp [ManufacturedReflector.orientedRoute, hold]
      exact (SwitchSimple.not_both_orientations
        ((ManufacturedReflector.stay R).orientedRoute_simple contact)
        hforward holdRoute hsameSwitch hpfresh).elim
  | flip R =>
      change path ∈ [R.runway, R.candy] at hpath
      change PathGrooves [R.runway, R.candy] contact at hpaths
      change (p, fresh) ∈
        (ManufacturedReflector.flip R).orientedRoute contact at hforward
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
      rcases hpath with hrunway | hcandy
      · subst path
        have holdRoute : (fresh, p) ∈
            (ManufacturedReflector.flip R).orientedRoute contact := by
          by_cases hselected :
              contact R.actionSwitch = bval R.firstArm
          · simp [ManufacturedReflector.orientedRoute,
              hselected, hold]
          · simp [ManufacturedReflector.orientedRoute,
              hselected, hold]
        exact (SwitchSimple.not_both_orientations
          ((ManufacturedReflector.flip R).orientedRoute_simple contact)
          hforward holdRoute hsameSwitch hpfresh).elim
      · subst path
        have hnotFirst :
            contact R.actionSwitch ≠ bval R.firstArm := by
          intro hselected
          have holdRoute : (fresh, p) ∈
              (ManufacturedReflector.flip R).orientedRoute contact := by
            simp [ManufacturedReflector.orientedRoute,
              hselected, hold]
          exact SwitchSimple.not_both_orientations
            ((ManufacturedReflector.flip R).orientedRoute_simple contact)
            hforward holdRoute hsameSwitch hpfresh
        have hsecond :
            contact R.actionSwitch = bval R.secondArm := by
          rcases R.selected_arm contact with hfirst | hsecond
          · exact (hnotFirst hfirst).elim
          · exact hsecond
        exact ⟨R, before, p, x, after, contact, fresh,
          rfl, hsplit, hprefix, hpaths, hold, hsecond⟩

/-- The state-changing forward merge left by protected pair repair. -/
def ManufacturedReflector.ChangedForwardMerge
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) : Prop :=
  ∃ approach p x suffix u v path old oriented repaired,
    A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix ∧
    PhysicalTrace w (g, B.activatedState) approach (p, u) ∧
    PathGrooves B.toSupported.paths u ∧
    arrive u p = (x, v) ∧
    path ∈ B.toSupported.paths ∧ old ∈ path ∧
    passageSwitch old = p / 3 ∧
    v (p / 3) ≠ u (p / 3) ∧
    oriented ∈ B.orientedRoute u ∧
    arrive u oriented.2 = (oriented.1, u) ∧
    passageSwitch oriented = p / 3 ∧
    x = oriented.2 ∧
    arrive v oriented.1 = (oriented.2, repaired) ∧
    arrive repaired oriented.2 = (oriented.1, repaired)

/-- The completed-reflector forward-splice construction only used the
second reflector to supply a switch-simple route.  This is the same lemma
with that route supplied directly, so it applies to a partial second run. -/
theorem partial_first_forward_contact_active_lead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {route approach : List Passage} {p x : Nat}
    {suffix : List Passage} {startState u v : Tongues}
    {oriented : Passage} {repaired : Tongues}
    (hsplit : route = approach ++ (p, x) :: suffix)
    (hfullSimple : SwitchSimple route)
    (happroach :
      PhysicalTrace w (e, startState) approach (p, u))
    (hpaths : PathGrooves A.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3))
    (horiented : oriented ∈ A.orientedRoute u)
    (horientedGroove : arrive u oriented.2 = (oriented.1, u))
    (horientedSwitch : passageSwitch oriented = p / 3)
    (hforward : x = oriented.2)
    (hrepair : arrive v oriented.1 = (oriented.2, repaired))
    (hrestored :
      arrive repaired oriented.2 = (oriented.1, repaired)) :
    ∃ (entry mouth returnPort outside : Nat)
        (oldPrefix oldTail candy : List Passage),
      (entry, mouth) ∈ A.orientedRoute u ∧
      A.orientedRoute u = oldPrefix ++ (entry, mouth) :: oldTail ∧
      PhysicalTrace w (outside, u) oldTail (A.orientedFinish u, u) ∧
      PhysicalTrace w (e, u) approach (returnPort, u) ∧
      PassagesGrooved u approach ∧
      (∀ passage ∈ approach, passageSwitch passage ≠ mouth / 3) ∧
      entry % 3 ≠ 0 ∧ mouth % 3 = 0 ∧
      w.link mouth = some outside ∧
      entry ≠ returnPort ∧
      PassagesGrooved u ((mouth, entry) :: candy) ∧
      PhysicalTrace w (mouth, u) ((mouth, entry) :: candy)
        (returnPort, u) ∧
      arrive u returnPort = (mouth, flipAt u (mouth / 3)) ∧
      PathGrooves A.toSupported.paths u ∧
      PassagesGrooved u candy ∧
      (∀ passage ∈ candy, passageSwitch passage ≠ mouth / 3) ∧
      IsReflector w mouth outside (candy.length + 2)
        (fun state => PassagesGrooved state candy)
        (fun state => flipAt state (mouth / 3)) ∧
      stepN w (approach.length + 1) (e, startState) =
        some (outside, flipAt u (mouth / 3)) := by
  rcases oriented with ⟨a, s⟩
  simp only at horiented horientedGroove hforward hrepair hrestored
  subst x
  obtain ⟨hpBranch, hsEq, _hv⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hsStem : s % 3 = 0 := by
    rw [hsEq]
    omega
  have hsp : s / 3 = p / 3 := by
    rw [hsEq]
    omega
  have hsa : s / 3 = a / 3 := by
    have hswitch := arrive_exit_switch u s
    rw [horientedGroove] at hswitch
    exact hswitch.symm
  have haBranch : a % 3 ≠ 0 := by
    have haEq : branchPort (s / 3) (u (s / 3)) = a := by
      unfold arrive at horientedGroove
      rw [if_pos hsStem] at horientedGroove
      exact congrArg Prod.fst horientedGroove
    intro haStem
    cases hu : u (s / 3) <;>
      simp [branchPort, hu] at haEq <;> omega
  have hap : a ≠ p := by
    intro hEq
    subst p
    have holdForward := groove_forward horientedGroove
    rw [harrive] at holdForward
    have huv : v = u := congrArg Prod.snd holdForward
    apply hchanged
    rw [huv]
  obtain ⟨oldPrefix, oldTail, hrouteSplit⟩ :=
    List.append_of_mem horiented
  have hroute := A.orientedRoute_trace u hpaths
  have hrouteSimple := A.orientedRoute_simple u
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hOldPrefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hrouteSplit hrouteGrooved hrouteSimple
  have hOldPrefixGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hrouteSplit]
      exact List.mem_append_left _ hp)
  have hApproachSimple : SwitchSimple approach := by
    have hsimple := hfullSimple
    unfold SwitchSimple at hsimple ⊢
    rw [hsplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple hApproachSimple
  have hApproachForeign :
      ∀ passage ∈ approach, passageSwitch passage ≠ p / 3 := by
    have hsimple := hfullSimple
    unfold SwitchSimple at hsimple
    rw [hsplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (p, s)) (by simp)
    exact hne (by simpa [passageSwitch] using hEq)
  let candy := reversePassages oldPrefix ++ approach
  have hCandyGrooved : PassagesGrooved u candy := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · exact reversePassages_grooved
        hOldPrefixGrooved passage hold
    · exact hApproachGrooved passage hnew
  have hCandyForeign :
      ∀ passage ∈ candy, passageSwitch passage ≠ s / 3 := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · have hmapped : passageSwitch passage ∈
          (reversePassages oldPrefix).map passageSwitch :=
        List.mem_map.mpr ⟨passage, hold, rfl⟩
      have hmap := map_passageSwitch_reversePassages hOldPrefixData.1
      rw [hmap] at hmapped
      have horiginal : passageSwitch passage ∈
          oldPrefix.map passageSwitch := List.mem_reverse.mp hmapped
      obtain ⟨old, holdMem, holdEq⟩ := List.mem_map.mp horiginal
      intro hmouth
      apply hOldPrefixData.2 old holdMem
      exact holdEq.trans (hmouth.trans hsa)
    · intro hmouth
      apply hApproachForeign passage hnew
      exact hmouth.trans hsp
  have hback := physicalTrace_contact_retraces_prefix
    hOldPrefixData.1 hOldPrefixGrooved A.entryEdge horientedGroove
  have hforwardTrace := happroach.replay_grooved u hApproachGrooved
  have hsplice :
      PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy, List.append_assoc] using
      hback.append hforwardTrace
  have hSpliceGrooved : PassagesGrooved u ((s, a) :: candy) := by
    intro passage hpassage
    rcases List.mem_cons.mp hpassage with hhead | htail
    · simpa [hhead] using groove_forward horientedGroove
    · exact hCandyGrooved passage htail
  have hroute' := hroute
  rw [hrouteSplit] at hroute'
  obtain ⟨middle, hOldBefore, hOldAfter⟩ := hroute'.split_append
  have hMiddle : middle = (a, u) := by
    have h₁ := hOldBefore.sound
    have h₂ := hOldPrefixData.1.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hOldAfter with
  | @cons _ _ outside _ oldAfter _ _ hOldArrive hmouth hOldRest =>
      have hOldAfterState : oldAfter = u := by
        have hforwardOld := groove_forward horientedGroove
        rw [hOldArrive] at hforwardOld
        exact congrArg Prod.snd hforwardOld
      subst oldAfter
      have hflip : v = flipAt u (s / 3) := by
        have hv := changed_arrival_eq_flipAt harrive hchanged
        simpa [hsp] using hv
      have hone : stepN w 1 (p, u) = some (outside, v) := by
        simp [stepN, step, harrive, hmouth]
      have hreach :
          stepN w (approach.length + 1) (e, startState) =
            some (outside, flipAt u (s / 3)) := by
        rw [stepN_add, happroach.sound]
        simp only [Option.bind_some]
        rw [hone, hflip]
      have hcrossed : arrive u p =
          (s, flipAt u (s / 3)) := by
        rw [harrive, hflip]
      refine ⟨a, s, p, outside, oldPrefix, oldTail,
        candy, horiented, hrouteSplit, hOldRest,
        hforwardTrace, hApproachGrooved,
        (by
          intro passage hpassage
          simpa [hsp] using hApproachForeign passage hpassage),
        haBranch, hsStem, hmouth, hap, hSpliceGrooved,
        hsplice, hcrossed, hpaths, hCandyGrooved,
        hCandyForeign, ?_, hreach⟩
      exact stem_lobe_isReflector_foreign w candy
        hsStem haBranch hpBranch hsa hsp hap hCandyForeign
        hsplice.linked hsplice.last_link hmouth

/-- Trimming a manufactured witness does not require rebasing it to the
current tongue vector. Keep the original terminal states and core trace;
only the runway's initial state and incoming edge change. -/
theorem ManufacturedStayReflector.suffix_after_runway_passage
    {w : Wiring} {g e : Nat}
    (R : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {before : List Passage} {p x : Nat} {after : List Passage}
    {outside : Nat}
    (hsplit : R.runway = before ++ (p, x) :: after)
    (houtside : w.link x = some outside) :
    ∃ C : ManufacturedStayReflector w outside x,
      PathGrooves C.toSupported.paths state ∧
      (LocalAction.flip (p / 3)).Avoids C.toSupported.paths := by
  obtain ⟨base, htail⟩ :=
    (hsplit ▸ R.runwayTrace).suffix_after_passage houtside
  have hs := R.simple
  unfold SwitchSimple at hs
  rw [hsplit] at hs
  have hrest : ((p, x) :: (after ++ [(R.mouth, R.arm)])).map
      passageSwitch |>.Nodup := by
    exact (List.nodup_append.mp (by simpa [List.map_append,
      List.map_cons, List.append_assoc] using hs)).2.1
  have hparts := List.nodup_cons.mp hrest
  let C : ManufacturedStayReflector w outside x := {
    base := base, mouthState := R.mouthState, returnState := R.returnState
    runway := after, mouth := R.mouth, arm := R.arm
    runwayTrace := htail, coreTrace := R.coreTrace, simple := hparts.2
    stemEndpoint := R.stemEndpoint, selfLink := R.selfLink, entryEdge := houtside
  }
  have hgrooves := pathGrooves_pair.mp hpaths
  refine ⟨C, pathGrooves_pair.mpr ⟨?_, hgrooves.2⟩, ?_⟩
  · intro passage hp
    apply hgrooves.1 passage
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  · intro path hp passage hpassage heq
    apply hparts.1
    change path ∈ [after, [(R.mouth, R.arm)]] at hp
    have hmem : passage ∈ after ++ [(R.mouth, R.arm)] := by
      simpa only [List.mem_append] using
        (show passage ∈ after ∨ passage ∈ [(R.mouth, R.arm)] from by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact Or.inl hpassage
          · have := List.mem_singleton.mp hp
            subst path
            exact Or.inr hpassage)
    exact List.mem_map.mpr ⟨passage, hmem, heq⟩

/-- A flip reflector's runway suffix uses the original candy orientation.
Its stored construction state need not equal the later state in which its
support is grooved; the ordinary reflector law already handles that. -/
theorem ManufacturedFlipReflector.suffix_after_runway_passage
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {before : List Passage} {p x : Nat} {after : List Passage}
    {outside : Nat}
    (hsplit : R.runway = before ++ (p, x) :: after)
    (houtside : w.link x = some outside) :
    ∃ C : ManufacturedFlipReflector w outside x,
      C.actionSwitch = R.actionSwitch ∧
      p / 3 ≠ C.actionSwitch ∧
      PathGrooves C.toSupported.paths state ∧
      (LocalAction.flip (p / 3)).Avoids C.toSupported.paths := by
  obtain ⟨base, htail⟩ :=
    (hsplit ▸ R.runwayTrace).suffix_after_passage houtside
  have hs := R.simple
  unfold SwitchSimple at hs
  rw [hsplit] at hs
  have hrest : ((p, x) :: (after ++ (R.mouth, R.firstArm) :: R.candy)).map
      passageSwitch |>.Nodup := by
    exact (List.nodup_append.mp (by simpa [List.map_append,
      List.map_cons, List.append_assoc] using hs)).2.1
  have hparts := List.nodup_cons.mp hrest
  let C : ManufacturedFlipReflector w outside x := {
    base := base, mouthState := R.mouthState, returnState := R.returnState
    afterReturn := R.afterReturn, runway := after, candy := R.candy
    mouth := R.mouth, firstArm := R.firstArm, secondArm := R.secondArm
    runwayTrace := htail, candyTrace := R.candyTrace, simple := hparts.2
    crossed := R.crossed, arms_ne := R.arms_ne, entryEdge := houtside
  }
  have hgrooves := pathGrooves_pair.mp hpaths
  refine ⟨C, rfl, ?_, pathGrooves_pair.mpr ⟨?_, hgrooves.2⟩, ?_⟩
  · exact R.support_foreign R.runway (by simp) (p, x)
      (by rw [hsplit]; exact List.mem_append_right _ List.mem_cons_self)
  · intro passage hp
    apply hgrooves.1 passage
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  · intro path hp passage hpassage heq
    apply hparts.1
    change path ∈ [after, R.candy] at hp
    apply List.mem_map.mpr
    refine ⟨passage, ?_, heq⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact List.mem_append_left _ hpassage
    · have := List.mem_singleton.mp hp
      subst path
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hpassage)

/-- Reverse the arbitrary lobe in the tongue state obtained after its own
flip.  No simplicity is needed: linked grooved passages retrace physically,
and the original entry arm becomes the final trailing arm that restores the
base state. -/
theorem arbitrary_lobe_reverse_trace
    {w : Wiring} {mouth entry returnPort : Nat}
    {state : Tongues} {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3) :
    PhysicalTrace w (mouth, flipAt state (mouth / 3))
        ((mouth, returnPort) :: reversePassages candy)
        (entry, flipAt state (mouth / 3)) ∧
      PassagesGrooved (flipAt state (mouth / 3))
        ((mouth, returnPort) :: reversePassages candy) ∧
      arrive (flipAt state (mouth / 3)) entry = (mouth, state) := by
  have hheadGroove : arrive state entry = (mouth, state) :=
    hgrooved (mouth, entry) List.mem_cons_self
  have hrestore : arrive (flipAt state (mouth / 3)) entry =
      (mouth, state) := by
    have hrepair :=
      flipped_passage_forward_trailing hheadGroove hentryBranch
    simpa [hentrySwitch] using hrepair
  have hmouthForward : arrive (flipAt state (mouth / 3)) mouth =
      (returnPort, flipAt state (mouth / 3)) := by
    have hback := arrive_back state returnPort
    rw [hcrossed] at hback
    exact hback
  have hreturnGroove :
      arrive (flipAt state (mouth / 3)) returnPort =
        (mouth, flipAt state (mouth / 3)) :=
    groove_forward hmouthForward
  have hCandyGrooved : PassagesGrooved state candy := by
    intro passage hpassage
    exact hgrooved passage (List.mem_cons_of_mem _ hpassage)
  have hCandyFlip :
      PassagesGrooved (flipAt state (mouth / 3)) candy :=
    grooved_after_flip_other hCandyGrooved hCandyForeign
  have hReverseGrooved :
      PassagesGrooved (flipAt state (mouth / 3))
        (reversePassages candy) := by
    intro passage hpassage
    exact reversePassages_grooved hCandyFlip passage hpassage
  have hfullReverseGrooved :
      PassagesGrooved (flipAt state (mouth / 3))
        ((mouth, returnPort) :: reversePassages candy) := by
    intro passage hpassage
    rcases List.mem_cons.mp hpassage with hhead | htail
    · simpa [hhead] using hreturnGroove
    · exact hReverseGrooved passage htail
  have hreverseTrace :
      PhysicalTrace w (mouth, flipAt state (mouth / 3))
        ((mouth, returnPort) :: reversePassages candy)
        (entry, flipAt state (mouth / 3)) := by
    cases htrace with
    | cons _ hentry tail =>
        exact physicalTrace_contact_retraces_prefix tail hCandyFlip hentry hmouthForward
  exact ⟨hreverseTrace, hfullReverseGrooved, hrestore⟩

theorem ManufacturedFlipReflector.nonrunway_oriented_branch_entry_is_candy
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues) {entry mouth : Nat}
    (horiented : (entry, mouth) ∈
      (ManufacturedReflector.flip R).orientedRoute state)
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0) :
    ∃ old ∈ R.candy,
      (entry, mouth) = old ∨
        (entry, mouth) = (old.2, old.1) := by
  by_cases hselected :
      state R.actionSwitch = bval R.firstArm
  · simp only [ManufacturedReflector.orientedRoute, hselected,
      if_pos] at horiented
    rcases List.mem_append.mp horiented with hrunway | hcore
    · exact (hnotRunway hrunway).elim
    · rcases List.mem_cons.mp hcore with hhead | hcandy
      · have hentryEq : entry = R.mouth :=
          congrArg Prod.fst hhead
        apply (hentryBranch (by
          rw [hentryEq]
          exact R.mouth_is_stem)).elim
      · exact ⟨(entry, mouth), hcandy, Or.inl rfl⟩
  · simp only [ManufacturedReflector.orientedRoute, hselected,
      if_false] at horiented
    rcases List.mem_append.mp horiented with hrunway | hcore
    · exact (hnotRunway hrunway).elim
    · rcases List.mem_cons.mp hcore with hhead | hreverse
      · have hentryEq : entry = R.mouth :=
          congrArg Prod.fst hhead
        apply (hentryBranch (by
          rw [hentryEq]
          exact R.mouth_is_stem)).elim
      · obtain ⟨old, hold, hEq⟩ :=
          source_of_mem_reversePassages hreverse
        exact ⟨old, hold, Or.inr hEq⟩

/-- Either orientation of a recorded candy passage is disjoint from the
old reflector's private mouth switch.  This packages the endpoint-switch
transport needed when a later splice cuts the selected candy route. -/
theorem ManufacturedFlipReflector.candy_entry_foreign_action
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    {entry mouth : Nat} {old : Passage}
    (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1)) :
    entry / 3 ≠ R.actionSwitch := by
  have holdForeign : passageSwitch old ≠ R.actionSwitch :=
    R.support_foreign R.candy (by simp) old hold
  have holdExitSwitch : old.2 / 3 = passageSwitch old :=
    R.candyTrace.passage_exit_switch old
      (List.mem_cons_of_mem _ hold)
  rcases horientation with hforward | hreverse
  · have hentryEq : entry = old.1 :=
      congrArg Prod.fst hforward
    simpa [passageSwitch, hentryEq] using holdForeign
  · have hentryEq : entry = old.2 :=
      congrArg Prod.fst hreverse
    intro hEq
    apply holdForeign
    rw [← holdExitSwitch, ← hentryEq]
    exact hEq

/-- A fresh approach to a strict candy splice cannot meet the old reflector
mouth facing-first.  From that mouth, determinism makes the fresh route and
the old selected candy route coincide until their first visit to the splice
switch.  Both avoid that switch internally, so the avoided-switch endpoint
lemma forces the two arrival arms to be equal, contradicting the splice. -/
theorem ManufacturedFlipReflector.facing_approach_to_candy_splice_impossible
    {w : Wiring} {g e entry mouth returnPort : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state)
    {oldPrefix oldTail approach : List Passage}
    (hrouteSplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (_hentryBranch : entry % 3 ≠ 0)
    (happroach : PhysicalTrace w (g, state) approach
      (returnPort, state))
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (harms : entry ≠ returnPort)
    {target : Passage}
    (htargetMem : target ∈ approach)
    (htargetSwitch : passageSwitch target = R.actionSwitch)
    (htargetStem : target.1 % 3 = 0) : False := by
  have htargetRoute : (entry, mouth) ∈
      (ManufacturedReflector.flip R).orientedRoute state := by
    rw [hrouteSplit]
    exact List.mem_append_right oldPrefix List.mem_cons_self
  have hroute :=
    (ManufacturedReflector.flip R).orientedRoute_trace state hpaths
  have hrouteSimple :=
    (ManufacturedReflector.flip R).orientedRoute_simple state
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hentryGrooved : arrive state entry = (mouth, state) :=
    groove_forward (hrouteGrooved (entry, mouth) htargetRoute)
  have hentryNew : entry / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state entry
    rw [hentryGrooved] at hs
    exact hs.symm
  have hreturnNew : returnPort / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state returnPort
    rw [hcrossed] at hs
    exact hs.symm

  obtain ⟨freshBefore, freshAfter, hfreshSplit⟩ :=
    List.append_of_mem htargetMem
  have hfreshTrace := happroach
  rw [hfreshSplit] at hfreshTrace
  obtain ⟨freshMiddle, hfreshBeforeRaw, hfreshRest⟩ :=
    hfreshTrace.split_append
  have hfreshMiddlePort : freshMiddle.1 = target.1 :=
    hfreshRest.head_arrive.1
  have hfreshBeforeGrooved : PassagesGrooved state freshBefore := by
    intro passage hpassage
    exact happroachGrooved passage (by
      rw [hfreshSplit]
      exact List.mem_append_left _ hpassage)
  have hfreshBefore : PhysicalTrace w (g, state) freshBefore
      (target.1, state) := by
    have hreplay :=
      hfreshBeforeRaw.replay_grooved state hfreshBeforeGrooved
    simpa [hfreshMiddlePort] using hreplay
  have hfreshMiddleEq : freshMiddle = (target.1, state) := by
    exact Option.some.inj
      (hfreshBeforeRaw.sound.symm.trans hfreshBefore.sound)
  subst freshMiddle
  rcases target with ⟨p, x⟩
  simp only [passageSwitch] at htargetSwitch
  have hpMouth : p = R.mouth := by
    have hm := R.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at htargetSwitch
    omega
  subst p
  have hfreshForeign : ∀ passage ∈
      (R.mouth, x) :: freshAfter,
      passageSwitch passage ≠ mouth / 3 := by
    intro passage hpassage
    apply happroachForeignNew passage
    rw [hfreshSplit]
    exact List.mem_append_right freshBefore hpassage

  have hOldSegment : ∃ segment,
      PhysicalTrace w (R.mouth, state) segment (entry, state) ∧
      (∀ passage ∈ segment, passageSwitch passage ≠ mouth / 3) := by
    have hcore : ∃ core, (ManufacturedReflector.flip R).orientedRoute state =
        R.runway ++ core := by
      simp only [ManufacturedReflector.orientedRoute]
      split <;> exact ⟨_, rfl⟩
    obtain ⟨core, hcore⟩ := hcore
    have hwhole : PhysicalTrace w (e, state) (R.runway ++ core)
        ((ManufacturedReflector.flip R).orientedFinish state, state) := hcore ▸ hroute
    obtain ⟨mid, hprefix, htail⟩ := hwhole.split_append
    have hmid : mid = (R.mouth, state) :=
      Option.some.inj (hprefix.sound.symm.trans
        (R.runway_trace state (pathGrooves_pair.mp hpaths).1).sound)
    subst mid
    have hsimple : SwitchSimple core := by
      have hs := hrouteSimple
      rw [hcore] at hs
      exact (List.nodup_append.mp (by simpa [SwitchSimple] using hs)).2.1
    obtain ⟨before, hsplit⟩ :=
      split_after_prefix_of_not_mem (hcore.symm.trans hrouteSplit) hnotRunway
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      htail hsplit (htail.grooved_of_switchSimple hsimple) hsimple
    exact ⟨before, hprefixData.1, fun passage hp heq =>
      hprefixData.2 passage hp (heq.trans hentryNew.symm)⟩
  obtain ⟨oldSegment, holdSegment, holdForeign⟩ := hOldSegment
  have hendpoints :=
    physicalTrace_endpoints_eq_before_avoided_switch
      holdSegment hfreshRest hentryNew hreturnNew
      holdForeign hfreshForeign
  apply harms
  exact congrArg Prod.fst hendpoints

/-- Once a selected-route split occurs strictly inside the candy, every
later selected passage is foreign to the old reflector's mouth action. -/
theorem ManufacturedFlipReflector.candy_tail_foreign_action
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    {oldPrefix oldTail : List Passage} {entry mouth : Nat}
    (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
      oldPrefix ++ (entry, mouth) :: oldTail)
    (hnotRunway : (entry, mouth) ∉ R.runway)
    (hentryBranch : entry % 3 ≠ 0) :
    ∀ passage ∈ oldTail,
      passageSwitch passage ≠ R.actionSwitch := by
  have hcore : ∃ arm candy,
      (ManufacturedReflector.flip R).orientedRoute state =
        (R.runway ++ [(R.mouth, arm)]) ++ candy ∧
      (∀ passage ∈ candy, passageSwitch passage ≠ R.actionSwitch) := by
    by_cases hselected : state R.actionSwitch = bval R.firstArm
    · exact ⟨R.firstArm, R.candy,
        by simp [ManufacturedReflector.orientedRoute, hselected, List.append_assoc],
        R.support_foreign R.candy (by simp)⟩
    · refine ⟨R.secondArm, reversePassages R.candy,
        by simp [ManufacturedReflector.orientedRoute, hselected, List.append_assoc], ?_⟩
      intro passage hp
      obtain ⟨old, hold, rfl⟩ := source_of_mem_reversePassages hp
      rw [show passageSwitch (old.2, old.1) = passageSwitch old from
        R.candyTrace.passage_exit_switch old (List.mem_cons_of_mem _ hold)]
      exact R.support_foreign R.candy (by simp) old hold
  obtain ⟨arm, candy, hcore, hforeign⟩ := hcore
  have habsent : (entry, mouth) ∉ R.runway ++ [(R.mouth, arm)] := by
    intro hm
    rcases List.mem_append.mp hm with hrunway | hhead
    · exact hnotRunway hrunway
    · have heq : entry = R.mouth := congrArg Prod.fst (List.mem_singleton.mp hhead)
      exact hentryBranch (heq.symm ▸ R.mouth_is_stem)
  obtain ⟨middle, hcandy⟩ :=
    split_after_prefix_of_not_mem (hcore.symm.trans hsplit) habsent
  intro passage hp
  apply hforeign passage
  rw [hcandy]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)

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


/-- After the selected one-way route of a flip reflector reaches its far
candy arm, one trailing passage applies the reflector's action and the train
retraces the runway to the far boundary.  The exact reverse-runway trace is
retained for later disjointness arguments. -/
theorem ManufacturedFlipReflector.oriented_return_trace
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves R.toSupported.paths state) :
    PhysicalTrace w
      ((ManufacturedReflector.flip R).orientedFinish state, state)
      (((ManufacturedReflector.flip R).orientedFinish state,
          R.mouth) :: reversePassages R.runway)
      (g, flipAt state R.actionSwitch) := by
  change PathGrooves [R.runway, R.candy] state at hpaths
  have hrunwayGrooved := (pathGrooves_pair.mp hpaths).1
  have hrunwayFlip :
      PassagesGrooved (flipAt state R.actionSwitch) R.runway := by
    apply grooved_after_flip_other hrunwayGrooved
    intro passage hpassage
    exact R.support_foreign R.runway (by simp) passage hpassage
  exact physicalTrace_contact_retraces_prefix R.runwayTrace hrunwayFlip
    R.entryEdge (R.oriented_finish_arrive state)


section
variable {w : Wiring} {g e outside : Nat}
  (R : ManufacturedFlipReflector w e g)
  (state : Tongues)
  (hpaths : PathGrooves R.toSupported.paths state)
  {oldPrefix oldTail : List Passage} {entry mouth : Nat}
  (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
    oldPrefix ++ (entry, mouth) :: oldTail)
  (htail : PhysicalTrace w (outside, state) oldTail
    ((ManufacturedReflector.flip R).orientedFinish state, state))
  (hnotRunway : (entry, mouth) ∉ R.runway)
include w g e outside R state hpaths oldPrefix oldTail entry mouth hsplit htail hnotRunway

/-- In the candy residual, the untouched selected-route tail followed by the
trailing old-mouth return and reverse runway completes from the splice's
outside endpoint to the old boundary.  The entire completion is disjoint
from the splice switch. -/
theorem ManufacturedFlipReflector.candy_completion_foreign
    {old : Passage} (hold : old ∈ R.candy)
    (horientation : (entry, mouth) = old ∨
      (entry, mouth) = (old.2, old.1)) :
    let completion := oldTail ++
      (((ManufacturedReflector.flip R).orientedFinish state,
        R.mouth) :: reversePassages R.runway)
    PhysicalTrace w (outside, state) completion
        (g, flipAt state R.actionSwitch) ∧
      (∀ passage ∈ completion,
        passageSwitch passage ≠ entry / 3) := by
  let finish := (ManufacturedReflector.flip R).orientedFinish state
  let completion := oldTail ++
    ((finish, R.mouth) :: reversePassages R.runway)
  have hreturn := R.oriented_return_trace state hpaths
  have htrace : PhysicalTrace w (outside, state) completion
      (g, flipAt state R.actionSwitch) := by
    dsimp [completion, finish]
    exact htail.append hreturn
  have hsimple :=
    (ManufacturedReflector.flip R).orientedRoute_simple state
  have htargetMem : (entry, mouth) ∈
      (ManufacturedReflector.flip R).orientedRoute state := by
    rw [hsplit]
    exact List.mem_append_right oldPrefix List.mem_cons_self
  have hs := hsimple
  unfold SwitchSimple at hs
  rw [hsplit] at hs
  simp only [List.map_append, List.map_cons] at hs
  have hs' :
      (oldPrefix.map passageSwitch ++
        passageSwitch (entry, mouth) ::
          oldTail.map passageSwitch).Nodup := by
    simpa [List.append_assoc] using hs
  have htargetNotTail : passageSwitch (entry, mouth) ∉
      oldTail.map passageSwitch :=
    (List.nodup_cons.mp (List.nodup_append.mp hs').2.1).1
  have htailForeign : ∀ passage ∈ oldTail,
      passageSwitch passage ≠ entry / 3 := by
    intro passage hpassage hEq
    apply htargetNotTail
    apply List.mem_map.mpr
    refine ⟨passage, hpassage, ?_⟩
    simpa [passageSwitch] using hEq
  have holdForeign : passageSwitch old ≠ R.actionSwitch :=
    R.support_foreign R.candy (by simp) old hold
  have holdExitSwitch : old.2 / 3 = passageSwitch old :=
    R.candyTrace.passage_exit_switch old
      (List.mem_cons_of_mem _ hold)
  have hnewOldForeign : entry / 3 ≠ R.actionSwitch := by
    rcases horientation with hforward | hreverse
    · have hentryEq : entry = old.1 :=
        congrArg Prod.fst hforward
      have hkey : entry / 3 = passageSwitch old := by
        rw [hentryEq]
        rfl
      exact fun hEq => holdForeign (hkey.symm.trans hEq)
    · have hentryEq : entry = old.2 :=
        congrArg Prod.fst hreverse
      intro hEq
      apply holdForeign
      rw [← holdExitSwitch, ← hentryEq]
      exact hEq
  have hfinishSwitch : finish / 3 = R.actionSwitch := by
    dsimp [finish]
    by_cases hselected :
        state R.actionSwitch = bval R.firstArm
    · simp [ManufacturedReflector.orientedFinish, hselected,
        R.secondArm_switch]
    · simp [ManufacturedReflector.orientedFinish, hselected,
        R.firstArm_switch]
  have hreturnForeign : passageSwitch (finish, R.mouth) ≠
      entry / 3 := by
    simp only [passageSwitch]
    rw [hfinishSwitch]
    exact Ne.symm hnewOldForeign
  have hreverseForeign : ∀ passage ∈ reversePassages R.runway,
      passageSwitch passage ≠ entry / 3 := by
    intro passage hpassage hEq
    have hmap := map_passageSwitch_reversePassages R.runwayTrace
    have hreverseKey : passageSwitch passage ∈
        (reversePassages R.runway).map passageSwitch :=
      List.mem_map.mpr ⟨passage, hpassage, rfl⟩
    rw [hmap] at hreverseKey
    have horiginalKey : passageSwitch passage ∈
        R.runway.map passageSwitch :=
      List.mem_reverse.mp hreverseKey
    obtain ⟨original, horiginal, hkey⟩ :=
      List.mem_map.mp horiginalKey
    have horiginalRoute : original ∈
        (ManufacturedReflector.flip R).orientedRoute state := by
      simp only [ManufacturedReflector.orientedRoute]
      split <;> exact List.mem_append_left _ horiginal
    have hsame : passageSwitch original =
        passageSwitch (entry, mouth) := by
      calc
        passageSwitch original = passageSwitch passage := hkey
        _ = entry / 3 := hEq
        _ = passageSwitch (entry, mouth) := by
          simp [passageSwitch]
    have hequal := hsimple.passage_eq_of_mem horiginalRoute
      htargetMem hsame
    apply hnotRunway
    rw [← hequal]
    exact horiginal
  refine ⟨htrace, ?_⟩
  intro passage hpassage
  change passage ∈ completion at hpassage
  rcases List.mem_append.mp hpassage with htailMem | hrestMem
  · exact htailForeign passage htailMem
  · rcases List.mem_cons.mp hrestMem with hreturnMem | hreverseMem
    · simpa [hreturnMem] using hreturnForeign
    · exact hreverseForeign passage hreverseMem

/-- Once the old action tongue has been pinned to the selected return arm,
the same candy completion is idempotent: the candy tail carries that bit,
the return passage is now grooved, and the reverse runway leaves it fixed. -/
theorem ManufacturedFlipReflector.candy_completion_latched
    (hentryBranch : entry % 3 ≠ 0) :
    let completion := oldTail ++
      (((ManufacturedReflector.flip R).orientedFinish state,
        R.mouth) :: reversePassages R.runway)
    PhysicalTrace w (outside, flipAt state R.actionSwitch)
      completion (g, flipAt state R.actionSwitch) := by
  let finish := (ManufacturedReflector.flip R).orientedFinish state
  let completion := oldTail ++
    ((finish, R.mouth) :: reversePassages R.runway)
  have htailForeign := R.candy_tail_foreign_action state
    hsplit hnotRunway hentryBranch
  have htailLatched := htail.flip_unvisited htailForeign
  have hreturn := R.oriented_return_trace state hpaths
  change PhysicalTrace w (finish, state)
    ((finish, R.mouth) :: reversePassages R.runway)
    (g, flipAt state R.actionSwitch) at hreturn
  cases hreturn with
  | @cons _ _ next _ after _ _ harrive hlink tail =>
      have hafter : after = flipAt state R.actionSwitch := by
        have hlocal := R.oriented_finish_arrive state
        rw [harrive] at hlocal
        exact congrArg Prod.snd hlocal
      subst after
      have hback := arrive_back state finish
      rw [R.oriented_finish_arrive state] at hback
      have hlatched : arrive (flipAt state R.actionSwitch) finish =
          (R.mouth, flipAt state R.actionSwitch) :=
        groove_forward hback
      have hreturnLatched : PhysicalTrace w
          (finish, flipAt state R.actionSwitch)
          ((finish, R.mouth) :: reversePassages R.runway)
          (g, flipAt state R.actionSwitch) :=
        PhysicalTrace.cons hlatched hlink tail
      dsimp [completion, finish]
      exact htailLatched.append hreturnLatched

end

section
variable {w : Wiring} {g e outside entry mouth returnPort : Nat}
  (R : ManufacturedFlipReflector w e g)
  (state : Tongues)
  (hpaths : PathGrooves R.toSupported.paths state)
  {oldPrefix oldTail approach : List Passage}
  (hsplit : (ManufacturedReflector.flip R).orientedRoute state =
    oldPrefix ++ (entry, mouth) :: oldTail)
  (htail : PhysicalTrace w (outside, state) oldTail
    ((ManufacturedReflector.flip R).orientedFinish state, state))
  (hnotRunway : (entry, mouth) ∉ R.runway)
  (hentryBranch : entry % 3 ≠ 0)
  {old : Passage} (hold : old ∈ R.candy)
  (horientation : (entry, mouth) = old ∨
    (entry, mouth) = (old.2, old.1))
  (hentryGrooved : arrive state entry = (mouth, state))
  (happroach : PhysicalTrace w (g, state) approach
    (returnPort, state))
include w g e outside entry mouth returnPort R state hpaths oldPrefix oldTail approach hsplit htail
  hnotRunway hentryBranch old hold horientation hentryGrooved happroach

/-- If the fresh approach avoids the old reflector action, a candy splice
settles after one macro traversal.  The first completion latches the old
action; thereafter both the old completion and the fresh approach/contact
carry the two latched tongues unchanged, giving an explicit raw period. -/
theorem manufactured_flip_candy_splice_periodic_of_approach_foreign
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (happroachForeignOld : ∀ passage ∈ approach,
      passageSwitch passage ≠ R.actionSwitch)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside) :
    EventuallyPeriodic w
        (outside, flipAt state (mouth / 3)) ∧
      ∃ settled,
        stepN w (oldTail.length + R.runway.length +
            approach.length + 2)
          (outside, flipAt state (mouth / 3)) = some settled ∧
        stepN w (oldTail.length + R.runway.length +
            approach.length + 2) settled = some settled := by
  let finish := (ManufacturedReflector.flip R).orientedFinish state
  let completion := oldTail ++
    ((finish, R.mouth) :: reversePassages R.runway)
  have hentryNew : entry / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state entry
    rw [hentryGrooved] at hs
    exact hs.symm
  have hentryOld : entry / 3 ≠ R.actionSwitch :=
    R.candy_entry_foreign_action hold horientation
  have hnewOld : mouth / 3 ≠ R.actionSwitch := by
    intro hEq
    exact hentryOld (hentryNew.trans hEq)
  have hreturnNew : returnPort / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state returnPort
    rw [hcrossed] at hs
    exact hs.symm
  have hreturnOld : returnPort / 3 ≠ R.actionSwitch := by
    rw [hreturnNew]
    exact hnewOld

  have hcompletionData := R.candy_completion_foreign state hpaths
    hsplit htail hnotRunway hold horientation
  change PhysicalTrace w (outside, state) completion
      (g, flipAt state R.actionSwitch) ∧
    (∀ passage ∈ completion,
      passageSwitch passage ≠ entry / 3) at hcompletionData
  obtain ⟨hcompletion, hcompletionForeignEntry⟩ := hcompletionData
  have hcompletionForeignNew : ∀ passage ∈ completion,
      passageSwitch passage ≠ mouth / 3 := by
    intro passage hpassage hEq
    exact hcompletionForeignEntry passage hpassage
      (hEq.trans hentryNew.symm)
  have hcomm :
      flipAt (flipAt state R.actionSwitch) (mouth / 3) =
        flipAt (flipAt state (mouth / 3)) R.actionSwitch :=
    flipAt_comm (Ne.symm hnewOld)
  have hcompletionNew :=
    hcompletion.flip_unvisited hcompletionForeignNew
  rw [hcomm] at hcompletionNew

  have hlatched := R.candy_completion_latched state hpaths
    hsplit htail hnotRunway hentryBranch
  change PhysicalTrace w (outside, flipAt state R.actionSwitch)
      completion (g, flipAt state R.actionSwitch) at hlatched
  have hlatchedBoth :=
    hlatched.flip_unvisited hcompletionForeignNew
  rw [hcomm] at hlatchedBoth

  have happroachNew :=
    happroach.flip_unvisited happroachForeignNew
  have happroachBoth :=
    happroachNew.flip_unvisited happroachForeignOld
  have hback := arrive_back state returnPort
  rw [hcrossed] at hback
  have hcontactNew :
      arrive (flipAt state (mouth / 3)) returnPort =
        (mouth, flipAt state (mouth / 3)) :=
    groove_forward hback
  have hcontactBoth := arrive_flip_other hcontactNew hreturnOld
  have hcontactTrace : PhysicalTrace w
      (returnPort,
        flipAt (flipAt state (mouth / 3)) R.actionSwitch)
      [(returnPort, mouth)]
      (outside,
        flipAt (flipAt state (mouth / 3)) R.actionSwitch) :=
    PhysicalTrace.cons hcontactBoth hmouthLink (PhysicalTrace.nil _)

  have hleadTrace :=
    (hcompletionNew.append happroachBoth).append hcontactTrace
  have hperiodTrace :=
    (hlatchedBoth.append happroachBoth).append hcontactTrace
  let loop := (completion ++ approach) ++ [(returnPort, mouth)]
  let settled :=
    (outside, flipAt (flipAt state (mouth / 3)) R.actionSwitch)
  have hpositive : 0 < loop.length := by
    dsimp [loop]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hleadLoop : stepN w loop.length
      (outside, flipAt state (mouth / 3)) = some settled := by
    simpa [loop, settled] using hleadTrace.sound
  have hperiodLoop : stepN w loop.length settled = some settled := by
    simpa [loop, settled] using hperiodTrace.sound
  have hloopLen : loop.length =
      oldTail.length + R.runway.length + approach.length + 2 := by
    dsimp [loop, completion]
    simp only [List.length_append, List.length_cons, List.length_nil,
      reversePassages_length]
    omega
  constructor
  · exact ⟨loop.length, loop.length, settled, hpositive,
      hleadLoop, hperiodLoop⟩
  · refine ⟨settled, ?_, ?_⟩
    · rw [← hloopLen]
      exact hleadLoop
    · rw [← hloopLen]
      exact hperiodLoop

/-- If the fresh approach does meet the old reflector action, its first such
contact cannot be facing by `facing_approach_to_candy_splice_impossible`.
It is therefore trailing: from the post-splice state it repairs the old
action, follows the deterministic suffix, and returns to that same state.
Prepending the old candy completion gives an explicit positive period. -/
theorem manufactured_flip_candy_splice_periodic_of_approach_contact
    (happroachGrooved : PassagesGrooved state approach)
    (happroachForeignNew : ∀ passage ∈ approach,
      passageSwitch passage ≠ mouth / 3)
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    (harms : entry ≠ returnPort)
    (hcontact : ∃ passage ∈ approach,
      passageSwitch passage = R.actionSwitch) :
    EventuallyPeriodic w
        (outside, flipAt state (mouth / 3)) ∧
      stepN w (oldTail.length + R.runway.length +
          approach.length + 2)
        (outside, flipAt state (mouth / 3)) =
          some (outside, flipAt state (mouth / 3)) := by
  let finish := (ManufacturedReflector.flip R).orientedFinish state
  let completion := oldTail ++
    ((finish, R.mouth) :: reversePassages R.runway)
  let newState := flipAt state (mouth / 3)
  have hentryNew : entry / 3 = mouth / 3 := by
    have hs := arrive_exit_switch state entry
    rw [hentryGrooved] at hs
    exact hs.symm
  have hentryOld : entry / 3 ≠ R.actionSwitch :=
    R.candy_entry_foreign_action hold horientation
  have hnewOld : mouth / 3 ≠ R.actionSwitch := by
    intro hEq
    exact hentryOld (hentryNew.trans hEq)

  have hcompletionData := R.candy_completion_foreign state hpaths
    hsplit htail hnotRunway hold horientation
  change PhysicalTrace w (outside, state) completion
      (g, flipAt state R.actionSwitch) ∧
    (∀ passage ∈ completion,
      passageSwitch passage ≠ entry / 3) at hcompletionData
  obtain ⟨hcompletion, hcompletionForeignEntry⟩ := hcompletionData
  have hcompletionForeignNew : ∀ passage ∈ completion,
      passageSwitch passage ≠ mouth / 3 := by
    intro passage hpassage hEq
    exact hcompletionForeignEntry passage hpassage
      (hEq.trans hentryNew.symm)
  have hcompletionNew :=
    hcompletion.flip_unvisited hcompletionForeignNew
  have hcomm :
      flipAt (flipAt state R.actionSwitch) (mouth / 3) =
        flipAt newState R.actionSwitch := by
    dsimp [newState]
    exact flipAt_comm (Ne.symm hnewOld)
  rw [hcomm] at hcompletionNew

  have happroachNew :=
    happroach.flip_unvisited happroachForeignNew
  change PhysicalTrace w (g, newState) approach
    (returnPort, newState) at happroachNew
  have happroachGroovedNew : PassagesGrooved newState approach := by
    dsimp [newState]
    exact grooved_after_flip_other happroachGrooved
      happroachForeignNew
  have hback := arrive_back state returnPort
  rw [hcrossed] at hback
  have hcontactNew : arrive newState returnPort =
      (mouth, newState) := by
    dsimp [newState]
    exact groove_forward hback
  have hcontactTraceNew : PhysicalTrace w
      (returnPort, newState) [(returnPort, mouth)]
      (outside, newState) :=
    PhysicalTrace.cons hcontactNew hmouthLink (PhysicalTrace.nil _)
  have hnormalTrace := happroachNew.append hcontactTraceNew
  have hnormal : stepN w (approach.length + 1)
      (g, newState) = some (outside, newState) := by
    simpa using hnormalTrace.sound

  obtain ⟨before, target, after, happSplit, hbeforeForeignOld,
      htargetSwitch⟩ :=
    exists_first_satisfying_split
      (fun passage => passageSwitch passage = R.actionSwitch)
      approach hcontact
  have htargetMem : target ∈ approach := by
    rw [happSplit]
    exact List.mem_append_right before List.mem_cons_self
  have happroachNew' := happroachNew
  rw [happSplit] at happroachNew'
  obtain ⟨middle, hbeforeRaw, hrest⟩ :=
    happroachNew'.split_append
  have hmiddlePort : middle.1 = target.1 :=
    hrest.head_arrive.1
  have hbeforeGrooved : PassagesGrooved newState before := by
    intro passage hpassage
    exact happroachGroovedNew passage (by
      rw [happSplit]
      exact List.mem_append_left _ hpassage)
  have hprefix : PhysicalTrace w (g, newState) before
      (target.1, newState) := by
    have hreplay := hbeforeRaw.replay_grooved newState hbeforeGrooved
    simpa [hmiddlePort] using hreplay
  have hmiddleEq : middle = (target.1, newState) := by
    exact Option.some.inj
      (hbeforeRaw.sound.symm.trans hprefix.sound)
  subst middle
  have hstem := happroach.passage_stem_endpoint target htargetMem
  rcases target with ⟨p, x⟩
  simp only [passageSwitch] at htargetSwitch
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  have hpNotStem : p ≠ 3 * (p / 3) := by
    intro hpStem
    apply R.facing_approach_to_candy_splice_impossible state hpaths
      hsplit hnotRunway hentryBranch happroach happroachGrooved
      happroachForeignNew hcrossed harms
      (target := (p, x)) htargetMem
    · simpa [passageSwitch] using htargetSwitch
    · omega
  have hxStem : x = 3 * (p / 3) := hstem.resolve_left hpNotStem
  have hxMouth : x = R.mouth := by
    have hm := R.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch at htargetSwitch
    omega
  clear hxStem
  subst x
  have htargetGroove : arrive newState R.mouth =
      (p, newState) :=
    happroachGroovedNew (p, R.mouth) htargetMem
  have hforward : arrive newState p = (R.mouth, newState) :=
    groove_forward htargetGroove
  have hpbranch : p % 3 ≠ 0 := by
    intro hpmod
    have hpEq : p = 3 * (p / 3) := by omega
    exact hpNotStem hpEq
  obtain ⟨q, hlink⟩ : ∃ q, w.link R.mouth = some q := by
    cases after with
    | nil =>
        exact ⟨returnPort, by
          simpa [lastPassageExit] using hrest.last_link⟩
    | cons passage rest =>
        rcases passage with ⟨q, y⟩
        exact ⟨q, hrest.linked.1⟩
  have hone : PhysicalTrace w (p, newState) [(p, R.mouth)]
      (q, newState) :=
    PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
  have hlead := hprefix.append hone
  let tailSteps := after.length + 1
  have happLength : approach.length =
      before.length + 1 + after.length := by
    have hlen := congrArg List.length happSplit
    simp only [List.length_append, List.length_cons] at hlen
    omega
  have htotal : approach.length + 1 =
      before.length + 1 + tailSteps := by
    dsimp [tailSteps]
    omega
  have hsuffix : stepN w tailSteps (q, newState) =
      some (outside, newState) := by
    apply suffix_after_physical_prefix hlead
    · simpa using htotal
    · exact hnormal
  have hfault : stepN w (before.length + 1 + tailSteps)
      (g, flipAt newState R.actionSwitch) =
        some (outside, newState) :=
    flipped_prefix_trailing_then hprefix hbeforeForeignOld
      htargetSwitch hpbranch hforward hlink hsuffix
  have hperiod : stepN w
      (completion.length + (before.length + 1 + tailSteps))
      (outside, newState) = some (outside, newState) := by
    rw [stepN_add, hcompletionNew.sound]
    exact hfault
  have hpositive : 0 < completion.length +
      (before.length + 1 + tailSteps) := by
    omega
  have hcycleLen : completion.length +
      (before.length + 1 + tailSteps) =
        oldTail.length + R.runway.length + approach.length + 2 := by
    dsimp [completion]
    simp only [List.length_append, List.length_cons,
      reversePassages_length]
    omega
  constructor
  · exact eventuallyPeriodic_of_period hpositive hperiod
  · rw [← hcycleLen]
    exact hperiod

end

end GeneralN
