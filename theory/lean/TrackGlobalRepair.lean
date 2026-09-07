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
  | nil => simp at hexists
  | cons head tail ih =>
      by_cases hp : P head
      · exact ⟨[], head, tail, rfl, by simp, hp⟩
      · obtain ⟨before, x, after, hs, hb, hx⟩ := ih (by simpa [hp] using hexists)
        exact ⟨head :: before, x, after, by simp [hs], by simpa [hp] using hb, hx⟩

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
  induction route generalizing left right with
  | nil => cases hleft
  | cons head tail ih =>
      simp only [SwitchSimple, List.map_cons, List.nodup_cons] at hsimple
      grind [SwitchSimple]

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
      have hbaseSame : nextBase = base := congrArg Prod.snd
        (harriveBase.symm.trans (groove_forward (hbase (p, x) List.mem_cons_self)))
      have htailBase : PassagesGrooved nextBase rest := by
        rw [hbaseSame]
        exact fun passage hp => hbase passage (List.mem_cons_of_mem _ hp)
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
            grind
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
                  _htailGrooved, hprotectedFinal⟩ := hcomplete
              have hfull := PhysicalTrace.cons harriveX hlink htailTrace
              exact Or.inr (Or.inr ⟨finalState, hfull,
                hfull.grooved_of_switchSimple (by simpa [SwitchSimple] using hsimple),
                hprotectedFinal⟩)
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
      ⟨suffix, heq, htail⟩ | ⟨suffix, heq, htail⟩
  all_goals
    cases suffix with
    | nil => cases htail; rfl
    | cons passage rest =>
        have := htail.head_arrive.1
        have hm : passage ∈ left ∨ passage ∈ right := by simp [heq]
        grind [passageSwitch]

theorem source_of_mem_reversePassages
    {passage : Passage} {passages : List Passage}
    (hmem : passage ∈ reversePassages passages) :
    ∃ old ∈ passages, passage = (old.2, old.1) := by
  obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmem
  exact ⟨old, List.mem_reverse.mp hold, heq.symm⟩

theorem ManufacturedReflector.support_grooves_of_orientedRoute
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (selector state : Tongues)
    (hroute : PassagesGrooved state (A.orientedRoute selector)) :
    PathGrooves A.toSupported.paths state := by
  intro path hp old ho
  obtain ⟨oriented, hm, horient⟩ := A.support_passage_on_orientedRoute selector hp ho
  rcases horient with rfl | rfl
  · exact hroute _ hm
  · exact groove_forward (hroute (old.2, old.1) hm)

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
  suffices ∃ reference, PathGrooves A.toSupported.paths reference ∧
      A.orientedRoute reference = A.orientedRoute state ∧
      A.orientedFinish reference = A.orientedFinish state ∧
      (∀ j, reference j ≠ base j → reference j = state j) by
    obtain ⟨reference, hp, hr, hf, hg⟩ := this
    refine ⟨reference, hp, hr, hf, ?_, hg⟩
    rw [← hr]
    exact (A.orientedRoute_trace reference hp).grooved_of_switchSimple
      (A.orientedRoute_simple reference)
  cases A with
  | stay R => exact ⟨base, hpaths, rfl, rfl, fun _ hj => (hj rfl).elim⟩
  | flip R =>
      let reference : Tongues := fun j => if j = R.actionSwitch then state j else base j
      refine ⟨reference, ?_, ?_, ?_, ?_⟩
      · intro path hp
        apply (hpaths path hp).transfer
        intro passage hm
        have hne := R.support_foreign path hp passage hm
        simp [reference, hne]
      · simp [ManufacturedReflector.orientedRoute, reference]
      · simp [ManufacturedReflector.orientedFinish, reference]
      · intro j hj
        by_cases heq : j = R.actionSwitch <;> simp_all [reference]

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
    have hprefixForeign : ∀ passage ∈ before,
        passageSwitch passage ≠ passageSwitch (p, x) := by
      rw [hsplit] at hsimple
      grind [SwitchSimple]
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
    have hstateBase : state (passageSwitch (p, x)) ≠ base (passageSwitch (p, x)) := by
      have := hreferenceGuard (passageSwitch (p, x))
      grind
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
  ∃ approach p x suffix u v path old oriented,
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
    x = oriented.2

/-- The completed-reflector forward-splice construction only used the
second reflector to supply a switch-simple route.  This is the same lemma
with that route supplied directly, so it applies to a partial second run. -/
theorem partial_first_forward_contact_active_lead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {route approach : List Passage} {p x : Nat}
    {suffix : List Passage} {startState u v : Tongues}
    {oriented : Passage}
    (hsplit : route = approach ++ (p, x) :: suffix)
    (hfullSimple : SwitchSimple route)
    (happroach :
      PhysicalTrace w (e, startState) approach (p, u))
    (hpaths : PathGrooves A.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3))
    (horiented : oriented ∈ A.orientedRoute u)
    (horientedGroove : arrive u oriented.2 = (oriented.1, u))
    (hforward : x = oriented.2) :
    ∃ (entry mouth returnPort outside : Nat)
        (oldPrefix oldTail candy : List Passage),
      (entry, mouth) ∈ A.orientedRoute u ∧
      A.orientedRoute u = oldPrefix ++ (entry, mouth) :: oldTail ∧
      PhysicalTrace w (outside, u) oldTail (A.orientedFinish u, u) ∧
      PhysicalTrace w (e, u) approach (returnPort, u) ∧
      PassagesGrooved u approach ∧
      (∀ passage ∈ approach, passageSwitch passage ≠ mouth / 3) ∧
      entry % 3 ≠ 0 ∧ entry / 3 = mouth / 3 ∧
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
  subst x
  have hap : a ≠ p := by
    intro heq
    subst p
    have hforwardOld := groove_forward horientedGroove
    have hvu := congrArg Prod.snd (harrive.symm.trans hforwardOld)
    exact hchanged (congrFun hvu (a / 3))
  obtain ⟨hsStem, haBranch, hpBranch, hsa, hsp⟩ :=
    crossed_arrivals_geometry horientedGroove harrive hap
  obtain ⟨oldPrefix, oldTail, hrouteSplit⟩ := List.append_of_mem horiented
  have hroute := A.orientedRoute_trace u hpaths
  have hrouteSimple := A.orientedRoute_simple u
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  obtain ⟨outside, hmouth, hOldPrefix, hOldRest⟩ :=
    (hrouteSplit ▸ hroute).split_grooved_at (hrouteSplit ▸ hrouteGrooved)
  have hOldGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by rw [hrouteSplit]; simp [hp])
  have hOldForeign : ∀ passage ∈ oldPrefix, passageSwitch passage ≠ s / 3 := by
    rw [hrouteSplit] at hrouteSimple
    grind [SwitchSimple, passageSwitch]
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple (by grind [SwitchSimple])
  have hApproachForeign : ∀ passage ∈ approach, passageSwitch passage ≠ s / 3 := by
    grind [SwitchSimple, passageSwitch]
  let candy := reversePassages oldPrefix ++ approach
  have hCandyGrooved : PassagesGrooved u candy := by
    intro passage hp
    rcases List.mem_append.mp hp with hp | hp
    · exact reversePassages_grooved hOldGrooved passage hp
    · exact hApproachGrooved passage hp
  have hCandyForeign : ∀ passage ∈ candy, passageSwitch passage ≠ s / 3 := by
    intro passage hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨old, hold, rfl⟩ := source_of_mem_reversePassages hp
      exact fun heq => hOldForeign old hold
        ((hOldPrefix.passage_exit_switch old hold).symm.trans heq)
    · exact hApproachForeign passage hp
  have hforward := happroach.replay_grooved u hApproachGrooved
  have hsplice : PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy] using (physicalTrace_contact_retraces_prefix
      hOldPrefix hOldGrooved A.entryEdge horientedGroove).append hforward
  have hSpliceGrooved : PassagesGrooved u ((s, a) :: candy) := by
    intro passage hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact groove_forward horientedGroove
    · exact hCandyGrooved passage hp
  have hflip : v = flipAt u (s / 3) := by
    simpa only [hsp] using changed_arrival_eq_flipAt harrive hchanged
  have hcrossed : arrive u p = (s, flipAt u (s / 3)) := by rw [harrive, hflip]
  refine ⟨a, s, p, outside, oldPrefix, oldTail, candy, horiented, hrouteSplit,
    hOldRest, hforward, hApproachGrooved, hApproachForeign, haBranch, hsa.symm,
    hmouth, hap, hSpliceGrooved, hsplice, hcrossed, hpaths, hCandyGrooved,
    hCandyForeign, ?_, ?_⟩
  · exact stem_lobe_isReflector_foreign w candy hsStem haBranch hpBranch hsa hsp hap
      hCandyForeign hsplice.linked hsplice.last_link hmouth
  · rw [stepN_add, happroach.sound]
    simp [stepN, step, hcrossed, hmouth]

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
  obtain ⟨outside, hlink, _, htail⟩ :=
    (hfreshSplit ▸ happroach).split_grooved_at (hfreshSplit ▸ happroachGrooved)
  have hfreshRest := PhysicalTrace.cons
    (groove_forward (happroachGrooved target htargetMem)) hlink htail
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
    have htail := (hcore ▸ hroute).after_prefix
      (R.runway_trace state (pathGrooves_pair.mp hpaths).1)
    have hsimple : SwitchSimple core := by
      have hs := hrouteSimple
      rw [hcore] at hs
      exact (List.nodup_append.mp (by simpa [SwitchSimple] using hs)).2.1
    obtain ⟨before, hsplit⟩ :=
      split_after_prefix_of_not_mem (hcore.symm.trans hrouteSplit) hnotRunway
    obtain ⟨_, _, hprefix, _⟩ := (hsplit ▸ htail).split_grooved_at
      (hsplit ▸ htail.grooved_of_switchSimple hsimple)
    refine ⟨before, hprefix, ?_⟩
    rw [hsplit] at hsimple
    grind [SwitchSimple, passageSwitch]
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
  have hsimple := (ManufacturedReflector.flip R).orientedRoute_simple state
  have htarget : (entry, mouth) ∈ (ManufacturedReflector.flip R).orientedRoute state := by
    rw [hsplit]; simp
  have htailForeign : ∀ passage ∈ oldTail, passageSwitch passage ≠ entry / 3 := by
    rw [hsplit] at hsimple
    grind [SwitchSimple, passageSwitch]
  have hnewOld := R.candy_entry_foreign_action hold horientation
  have hfinish := arrive_exit_switch state ((ManufacturedReflector.flip R).orientedFinish state)
  rw [R.oriented_finish_arrive state] at hfinish
  change R.actionSwitch = (ManufacturedReflector.flip R).orientedFinish state / 3 at hfinish
  refine ⟨htail.append (R.oriented_return_trace state hpaths), ?_⟩
  intro passage hp
  rcases List.mem_append.mp hp with hp | hp
  · exact htailForeign passage hp
  · rcases List.mem_cons.mp hp with rfl | hp
    · simpa only [passageSwitch, ← hfinish] using Ne.symm hnewOld
    · obtain ⟨old, holdRunway, rfl⟩ := source_of_mem_reversePassages hp
      intro heq
      have holdRoute : old ∈ (ManufacturedReflector.flip R).orientedRoute state := by
        simp only [ManufacturedReflector.orientedRoute]
        split <;> exact List.mem_append_left _ holdRunway
      have hequal := hsimple.passage_eq_of_mem holdRoute htarget
        ((R.runwayTrace.passage_exit_switch old holdRunway).symm.trans heq)
      exact hnotRunway (hequal ▸ holdRunway)


end

end GeneralN
