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
  classical
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

/-- Replay a damaged switch-simple route up to its first facing obstruction.
The prefix is an actual physical trace in the new state and cannot touch the
obstruction's switch.  Consequently that switch still has its initial tongue
when reached, and the train exits through the other branch.  If there is no
facing obstruction, the whole route repairs as before.

This is the trace-valued strengthening needed for the remaining theta case:
it exposes the exact approach to the diversion instead of an unlocated broken
groove. -/
theorem PhysicalTrace.repair_until_first_facing
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PassagesGrooved start.2 passages)
    (state : Tongues) :
    (∃ before p x after contact other,
      passages = before ++ (p, x) :: after ∧
      PhysicalTrace w (start.1, state) before (p, contact) ∧
      (∀ passage ∈ before,
        passageSwitch passage ≠ passageSwitch (p, x)) ∧
      p % 3 = 0 ∧
      arrive contact x ≠ (p, contact) ∧
      arrive contact p = (other, contact) ∧ other ≠ x) ∨
    ∃ finalState,
      PhysicalTrace w (start.1, state) passages
        (finish.1, finalState) ∧
      PassagesGrooved finalState passages := by
  classical
  let P : Passage → Prop := fun passage =>
    arrive state passage.2 ≠ (passage.1, state) ∧
      passage.1 % 3 = 0
  by_cases hfacing : ∃ passage ∈ passages, P passage
  · obtain ⟨before, target, after, hsplit, hbefore, htarget⟩ :=
      exists_first_satisfying_split P passages hfacing
    rcases target with ⟨p, x⟩
    have htrace' := htrace
    rw [hsplit] at htrace'
    obtain ⟨middle, hprefixBase, hsuffixBase⟩ := htrace'.split_append
    have hmiddlePort : middle.1 = p := hsuffixBase.head_arrive.1
    rcases middle with ⟨middlePort, middleState⟩
    simp only at hmiddlePort
    subst middlePort
    have hprefixSimple : SwitchSimple before := by
      unfold SwitchSimple at hsimple ⊢
      rw [hsplit] at hsimple
      simp only [List.map_append, List.map_cons] at hsimple
      exact (List.nodup_append.mp hsimple).1
    have hprefixBaseGrooved : PassagesGrooved start.2 before := by
      intro passage hp
      exact hbase passage (by
        rw [hsplit]
        exact List.mem_append_left _ hp)
    have hprefixForeign : ∀ passage ∈ before,
        passageSwitch passage ≠ passageSwitch (p, x) := by
      unfold SwitchSimple at hsimple
      rw [hsplit] at hsimple
      simp only [List.map_append, List.map_cons] at hsimple
      have hparts := List.nodup_append.mp hsimple
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (passageSwitch (p, x)) (by simp)
      exact hne hEq
    have hprefixForward : ∀ passage ∈ before,
        arrive state passage.2 ≠ (passage.1, state) →
          passage.1 % 3 ≠ 0 := by
      intro passage hp hbroken hstem
      exact (hbefore passage hp ⟨hbroken, hstem⟩).elim
    obtain ⟨contact, hprefix, _hprefixGrooved⟩ :=
      hprefixBase.repair_forward_damage hprefixSimple
        hprefixBaseGrooved state hprefixForward
    have hsame : contact (passageSwitch (p, x)) =
        state (passageSwitch (p, x)) :=
      hprefix.preserves _ hprefixForeign
    have htargetBase : arrive start.2 x = (p, start.2) :=
      hbase (p, x) (by
        rw [hsplit]
        exact List.mem_append_right before List.mem_cons_self)
    have hswitch : x / 3 = passageSwitch (p, x) := by
      have h := arrive_exit_switch start.2 x
      rw [htargetBase] at h
      exact h.symm
    have hbadContact : arrive contact x ≠ (p, contact) := by
      intro hgroove
      apply htarget.1
      apply groove_transfer hgroove
      rw [hswitch]
      exact hsame.symm
    let other := (arrive contact p).1
    have hactual : arrive contact p = (other, contact) := by
      dsimp [other]
      unfold arrive
      rw [if_pos htarget.2]
    have hother : other ≠ x := by
      intro heq
      have hback := arrive_back contact p
      rw [hactual, heq] at hback
      exact hbadContact hback
    exact Or.inl ⟨before, p, x, after, contact, other,
      hsplit, hprefix, hprefixForeign, htarget.2,
      hbadContact, hactual, hother⟩
  · right
    apply htrace.repair_forward_damage hsimple hbase state
    intro passage hpassage hbroken
    by_cases hstem : passage.1 % 3 = 0
    · exact (hfacing ⟨passage, hpassage, hbroken, hstem⟩).elim
    · exact hstem

/-- Replay a switch-simple grooved route while protecting an independent
family of already-installed grooves.  The replay stops at the first event
that is not harmless for the two-route system:

* a facing entry leaves through a branch different from the reference route;
* a trailing passage genuinely rewrites a switch used by `protected`.

Before either stop, the returned prefix is an exact physical trace and the
whole protected family is still grooved.  If neither event occurs, the full
reference route is installed and the protected family survives as well.

This is the well-founded interface needed by the global theta argument: each
recursive call consumes one reference passage, while no earlier contact is
silently allowed to damage the other reflector. -/
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
  classical
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

/-- Classify the state-changing stop produced by
`repair_preserving_paths_until_conflict` against the protected reflector's
currently selected route.  A backward-oriented contact closes an exact
grooved cycle immediately.  The only residual is the forward orientation,
where the old selected passage repairs itself on the next trailing entry.

Unlike the older outward-fault theorem, the fresh approach here may be any
switch-simple route prefix.  This is the form required when one manufactured
reflector is being repaired while the other's support is kept intact. -/
theorem ManufacturedReflector.protected_changed_contact_periodic_or_forward
    {w : Wiring} {g e p x : Nat}
    (B : ManufacturedReflector w e g)
    {startState u v : Tongues}
    {route approach suffix : List Passage}
    {path : List Passage} {old : Passage}
    (hrouteSplit : route = approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    EventuallyPeriodic w (g, startState) ∨
      ∃ oriented repaired,
        oriented ∈ B.orientedRoute u ∧
        arrive u oriented.2 = (oriented.1, u) ∧
        passageSwitch oriented = p / 3 ∧
        x = oriented.2 ∧
        arrive v oriented.1 = (oriented.2, repaired) ∧
        arrive repaired oriented.2 = (oriented.1, repaired) := by
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    B.changed_contact_on_orientedRoute u v hpaths
      hpath hold hswitch harrive hchanged
  rcases hdirection with hbackward | hforward
  · obtain ⟨recorded, tail, hBsplit⟩ :=
      List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace u hpaths
    have hBsimple := B.orientedRoute_simple u
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedForeign : ∀ passage ∈ recorded,
        passageSwitch passage ≠ p / 3 := by
      intro passage hp hEq
      apply hprefixData.2 passage hp
      exact hEq.trans horientedSwitch.symm
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hflip : v = flipAt u (p / 3) :=
      changed_arrival_eq_flipAt harrive hchanged
    have hrecordedV : PhysicalTrace w
        (e, v) recorded (oriented.1, v) := by
      rw [hflip]
      exact hrecorded.flip_unvisited hrecordedForeign
    have hrecordedGroovedV : PassagesGrooved v recorded :=
      hrecordedV.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple' := hrouteSimple
    rw [hrouteSplit] at hrouteSimple'
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple' ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      exact (List.nodup_append.mp hrouteSimple').1
    have happroachForeign : ∀ passage ∈ approach,
        passageSwitch passage ≠ p / 3 := by
      unfold SwitchSimple at hrouteSimple'
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      have hparts := List.nodup_append.mp hrouteSimple'
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (p / 3) (by simp [passageSwitch])
      exact hne hEq
    have happroachV : PhysicalTrace w
        (g, flipAt startState (p / 3)) approach (p, v) := by
      rw [hflip]
      exact happroach.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have hsettles := backward_contact_settles_grooved_cycle
      hrecorded hrecordedGroovedV B.entryEdge
      (by simpa [hbackward] using harrive)
      happroach happroachGroovedV
    exact Or.inl
      (eventuallyPeriodic_of_reaches_simple_cycle
        happroach.sound hsettles)
  · obtain ⟨hforwardExit, repaired, hrepair, hgroove⟩ := hforward
    exact Or.inr ⟨oriented, repaired, horiented,
      horientedGroove, horientedSwitch,
      hforwardExit, hrepair, hgroove⟩

/-- A facing replay contact that follows an intact protected support passage
has only two orientations.  If it runs backward relative to the protected
reflector's selected route, the two prefixes form an exact grooved cycle.  If
it runs forward, the fresh route has literally merged into that selected
route; the residual records the exact oriented passage `(p, fresh)`.

This theorem handles the no-tongue-change counterpart of
`protected_changed_contact_periodic_or_forward`. -/
theorem ManufacturedReflector.protected_facing_contact_periodic_or_forward
    {w : Wiring} {g e p marker fresh : Nat}
    (B : ManufacturedReflector w e g)
    {startState contact : Tongues}
    {route approach suffix path : List Passage}
    (hrouteSplit : route = approach ++ (p, marker) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact)) :
    EventuallyPeriodic w (g, startState) ∨
      (p, fresh) ∈ B.orientedRoute contact := by
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute contact hpath hold
  rcases horientation with hsame | hreverse
  · have horientedEq : oriented = (fresh, p) := hsame
    subst oriented
    obtain ⟨recorded, tail, hBsplit⟩ :=
      List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace contact hpaths
    have hBsimple := B.orientedRoute_simple contact
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hrecordedGrooved : PassagesGrooved contact recorded :=
      hrecorded.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple' := hrouteSimple
    rw [hrouteSplit] at hrouteSimple'
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple' ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple'
      exact (List.nodup_append.mp hrouteSimple').1
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have hsettles := backward_contact_settles_grooved_cycle
      hrecorded hrecordedGrooved B.entryEdge harrive
      happroach happroachGrooved
    exact Or.inl
      (eventuallyPeriodic_of_reaches_simple_cycle
        happroach.sound hsettles)
  · right
    simpa [hreverse] using horiented

/-- Entering a flip reflector's mouth after a switch-simple prefix is already
eventually periodic whenever its reusable support is grooved.  The first
capture toggles the mouth and returns to the prefix's start; the same grooved
prefix and capture in the opposite mouth state toggle it back. -/
theorem ManufacturedFlipReflector.facing_mouth_contact_eventuallyPeriodic
    {w : Wiring} {g e x : Nat}
    (B : ManufacturedFlipReflector w e g)
    {startState contact : Tongues}
    {route approach suffix : List Passage}
    (hrouteSplit : route = approach ++ (B.mouth, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach
      (B.mouth, contact))
    (hpaths : PathGrooves [B.runway, B.candy] contact) :
    EventuallyPeriodic w (g, startState) := by
  have hrouteSimple' := hrouteSimple
  rw [hrouteSplit] at hrouteSimple'
  have happroachSimple : SwitchSimple approach := by
    unfold SwitchSimple at hrouteSimple' ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple'
    exact (List.nodup_append.mp hrouteSimple').1
  have hforeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ B.actionSwitch := by
    unfold SwitchSimple at hrouteSimple'
    simp only [List.map_append, List.map_cons] at hrouteSimple'
    have hparts := List.nodup_append.mp hrouteSimple'
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (B.mouth, x)) (by simp)
    apply hne
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hEq
  have happroachGrooved : PassagesGrooved contact approach :=
    happroach.grooved_of_switchSimple happroachSimple
  have happroachContact : PhysicalTrace w
      (g, contact) approach (B.mouth, contact) :=
    happroach.replay_grooved contact happroachGrooved
  let alternate := flipAt contact B.actionSwitch
  have happroachAlternate : PhysicalTrace w
      (g, alternate) approach (B.mouth, alternate) := by
    dsimp [alternate]
    exact happroachContact.flip_unvisited hforeign
  have hpathsAlternate :
      PathGrooves [B.runway, B.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [B.runway, B.candy]
      ((LocalAction.flip B.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action B.support_foreign
  let cap := B.candy.length + 2 + B.runway.length
  have hcaptureFromAlternate :
      stepN w cap (B.mouth, alternate) = some (g, contact) := by
    dsimp [cap, alternate]
    exact B.capture_from_mouth contact
      (pathGrooves_pair.mp hpaths).1
      (pathGrooves_pair.mp hpaths).2
  have hcaptureFromContact :
      stepN w cap (B.mouth, contact) = some (g, alternate) := by
    have hcapture := B.capture_from_mouth alternate
      (pathGrooves_pair.mp hpathsAlternate).1
      (pathGrooves_pair.mp hpathsAlternate).2
    simpa [cap, alternate, flipAt_flipAt] using hcapture
  let half := approach.length + cap
  have hhalfAlternate :
      stepN w half (g, alternate) = some (g, contact) := by
    dsimp [half]
    rw [stepN_add, happroachAlternate.sound]
    exact hcaptureFromAlternate
  have hhalfContact :
      stepN w half (g, contact) = some (g, alternate) := by
    dsimp [half]
    rw [stepN_add, happroachContact.sound]
    exact hcaptureFromContact
  have hperiod :
      stepN w (half + half) (g, alternate) =
        some (g, alternate) := by
    rw [stepN_add, hhalfAlternate]
    exact hhalfContact
  have hperiodicAlternate : EventuallyPeriodic w (g, alternate) :=
    eventuallyPeriodic_of_period (by
      dsimp [half, cap]
      omega) hperiod
  have hlead : stepN w (approach.length + cap)
      (g, startState) = some (g, alternate) := by
    rw [stepN_add, happroach.sound]
    exact hcaptureFromContact
  exact hperiodicAlternate.prepend hlead

/-- The apparent final-return exception in activation provenance is not a
residual.  A genuine final-return change forces a nondegenerate flip
reflector; the facing stem is its mouth, and the two-capture theorem above
closes the run. -/
theorem ManufacturedReflector.return_change_facing_eventuallyPeriodic
    {w : Wiring} {g e p x : Nat}
    (B : ManufacturedReflector w e g)
    {startState contact : Tongues}
    {route approach suffix : List Passage}
    (hrouteSplit : route = approach ++ (p, x) :: suffix)
    (hrouteSimple : SwitchSimple route)
    (happroach : PhysicalTrace w (g, startState) approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hp : p % 3 = 0)
    (hswitch : p / 3 = B.preReturn.1 / 3)
    (hreturnChange : B.activatedState (p / 3) ≠
      B.preReturn.2 (p / 3)) :
    EventuallyPeriodic w (g, startState) := by
  cases B with
  | stay R =>
      exact (hreturnChange rfl).elim
  | flip R =>
      have hsecondSwitch : R.secondArm / 3 = R.mouth / 3 := by
        have hs := arrive_exit_switch R.returnState R.secondArm
        rw [R.crossed] at hs
        exact hs.symm
      have hmouthStem := R.mouth_is_stem
      have hpmouth : p = R.mouth := by
        change p / 3 = R.secondArm / 3 at hswitch
        omega
      subst p
      exact R.facing_mouth_contact_eventuallyPeriodic
        hrouteSplit hrouteSimple happroach hpaths

/-- Whole-route form of the local forward-repair law.  If no broken passage
of a switch-simple reference trace is approached through its stem, every
broken passage is trailing and the trace repairs all of its grooves. -/
theorem PhysicalTrace.repair_forward_damage_or_facing
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PassagesGrooved start.2 passages)
    (state : Tongues) :
    (∃ passage ∈ passages,
      arrive state passage.2 ≠ (passage.1, state) ∧
      passage.1 % 3 = 0) ∨
    ∃ finalState,
      PhysicalTrace w (start.1, state) passages
        (finish.1, finalState) ∧
      PassagesGrooved finalState passages := by
  classical
  by_cases hfacing : ∃ passage ∈ passages,
      arrive state passage.2 ≠ (passage.1, state) ∧
      passage.1 % 3 = 0
  · exact Or.inl hfacing
  · right
    apply htrace.repair_forward_damage hsimple hbase state
    intro passage hpassage hbroken
    by_cases hstem : passage.1 % 3 = 0
    · exact (hfacing ⟨passage, hpassage, hbroken, hstem⟩).elim
    · exact hstem

/-- Endpoint-strengthened deterministic prefix comparison.  Two traces from
the same physical configuration are prefix-comparable; moreover, the unmatched
suffix is itself a physical trace from the shorter trace's endpoint to the
longer trace's endpoint. -/
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

/-- Endpoint-strengthened forward merge.  The fresh branch changes only the
contact tongue.  Rebase the old suffix in that changed state; determinism then
identifies not only which suffix is longer, but the exact physical trace along
the unmatched tail. -/
theorem forward_merge_tails_endpoint_dichotomy
    {w : Wiring} {oldEntry freshEntry exit : Nat}
    {u v : Tongues} {oldTail freshTail : List Passage}
    {oldFinish freshFinish : Nat × Tongues}
    (holdTrace : PhysicalTrace w (oldEntry, u)
      ((oldEntry, exit) :: oldTail) oldFinish)
    (hfreshTrace : PhysicalTrace w (freshEntry, u)
      ((freshEntry, exit) :: freshTail) freshFinish)
    (hOldSimple : SwitchSimple ((oldEntry, exit) :: oldTail))
    (hold : arrive u oldEntry = (exit, u))
    (hswitch : oldEntry / 3 = freshEntry / 3)
    (hfresh : arrive u freshEntry = (exit, v))
    (hchanged : v (freshEntry / 3) ≠ u (freshEntry / 3)) :
    (∃ suffix,
      freshTail = oldTail ++ suffix ∧
      PhysicalTrace w
        (oldFinish.1, flipAt oldFinish.2 (freshEntry / 3))
        suffix freshFinish) ∨
    (∃ suffix,
      oldTail = freshTail ++ suffix ∧
      PhysicalTrace w freshFinish suffix
        (oldFinish.1, flipAt oldFinish.2 (freshEntry / 3))) := by
  cases holdTrace with
  | @cons _ _ oldNext _ oldAfter _ _ holdArrive oldLink oldRest =>
      have hOldAfter : oldAfter = u := by
        have hEq := hold.symm.trans holdArrive
        exact (congrArg Prod.snd hEq).symm
      subst oldAfter
      cases hfreshTrace with
      | @cons _ _ freshNext _ freshAfter _ _ freshArrive freshLink
          freshRest =>
          have hfreshAfter : freshAfter = v := by
            have hEq := hfresh.symm.trans freshArrive
            exact (congrArg Prod.snd hEq).symm
          subst freshAfter
          have hnext : oldNext = freshNext := by
            rw [oldLink] at freshLink
            injection freshLink
          subst freshNext
          have hflip : v = flipAt u (freshEntry / 3) :=
            changed_arrival_eq_flipAt hfresh hchanged
          have hforeign : ∀ passage ∈ oldTail,
              passageSwitch passage ≠ freshEntry / 3 := by
            unfold SwitchSimple at hOldSimple
            simp only [List.map_cons, List.nodup_cons] at hOldSimple
            intro passage hp hEq
            apply hOldSimple.1
            apply List.mem_map.mpr
            exact ⟨passage, hp, by
              simpa [passageSwitch, hswitch] using hEq⟩
          have oldRest' : PhysicalTrace w
              (oldNext, flipAt u (freshEntry / 3)) oldTail
              (oldFinish.1,
                flipAt oldFinish.2 (freshEntry / 3)) :=
            oldRest.flip_unvisited hforeign
          rw [← hflip] at oldRest'
          exact physicalTrace_prefix_comparable_with_endpoints
            oldRest' freshRest

/-- Converse membership for the explicitly reversed passage list. -/
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

/-- A forward theta fault with the endpoint information retained.  At the
merge, the fresh exploration suffix and old selected-route suffix share one
deterministic continuation.  Whichever suffix is longer, its unmatched tail
is an actual physical trace between the two advertised endpoints in the
post-contact tongue state. -/
theorem ManufacturedReflector.ForwardOrientedFault.tails_endpoint_dichotomy
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hfault : A.ForwardOrientedFault B) :
    ∃ (approach : List Passage) (p x : Nat)
        (suffix : List Passage) (u v : Tongues)
        (oriented : Passage) (oldPrefix oldTail : List Passage),
      B.exploration = approach ++ (p, x) :: suffix ∧
      A.orientedRoute u = oldPrefix ++ oriented :: oldTail ∧
      PathGrooves A.toSupported.paths u ∧
      arrive u p = (x, v) ∧
      v (p / 3) ≠ u (p / 3) ∧
      passageSwitch oriented = p / 3 ∧
      x = oriented.2 ∧
      ((∃ extra,
          suffix = oldTail ++ extra ∧
          PhysicalTrace w (A.orientedFinish u, v)
            extra B.preReturn) ∨
        (∃ extra,
          oldTail = suffix ++ extra ∧
          PhysicalTrace w B.preReturn extra
            (A.orientedFinish u, v))) := by
  obtain ⟨approach, p, x, suffix, u, v, oriented, repaired,
      hsplit, happroach, hgrooves, harrive, hchanged,
      horiented, horientedGroove, horientedSwitch,
      hforward, _hrepair, _hrestored⟩ := hfault
  obtain ⟨oldPrefix, oldTail, hrouteSplit⟩ :=
    List.append_of_mem horiented
  have hroute := A.orientedRoute_trace u hgrooves
  have hrouteSimple := A.orientedRoute_simple u
  have hroute' := hroute
  rw [hrouteSplit] at hroute'
  obtain ⟨oldMiddle, _hOldPrefix, hOldAfter⟩ :=
    hroute'.split_append
  have hOldPrefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hrouteSplit
      (hroute.grooved_of_switchSimple hrouteSimple) hrouteSimple
  have hOldMiddle : oldMiddle = (oriented.1, u) := by
    have h₁ := _hOldPrefix.sound
    have h₂ := hOldPrefixData.1.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst oldMiddle
  have hOldSimple : SwitchSimple (oriented :: oldTail) := by
    unfold SwitchSimple at hrouteSimple ⊢
    rw [hrouteSplit] at hrouteSimple
    simp only [List.map_append] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).2.1
  have hnew := B.exploration_trace
  rw [hsplit] at hnew
  obtain ⟨newMiddle, hNewPrefix, hNewAfter⟩ := hnew.split_append
  have hNewMiddle : newMiddle = (p, u) := by
    have h₁ := hNewPrefix.sound
    have h₂ := happroach.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst newMiddle
  have hNewAfter' : PhysicalTrace w (p, u)
      ((p, oriented.2) :: suffix) B.preReturn := by
    simpa [hforward] using hNewAfter
  have hendpoints := forward_merge_tails_endpoint_dichotomy
    hOldAfter hNewAfter' hOldSimple
    (groove_forward horientedGroove)
    (by simpa [passageSwitch] using horientedSwitch)
    (by simpa [hforward] using harrive) hchanged
  have hflip : v = flipAt u (p / 3) :=
    changed_arrival_eq_flipAt harrive hchanged
  rw [← hflip] at hendpoints
  exact ⟨approach, p, x, suffix, u, v, oriented,
    oldPrefix, oldTail, hsplit, hrouteSplit, hgrooves,
    harrive, hchanged, horientedSwitch, hforward, hendpoints⟩

/-- Grooving the selected outward route grooves every reusable support path.
For a reverse-selected candy, each stored passage follows by reversing the
corresponding grooved reverse passage. -/
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

/-- **Damaged-reflector macro dichotomy.**  Fix any grooved state selecting
one of a manufactured reflector's two possible outward routes.  From an
arbitrary tongue vector, either that route exposes a concrete facing-first
broken passage, or it repairs every support groove and completes all the way
to the opposite boundary.  The theorem is over raw `Wiring`/`stepN`, for
arbitrary `N`; no planarity or enumeration is used. -/
theorem ManufacturedReflector.repair_or_facing_diversion
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (selector state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths selector) :
    (∃ passage ∈ A.orientedRoute selector,
      arrive state passage.2 ≠ (passage.1, state) ∧
      passage.1 % 3 = 0) ∨
    ∃ travel finalState,
      stepN w travel (g, state) =
        some (e, A.toSupported.action.apply finalState) ∧
      PathGrooves A.toSupported.paths finalState := by
  have hroute := A.orientedRoute_trace selector hpaths
  have hsimple := A.orientedRoute_simple selector
  have hrouteGrooved :
      PassagesGrooved selector (A.orientedRoute selector) :=
    hroute.grooved_of_switchSimple hsimple
  rcases hroute.repair_forward_damage_or_facing
      hsimple hrouteGrooved state with hfacing | hrepaired
  · exact Or.inl hfacing
  · right
    obtain ⟨finalState, hrepairTrace, hfinalRouteGrooved⟩ := hrepaired
    have hfinalPaths : PathGrooves A.toSupported.paths finalState :=
      A.support_grooves_of_orientedRoute selector finalState
        hfinalRouteGrooved
    have horiented := A.oriented_data_eq_of_route_grooved
      selector finalState hrouteGrooved hfinalRouteGrooved
    have hrouteFinal := A.orientedRoute_trace finalState hfinalPaths
    have hrouteFinal' : PhysicalTrace w (g, finalState)
        (A.orientedRoute selector)
        (A.orientedFinish selector, finalState) := by
      simpa [horiented.1, horiented.2] using hrouteFinal
    have hsplit : A.orientedRoute finalState =
        A.orientedRoute selector ++ [] := by
      simpa [horiented.1]
    obtain ⟨tailSteps, _hlen, htail⟩ :=
      A.complete_after_oriented_prefix finalState hfinalPaths
        hsplit hrouteFinal'
    refine ⟨(A.orientedRoute selector).length + tailSteps,
      finalState, ?_, hfinalPaths⟩
    rw [stepN_add, hrepairTrace.sound]
    exact htail

/-- A facing diversion is the only obstruction left by whole-route repair:
some passage on the route selected in `selector` is no longer grooved in
`state`, and replay reaches that passage through its stem. -/
def ManufacturedReflector.FacingDiversion
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (selector state : Tongues) : Prop :=
  ∃ passage ∈ A.orientedRoute selector,
    arrive state passage.2 ≠ (passage.1, state) ∧
    passage.1 % 3 = 0

/-- A facing obstruction on the route selected by the current state is never
the flip reflector's private action mouth: that arm is selected and therefore
already grooved.  Every such obstruction is an oriented occurrence of a
genuine reusable support passage. -/
theorem ManufacturedReflector.current_facing_has_support_witness
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (state : Tongues)
    (hfacing : A.FacingDiversion state state) :
    ∃ oriented ∈ A.orientedRoute state,
      arrive state oriented.2 ≠ (oriented.1, state) ∧
      oriented.1 % 3 = 0 ∧
      ∃ path ∈ A.toSupported.paths, ∃ old ∈ path,
        oriented = old ∨ oriented = (old.2, old.1) := by
  obtain ⟨oriented, horiented, hbroken, hstem⟩ := hfacing
  refine ⟨oriented, horiented, hbroken, hstem, ?_⟩
  cases A with
  | stay R =>
      change oriented ∈ R.runway ++ [(R.mouth, R.arm)] at horiented
      change ∃ path ∈ [R.runway, [(R.mouth, R.arm)]],
        ∃ old ∈ path,
          oriented = old ∨ oriented = (old.2, old.1)
      rcases List.mem_append.mp horiented with hrunway | hcore
      · exact ⟨R.runway, by simp, oriented, hrunway, Or.inl rfl⟩
      · simp only [List.mem_singleton] at hcore
        subst oriented
        exact ⟨[(R.mouth, R.arm)], by simp,
          (R.mouth, R.arm), List.mem_cons_self, Or.inl rfl⟩
  | flip R =>
      change ∃ path ∈ [R.runway, R.candy], ∃ old ∈ path,
        oriented = old ∨ oriented = (old.2, old.1)
      by_cases hselected :
          state R.actionSwitch = bval R.firstArm
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          if_pos] at horiented
        rcases List.mem_append.mp horiented with hrunway | hcore
        · exact ⟨R.runway, by simp, oriented, hrunway, Or.inl rfl⟩
        · rcases List.mem_cons.mp hcore with hhead | hcandy
          · subst oriented
            exact (hbroken
              (R.firstArm_groove_of_selected state hselected)).elim
          · exact ⟨R.candy, by simp, oriented, hcandy, Or.inl rfl⟩
      · have hsecond :
            state R.actionSwitch = bval R.secondArm := by
          rcases R.selected_arm state with hfirst | hsecond
          · exact absurd hfirst hselected
          · exact hsecond
        simp only [ManufacturedReflector.orientedRoute, hselected,
          if_false] at horiented
        rcases List.mem_append.mp horiented with hrunway | hcore
        · exact ⟨R.runway, by simp, oriented, hrunway, Or.inl rfl⟩
        · rcases List.mem_cons.mp hcore with hhead | hreverse
          · subst oriented
            exact (hbroken
              (R.secondArm_groove_of_selected state hsecond)).elim
          · obtain ⟨old, hold, hEq⟩ :=
              source_of_mem_reversePassages hreverse
            exact ⟨R.candy, by simp, old, hold, Or.inr hEq⟩

/-- Every state-changing passage in a manufactured exploration belongs to
the reflector's reusable support.  The only exploration passage omitted from
the support of a nondegenerate reflector is its facing mouth passage, and a
facing passage cannot change a tongue. -/
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

/-- Exclusive form of `activated_change_location`.  Away from the final
repeated-mouth switch, the unique changing exploration passage is retained,
and its post-passage value is already the final activated value.  The latter
fact follows because the final return can modify only its own switch. -/
theorem ManufacturedReflector.activated_change_location_strict
    {w : Wiring} {g e j : Nat}
    (A : ManufacturedReflector w g e)
    (hchange : A.activatedState j ≠ A.baseState j) :
    j = A.preReturn.1 / 3 ∨
      ∃ before p x after u v,
        A.exploration = before ++ (p, x) :: after ∧
        passageSwitch (p, x) = j ∧
        PhysicalTrace w (g, A.baseState) before (p, u) ∧
        arrive u p = (x, v) ∧
        u j = A.baseState j ∧ A.activatedState j = v j ∧
        v j ≠ u j ∧ j ≠ A.preReturn.1 / 3 := by
  by_cases hreturn : j = A.preReturn.1 / 3
  · exact Or.inl hreturn
  · right
    have hpreChange : A.preReturn.2 j ≠ A.baseState j := by
      rcases A.activated_change_before_or_at_return hchange with
        hatReturn | hpre
      · exact (hreturn hatReturn).elim
      · exact hpre
    obtain ⟨before, p, x, after, u, v,
        hsplit, hswitch, htrace, harrive,
        hbase, hpre, hchanged⟩ :=
      A.exploration_trace.changed_switch_has_changed_passage
        A.exploration_simple hpreChange
    obtain ⟨returnExit, hreturnArrive⟩ := A.return_arrive
    have hactivatedPre : A.activatedState j = A.preReturn.2 j :=
      arrive_preserves_other hreturnArrive hreturn
    exact ⟨before, p, x, after, u, v,
      hsplit, hswitch, htrace, harrive, hbase,
      hactivatedPre.trans hpre, hchanged, hreturn⟩

/-- Causal activation split.  A final net change either really occurs on the
last return passage, or it was already present at `preReturn` and is localized
to the unique state-changing exploration passage.  Unlike the coarser
port-based split, an identity return is therefore never misclassified as the
hard mouth case. -/
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
      ∃ approach fresh suffix u v path,
        A.exploration = approach ++ (fresh, stem) :: suffix ∧
        passageSwitch (fresh, stem) = stem / 3 ∧
        PhysicalTrace w (g, A.baseState) approach (fresh, u) ∧
        arrive u fresh = (stem, v) ∧
        path ∈ A.toSupported.paths ∧ (fresh, stem) ∈ path ∧
        other = fresh := by
  rcases A.activated_change_return_or_exploration hchange with
    hreturn | hchanged
  · exact Or.inl hreturn
  · right
    obtain ⟨approach, fresh, exit, suffix, u, v,
        hsplit, hswitch, htrace, harrive,
        _hbase, hactivated, hchanged⟩ := hchanged
    have hentrySwitch : fresh / 3 = stem / 3 := by
      simpa [passageSwitch] using hswitch
    have hchangedFresh : v (fresh / 3) ≠ u (fresh / 3) := by
      rw [hentrySwitch]
      exact hchanged
    obtain ⟨_hfreshBranch, hexitStem, _hv, _hback⟩ :=
      changed_arrival_is_trailing harrive hchangedFresh
    have hexitEq : exit = stem := by
      omega
    rw [hexitEq] at hsplit hswitch harrive
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
    exact ⟨approach, fresh, suffix, u, v, path,
      hsplit, by simpa [passageSwitch], htrace, harrive,
      hpath, hfreshSupport, hother⟩

/-- If repairing a currently selected route reaches its far endpoint with
both reflector supports installed, the run is already eventually periodic.
The common-support pair theorem supplies a periodic orbit from the repaired
state; the selected grooved route reaches the current endpoint on that orbit,
and determinism transfers periodicity first to that endpoint and then back
through the actual repair trace. -/
theorem ManufacturedReflector.completed_route_with_pair_support_periodic
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (base state finalState : Tongues)
    (hbasePaths : PathGrooves A.toSupported.paths base)
    (hrepair : PhysicalTrace w (g, state)
      (A.orientedRoute state)
      (A.orientedFinish state, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState) :
    EventuallyPeriodic w (g, state) := by
  obtain ⟨reference, _hreferencePaths, hroute, hfinish,
      hreferenceGrooved, _hguard⟩ :=
    A.current_route_reference base state hbasePaths
  have hfinalGrooved :
      PassagesGrooved finalState (A.orientedRoute state) :=
    hrepair.grooved_of_switchSimple (A.orientedRoute_simple state)
  have hfinalReferenceGrooved :
      PassagesGrooved finalState (A.orientedRoute reference) := by
    rw [hroute]
    exact hfinalGrooved
  have hreferenceGrooved' :
      PassagesGrooved reference (A.orientedRoute reference) := by
    rw [hroute]
    exact hreferenceGrooved
  have horiented := A.oriented_data_eq_of_route_grooved
    reference finalState hreferenceGrooved' hfinalReferenceGrooved
  have hrouteFinal := A.orientedRoute_trace finalState hAfinal
  have hrouteFinal' : PhysicalTrace w (g, finalState)
      (A.orientedRoute state)
      (A.orientedFinish state, finalState) := by
    rw [horiented.1, horiented.2, hroute, hfinish] at hrouteFinal
    exact hrouteFinal
  have hpair := manufactured_pair_eventually_periodic
    A B finalState hAfinal hBfinal
  have hendPeriodic := hpair.forward hrouteFinal'.sound
  exact hendPeriodic.prepend hrepair.sound

/-- **Protected two-reflector reduction.**  Start repairing `A` immediately
after `B` has been activated, but preserve every reusable groove of `B` at
each replay step.  The old undifferentiated facing residual is eliminated:

* a genuine return-mouth change is periodic by the two-capture theorem;
* a backward support contact is periodic by exact grooved retracing;
* a state-changing backward contact is periodic for the same reason.

Only two explicitly forward-oriented merges remain, plus complete repair of
`A` with both support families still installed.  All data are raw physical
traces; no planarity or finite-`N` enumeration is used. -/
theorem manufactured_pair_protected_repair_outcomes
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodic w (g, B.activatedState) ∨
    (∃ before p x after contact fresh path,
      A.orientedRoute B.activatedState =
        before ++ (p, x) :: after ∧
      PhysicalTrace w (g, B.activatedState) before (p, contact) ∧
      PathGrooves B.toSupported.paths contact ∧
      p % 3 = 0 ∧
      B.activatedState (p / 3) ≠ B.baseState (p / 3) ∧
      contact (p / 3) = B.activatedState (p / 3) ∧
      path ∈ B.toSupported.paths ∧ (fresh, p) ∈ path ∧
      arrive contact p = (fresh, contact) ∧ fresh ≠ x ∧
      (p, fresh) ∈ B.orientedRoute contact) ∨
    (∃ approach p x suffix u v path old oriented repaired,
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
      arrive repaired oriented.2 = (oriented.1, repaired)) ∨
    ∃ finalState,
      PhysicalTrace w (g, B.activatedState)
        (A.orientedRoute B.activatedState)
        (A.orientedFinish B.activatedState, finalState) ∧
      PathGrooves A.toSupported.paths finalState ∧
      PathGrooves B.toSupported.paths finalState := by
  rcases A.repair_current_route_preserving_until_conflict
      B.baseState B.activatedState hA hB with hfacing | hrest
  · obtain ⟨before, p, x, after, contact, other,
        hsplit, hprefix, hBcontact, hp, hchange,
        hcontact, harrive, hother⟩ := hfacing
    rcases B.facing_exit_matches_activation_passage
        hchange hcontact hp harrive with hreturn | hexploration
    · left
      exact B.return_change_facing_eventuallyPeriodic
        hsplit (A.orientedRoute_simple B.activatedState)
        hprefix hBcontact hp hreturn.1 hreturn.2
    · obtain ⟨oldApproach, fresh, oldSuffix, oldU, oldV, path,
          _holdSplit, _holdSwitch, _holdTrace, _holdArrive,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases B.protected_facing_contact_periodic_or_forward
          hsplit (A.orientedRoute_simple B.activatedState)
          hprefix hBcontact hpath hold harriveFresh with
        hperiodic | hforward
      · exact Or.inl hperiodic
      · exact Or.inr (Or.inl ⟨before, p, x, after,
          contact, fresh, path, hsplit, hprefix, hBcontact, hp,
          hchange, by simpa [passageSwitch] using hcontact,
          hpath, hold, harriveFresh,
          by simpa [hotherFresh] using hother,
          hforward⟩)
  · rcases hrest with hchanged | hcomplete
    · obtain ⟨approach, p, x, suffix, u, v, path, old,
          hsplit, hprefix, hBu, harrive,
          hpath, hold, hswitch, hchange⟩ := hchanged
      rcases B.protected_changed_contact_periodic_or_forward
          hsplit (A.orientedRoute_simple B.activatedState)
          hprefix hBu harrive hpath hold hswitch hchange with
        hperiodic | hforward
      · exact Or.inl hperiodic
      · obtain ⟨oriented, repaired, horiented, horientedGroove,
            horientedSwitch, hforwardExit, hrepair,
            hgroove⟩ := hforward
        exact Or.inr (Or.inr (Or.inl
          ⟨approach, p, x, suffix, u, v, path, old,
            oriented, repaired, hsplit, hprefix, hBu, harrive,
            hpath, hold, hswitch, hchange, horiented,
            horientedGroove, horientedSwitch, hforwardExit,
            hrepair, hgroove⟩))
    · exact Or.inr (Or.inr (Or.inr hcomplete))

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
      p % 3 = 0 ∧
      arrive contact p = (fresh, contact) ∧ fresh ≠ x ∧
      (fresh, p) ∈ R.candy ∧
      contact R.actionSwitch = bval R.secondArm ∧
      (p, fresh) ∈
        (ManufacturedReflector.flip R).orientedRoute contact := by
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
          rfl, hsplit, hprefix, hpaths, hp, harrive, hne,
          hold, hsecond, hforward⟩

/-- Once a forward facing merge enters the reversed candy of a flip
reflector, the remaining suffix absorbs the reflector's action flip.  Starting
at the merge stem in either the selected state or its action-flipped state,
the train reaches the far boundary in the latter state.

The proof is entirely local.  The remaining reversed candy avoids the action
switch, so it replays in both states.  Its final trailing visit to `firstArm`
then either makes the action flip or finds it already made, after which the
old runway is retraced. -/
theorem ManufacturedFlipReflector.reverse_candy_suffix_absorbs
    {w : Wiring} {e g : Nat}
    (R : ManufacturedFlipReflector w e g)
    (contact : Tongues)
    (hpaths : PathGrooves [R.runway, R.candy] contact)
    (hsecond : contact R.actionSwitch = bval R.secondArm)
    {before after : List Passage} {fresh p : Nat}
    (hoccurs : R.candy = before ++ (fresh, p) :: after) :
    let alternate := flipAt contact R.actionSwitch
    ∃ travel, 0 < travel ∧
      stepN w travel (p, contact) = some (g, alternate) ∧
      stepN w travel (p, alternate) = some (g, alternate) := by
  have hopp : bval R.secondArm = !(bval R.firstArm) :=
    branch_values_opposite R.firstArm_branch R.secondArm_branch
      (R.firstArm_switch.trans R.secondArm_switch.symm) R.arms_ne
  have hnotFirst :
      contact R.actionSwitch ≠ bval R.firstArm := by
    intro hfirst
    have heq : bval R.firstArm = bval R.secondArm :=
      hfirst.symm.trans hsecond
    rw [hopp] at heq
    cases hvalue : bval R.firstArm <;> simp [hvalue] at heq
  let alternate := flipAt contact R.actionSwitch
  have hfirstAlternate :
      alternate R.actionSwitch = bval R.firstArm := by
    simp [alternate, flipAt, hsecond, hopp]
  have hpathsAlternate :
      PathGrooves [R.runway, R.candy] alternate := by
    dsimp [alternate]
    change PathGrooves [R.runway, R.candy]
      ((LocalAction.flip R.actionSwitch).apply contact)
    exact hpaths.after_avoiding_action R.support_foreign
  let lead := R.runway ++
    (R.mouth, R.secondArm) :: reversePassages after
  let candyTail := reversePassages (before ++ [(fresh, p)])
  have hrouteSplit :
      (ManufacturedReflector.flip R).orientedRoute contact =
        lead ++ candyTail := by
    dsimp [lead, candyTail]
    simp [ManufacturedReflector.orientedRoute, hnotFirst,
      hoccurs, reversePassages_append, reversePassages,
      List.append_assoc]
  have hroute :=
    (ManufacturedReflector.flip R).orientedRoute_trace contact hpaths
  rw [hrouteSplit] at hroute
  obtain ⟨middle, hlead, htail⟩ := hroute.split_append
  have hprefixData := R.reverse_prefix_to_candy_occurrence
    contact hpaths hsecond hoccurs
  have hleadExpected :
      PhysicalTrace w (e, contact) lead (p, contact) := by
    simpa [lead] using hprefixData.1
  have hmiddle : middle = (p, contact) := by
    have h₁ := hlead.sound
    have h₂ := hleadExpected.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  have htailContact :
      PhysicalTrace w (p, contact) candyTail (R.firstArm, contact) := by
    simpa [ManufacturedReflector.orientedFinish, hnotFirst] using htail
  have htailForeign : ∀ passage ∈ candyTail,
      passageSwitch passage ≠ R.actionSwitch := by
    intro passage hpassage
    dsimp [candyTail] at hpassage
    obtain ⟨old, holdSegment, hpassageEq⟩ :=
      source_of_mem_reversePassages hpassage
    subst passage
    have holdCandy : old ∈ R.candy := by
      rw [hoccurs]
      rcases List.mem_append.mp holdSegment with holdBefore | holdLast
      · exact List.mem_append_left ((fresh, p) :: after) holdBefore
      · simp only [List.mem_singleton] at holdLast
        subst old
        exact List.mem_append_right before List.mem_cons_self
    have havoid := R.support_foreign R.candy (by simp) old holdCandy
    have hexit := R.candyTrace.passage_exit_switch old
      (List.mem_cons_of_mem _ holdCandy)
    have hswitch :
        passageSwitch (old.2, old.1) = passageSwitch old := by
      simp only [passageSwitch]
      exact hexit
    rw [hswitch]
    exact havoid
  have htailAlternate :
      PhysicalTrace w (p, alternate) candyTail
        (R.firstArm, alternate) :=
    htailContact.flip_unvisited htailForeign
  have hfirstGrooveAlternate :
      arrive alternate R.firstArm = (R.mouth, alternate) :=
    R.firstArm_groove_of_selected alternate hfirstAlternate
  have hrunwayAlternate : PassagesGrooved alternate R.runway :=
    (pathGrooves_pair.mp hpathsAlternate).1
  have hreturnAlternate :
      PhysicalTrace w (R.firstArm, alternate)
        ((R.firstArm, R.mouth) :: reversePassages R.runway)
        (g, alternate) :=
    physicalTrace_contact_retraces_prefix R.runwayTrace
      hrunwayAlternate R.entryEdge hfirstGrooveAlternate
  have hflipBack : flipAt alternate R.actionSwitch = contact := by
    dsimp [alternate]
    exact flipAt_flipAt contact R.actionSwitch
  have hfirstContact :
      arrive contact R.firstArm = (R.mouth, alternate) := by
    have hrepair := flipped_passage_forward_trailing
      hfirstGrooveAlternate R.firstArm_branch
    rw [R.firstArm_switch, hflipBack] at hrepair
    exact hrepair
  have hreturnContact :
      PhysicalTrace w (R.firstArm, contact)
        ((R.firstArm, R.mouth) :: reversePassages R.runway)
        (g, alternate) :=
    physicalTrace_contact_retraces_prefix R.runwayTrace
      hrunwayAlternate R.entryEdge hfirstContact
  let journey := candyTail ++
    (R.firstArm, R.mouth) :: reversePassages R.runway
  have hjourneyContact :
      PhysicalTrace w (p, contact) journey (g, alternate) := by
    simpa [journey] using htailContact.append hreturnContact
  have hjourneyAlternate :
      PhysicalTrace w (p, alternate) journey (g, alternate) := by
    simpa [journey] using htailAlternate.append hreturnAlternate
  refine ⟨journey.length, ?_, hjourneyContact.sound,
    hjourneyAlternate.sound⟩
  dsimp [journey]
  simp only [List.length_append, List.length_cons]
  omega

/-- The apparent no-change forward residual is not a residual.  Its approach
and the absorbing reverse-candy suffix form a period after at most one local
repair of the protected reflector's action tongue. -/
theorem ManufacturedReflector.FacingForwardMerge.eventuallyPeriodic
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.FacingForwardMerge B) :
    EventuallyPeriodic w (g, B.activatedState) := by
  obtain ⟨R, before, p, x, after, contact, fresh,
      hB, hrouteSplit, hprefix, hpaths, _hp, _harrive,
      _hfreshNe, hcandyMem, hsecond, _hforward⟩ :=
    hmerge.flip_candy
  subst B
  obtain ⟨candyBefore, candyAfter, hcandySplit⟩ :=
    List.append_of_mem hcandyMem
  let alternate := flipAt contact R.actionSwitch
  obtain ⟨tailTravel, htailPositive, htailContact,
      htailAlternate⟩ :=
    R.reverse_candy_suffix_absorbs contact hpaths hsecond hcandySplit
  have hrouteSimple :=
    A.orientedRoute_simple
      (ManufacturedReflector.flip R).activatedState
  rw [hrouteSplit] at hrouteSimple
  have hbeforeSimple : SwitchSimple before := by
    unfold SwitchSimple at hrouteSimple ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hbeforeGrooved : PassagesGrooved contact before :=
    hprefix.grooved_of_switchSimple hbeforeSimple
  have hprefixContact :
      PhysicalTrace w (g, contact) before (p, contact) :=
    hprefix.replay_grooved contact hbeforeGrooved
  let loopSteps := before.length + tailTravel
  have hlead :
      stepN w loopSteps
        (g, (ManufacturedReflector.flip R).activatedState) =
          some (g, alternate) := by
    dsimp [loopSteps]
    rw [stepN_add, hprefix.sound]
    exact htailContact
  have hcontactToAlternate :
      stepN w loopSteps (g, contact) = some (g, alternate) := by
    dsimp [loopSteps]
    rw [stepN_add, hprefixContact.sound]
    exact htailContact
  have hloopPositive : 0 < loopSteps := by
    dsimp [loopSteps]
    omega
  by_cases htouch : ∃ passage ∈ before,
      passageSwitch passage = R.actionSwitch
  · obtain ⟨passage, hpassage, hswitch⟩ := htouch
    obtain ⟨prior, later, hbeforeSplit⟩ :=
      List.append_of_mem hpassage
    have hdecomp : before.length =
        prior.length + 1 + later.length := by
      rw [hbeforeSplit]
      simp only [List.length_append, List.length_cons]
      omega
    have hnormal :
        stepN w before.length (g, contact) = some (p, contact) :=
      hprefixContact.sound
    rcases runway_fault_dichotomy_general R contact hpaths
        hprefixContact hbeforeGrooved hbeforeSimple passage
        hbeforeSplit hswitch hdecomp hnormal with
      hcapture | hrepair
    · obtain ⟨captureTravel, hcapture⟩ := hcapture
      have hperiod :
          stepN w (captureTravel + loopSteps) (g, alternate) =
            some (g, alternate) := by
        rw [stepN_add, hcapture]
        exact hcontactToAlternate
      have hperiodic : EventuallyPeriodic w (g, alternate) :=
        eventuallyPeriodic_of_period (by omega) hperiod
      exact hperiodic.prepend hlead
    · have hperiod :
          stepN w loopSteps (g, alternate) = some (g, alternate) := by
        dsimp [loopSteps]
        rw [stepN_add, hrepair]
        exact htailContact
      have hperiodic : EventuallyPeriodic w (g, alternate) :=
        eventuallyPeriodic_of_period hloopPositive hperiod
      exact hperiodic.prepend hlead
  · have hforeign : ∀ passage ∈ before,
        passageSwitch passage ≠ R.actionSwitch := by
      intro passage hpassage hswitch
      exact htouch ⟨passage, hpassage, hswitch⟩
    have hprefixAlternate :
        PhysicalTrace w (g, alternate) before (p, alternate) :=
      hprefixContact.flip_unvisited hforeign
    have hperiod :
        stepN w loopSteps (g, alternate) = some (g, alternate) := by
      dsimp [loopSteps]
      rw [stepN_add, hprefixAlternate.sound]
      exact htailAlternate
    have hperiodic : EventuallyPeriodic w (g, alternate) :=
      eventuallyPeriodic_of_period hloopPositive hperiod
    exact hperiodic.prepend hlead

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

/-- A state-changing forward merge manufactures a concrete new lobe at the
contact switch even when the fresh route is an arbitrary selected route being
repaired (rather than the exploration that originally manufactured a
reflector).  Its candy retraces the old protected-route prefix, crosses the
boundary edge, and replays the fresh approach.  From the lobe's outside edge,
the untouched suffix of the old reflector still reaches the original
boundary and applies the old reflector action. -/
theorem ManufacturedReflector.ChangedForwardMerge.spliced_lobe_reflector
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B) :
    ∃ (entry mouth returnPort outside : Nat) (candy : List Passage)
        (state : Tongues) (leadSteps tailSteps : Nat),
      (entry, mouth) ∈ B.orientedRoute state ∧
      entry % 3 ≠ 0 ∧ mouth % 3 = 0 ∧
      w.link mouth = some outside ∧
      entry ≠ returnPort ∧
      PassagesGrooved state ((mouth, entry) :: candy) ∧
      PhysicalTrace w (mouth, state) ((mouth, entry) :: candy)
        (returnPort, state) ∧
      arrive state returnPort =
        (mouth, flipAt state (mouth / 3)) ∧
      PathGrooves B.toSupported.paths state ∧
      PassagesGrooved state candy ∧
      (∀ passage ∈ candy,
        passageSwitch passage ≠ mouth / 3) ∧
      IsReflector w mouth outside (candy.length + 2)
        (fun state => PassagesGrooved state candy)
        (fun state => flipAt state (mouth / 3)) ∧
      stepN w leadSteps (g, B.activatedState) =
        some (outside, flipAt state (mouth / 3)) ∧
      stepN w tailSteps (outside, state) =
        some (g, B.toSupported.action.apply state) := by
  obtain ⟨approach, p, x, suffix, u, v, _path, _old,
      oriented, repaired, hsplit, happroach, hpaths, harrive,
      _hpath, _hold, _holdSwitch, hchanged, horiented,
      horientedGroove, _horientedSwitch, hforward,
      hrepair, hrestored⟩ := hmerge
  rcases oriented with ⟨a, s⟩
  simp only at horiented horientedGroove hforward hrepair hrestored
  subst x
  obtain ⟨hpBranch, hsEq, _hv, _hback⟩ :=
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
  have hroute := B.orientedRoute_trace u hpaths
  have hrouteSimple := B.orientedRoute_simple u
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hOldPrefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hrouteSplit hrouteGrooved hrouteSimple
  have hOldPrefixGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hrouteSplit]
      exact List.mem_append_left _ hp)

  have hApproachSimple : SwitchSimple approach := by
    have hsimple :=
      A.orientedRoute_simple
        (ManufacturedReflector.activatedState B)
    unfold SwitchSimple at hsimple ⊢
    rw [hsplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple hApproachSimple
  have hApproachForeign : ∀ passage ∈ approach,
      passageSwitch passage ≠ p / 3 := by
    have hsimple :=
      A.orientedRoute_simple
        (ManufacturedReflector.activatedState B)
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
    · exact reversePassages_grooved hOldPrefixGrooved passage hold
    · exact hApproachGrooved passage hnew
  have hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ s / 3 := by
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
    hOldPrefixData.1 hOldPrefixGrooved B.entryEdge horientedGroove
  have hforwardTrace :=
    happroach.replay_grooved u hApproachGrooved
  have hsplice :
      PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy, List.append_assoc] using hback.append hforwardTrace
  have hSpliceGrooved :
      PassagesGrooved u ((s, a) :: candy) := by
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
  | @cons _ _ outside _ oldAfter _ _ _hOldArrive hmouth _oldRest =>
      have hcontactTrace : PhysicalTrace w (a, u) [(a, s)]
          (outside, u) :=
        PhysicalTrace.cons (groove_forward horientedGroove) hmouth
          (PhysicalTrace.nil _)
      have hlead := hOldPrefixData.1.append hcontactTrace
      have hleadSplit : B.orientedRoute u =
          (oldPrefix ++ [(a, s)]) ++ oldTail := by
        rw [hrouteSplit]
        simp [List.append_assoc]
      obtain ⟨tailSteps, _hlen, hcomplete⟩ :=
        B.complete_after_oriented_prefix u hpaths hleadSplit hlead
      have hflip : v = flipAt u (s / 3) := by
        have hv := changed_arrival_eq_flipAt harrive hchanged
        simpa [hsp] using hv
      have hone : stepN w 1 (p, u) = some (outside, v) := by
        simp [stepN, step, harrive, hmouth]
      have hreach : stepN w (approach.length + 1)
          (g, B.activatedState) =
          some (outside, flipAt u (s / 3)) := by
        rw [stepN_add, happroach.sound]
        simp only [Option.bind_some]
        rw [hone, hflip]
      have hcrossed : arrive u p =
          (s, flipAt u (s / 3)) := by
        rw [harrive, hflip]
      refine ⟨a, s, p, outside, candy, u, approach.length + 1,
        tailSteps, horiented, haBranch, hsStem, hmouth,
        hap, hSpliceGrooved, hsplice, hcrossed, hpaths,
        hCandyGrooved, hCandyForeign, ?_, hreach, hcomplete⟩
      exact stem_lobe_isReflector_foreign w candy
        hsStem haBranch hpBranch hsa hsp hap hCandyForeign
        hsplice.linked hsplice.last_link hmouth

/-- Flipping the switch of one *trailing* passage on a manufactured
reflector's selected route cannot damage the reflector.  The flipped run
replays the untouched prefix, the trailing passage restores its own groove,
and the deterministic suffix completes with the reflector's original local
action.  This is the state-repair half of the remaining forward splice. -/
theorem ManufacturedReflector.single_flipped_trailing_repairs
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hpaths : PathGrooves B.toSupported.paths state)
    {oriented : Passage}
    (horiented : oriented ∈ B.orientedRoute state)
    (hbranch : oriented.1 % 3 ≠ 0) :
    stepN w B.toSupported.travel
        (e, flipAt state (passageSwitch oriented)) =
      some (g, B.toSupported.action.apply state) := by
  rcases oriented with ⟨p, x⟩
  simp only [passageSwitch] at horiented ⊢
  obtain ⟨before, after, hsplit⟩ :=
    List.append_of_mem horiented
  have hroute := B.orientedRoute_trace state hpaths
  have hsimple := B.orientedRoute_simple state
  have hgrooved := hroute.grooved_of_switchSimple hsimple
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hsplit hgrooved hsimple
  have hprefix := hprefixData.1
  have hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ p / 3 := by
    intro passage hpassage
    exact hprefixData.2 passage hpassage
  have hforward : arrive state p = (x, state) :=
    groove_forward (hgrooved (p, x) (by
      rw [hsplit]
      exact List.mem_append_right before List.mem_cons_self))
  have hroute' := hroute
  rw [hsplit] at hroute'
  obtain ⟨middle, hbefore, hafter⟩ := hroute'.split_append
  have hmiddle : middle = (p, state) := by
    have h₁ := hbefore.sound
    have h₂ := hprefix.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hafter with
  | @cons _ _ outside _ next _ _ _ hlink tail =>
      have hone : PhysicalTrace w (p, state) [(p, x)]
          (outside, state) :=
        PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
      have hlead := hprefix.append hone
      have hleadSplit : B.orientedRoute state =
          (before ++ [(p, x)]) ++ after := by
        rw [hsplit]
        simp [List.append_assoc]
      obtain ⟨tailSteps, hlength, hcomplete⟩ :=
        B.complete_after_oriented_prefix state hpaths
          hleadSplit hlead
      have hrepair := flipped_prefix_trailing_then
        hprefix hforeign rfl hbranch hforward hlink hcomplete
      have htotal : B.toSupported.travel =
          before.length + 1 + tailSteps := by
        rw [hlength]
        simp
      rwa [← htotal] at hrepair

/-- A strict suffix of the runway of a degenerate identity reflector is
again an identity reflector.  If `(p,x)` is the discarded runway passage,
the new reflector starts just beyond `x` and ends at `x`; moreover its whole
support is foreign to the discarded passage's switch.  This is the exact
opposite-facing reflector needed to compose with a lobe spliced at `x`. -/
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
  change PathGrooves [R.runway, [(R.mouth, R.arm)]] state at hpaths
  have hrunwayGrooved := (pathGrooves_pair.mp hpaths).1
  have hcoreGrooved := (pathGrooves_pair.mp hpaths).2
  have hafterGrooved : PassagesGrooved state after := by
    intro passage hpassage
    exact hrunwayGrooved passage (by
      rw [hsplit]
      exact List.mem_append_right before
        (List.mem_cons_of_mem _ hpassage))
  have hsimpleRunway : SwitchSimple R.runway := by
    have hs := R.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hrun := R.runway_trace state hrunwayGrooved
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    hrun hsplit hrunwayGrooved hsimpleRunway
  have hrun' := hrun
  rw [hsplit] at hrun'
  obtain ⟨middle, hbefore, hafter⟩ := hrun'.split_append
  have hmiddle : middle = (p, state) := by
    have h₁ := hbefore.sound
    have h₂ := hprefixData.1.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hafter with
  | @cons _ _ next _ nextState _ _ harrive hlink tail =>
      have hforward : arrive state p = (x, state) :=
        groove_forward (hrunwayGrooved (p, x) (by
          rw [hsplit]
          exact List.mem_append_right before List.mem_cons_self))
      have hnextState : nextState = state := by
        rw [harrive] at hforward
        exact congrArg Prod.snd hforward
      subst nextState
      have hnext : next = outside := by
        rw [houtside] at hlink
        exact (Option.some.inj hlink).symm
      subst next
      have hcoreBack : arrive state R.arm = (R.mouth, state) :=
        passagesGrooved_singleton.mp hcoreGrooved
      have hcoreForward : arrive state R.mouth = (R.arm, state) :=
        groove_forward hcoreBack
      have hcore : PhysicalTrace w (R.mouth, state)
          [(R.mouth, R.arm)] (R.arm, state) :=
        PhysicalTrace.cons hcoreForward R.selfLink
          (PhysicalTrace.nil _)
      have hs := R.simple
      unfold SwitchSimple at hs
      rw [hsplit] at hs
      simp only [List.map_append, List.map_cons, List.map_nil] at hs
      have hs' :
          (before.map passageSwitch ++
            passageSwitch (p, x) ::
              (after.map passageSwitch ++
                [passageSwitch (R.mouth, R.arm)])).Nodup := by
        simpa [List.append_assoc] using hs
      have hrestNodup :
          (passageSwitch (p, x) ::
            (after.map passageSwitch ++
              [passageSwitch (R.mouth, R.arm)])).Nodup :=
        (List.nodup_append.mp hs').2.1
      have htailSimple :
          SwitchSimple (after ++ [(R.mouth, R.arm)]) := by
        unfold SwitchSimple
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact (List.nodup_cons.mp hrestNodup).2
      have hdiscardedForeign :
          passageSwitch (p, x) ∉
            after.map passageSwitch ++
              [passageSwitch (R.mouth, R.arm)] :=
        (List.nodup_cons.mp hrestNodup).1
      have havoid :
          (LocalAction.flip (p / 3)).Avoids
            [after, [(R.mouth, R.arm)]] := by
        intro path hpath passage hpassage
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
        apply fun hEq => hdiscardedForeign (by
          have hkey : passageSwitch passage =
              passageSwitch (p, x) := by
            simpa [passageSwitch] using hEq
          rcases hpath with rfl | rfl
          · apply List.mem_append_left
            apply List.mem_map.mpr
            exact ⟨passage, hpassage, hkey⟩
          · simp only [List.mem_singleton] at hpassage
            subst passage
            apply List.mem_append_right
            simp [hkey])
      let C : ManufacturedStayReflector w outside x := {
        base := state
        mouthState := state
        returnState := state
        runway := after
        mouth := R.mouth
        arm := R.arm
        runwayTrace := tail
        coreTrace := hcore
        simple := htailSimple
        stemEndpoint := R.stemEndpoint
        selfLink := R.selfLink
        entryEdge := houtside
      }
      refine ⟨C, ?_, ?_⟩
      · change PathGrooves [after, [(R.mouth, R.arm)]] state
        exact pathGrooves_pair.mpr ⟨hafterGrooved, hcoreGrooved⟩
      · change (LocalAction.flip (p / 3)).Avoids
          [after, [(R.mouth, R.arm)]]
        exact havoid

/-- A strict suffix of a flip reflector's runway is again a manufactured
flip reflector.  The candy is oriented according to the current tongue, so
the shortened reflector is immediately usable in `state`.  Its support is
foreign to the discarded runway switch. -/
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
  change PathGrooves [R.runway, R.candy] state at hpaths
  have hrunwayGrooved := (pathGrooves_pair.mp hpaths).1
  have hCandyGrooved := (pathGrooves_pair.mp hpaths).2
  have hafterGrooved : PassagesGrooved state after := by
    intro passage hpassage
    exact hrunwayGrooved passage (by
      rw [hsplit]
      exact List.mem_append_right before
        (List.mem_cons_of_mem _ hpassage))
  have hdiscardedOldForeign : p / 3 ≠ R.actionSwitch := by
    have hforeign := R.support_foreign R.runway (by simp)
      (p, x) (by
        rw [hsplit]
        exact List.mem_append_right before List.mem_cons_self)
    simpa [passageSwitch] using hforeign
  have hsimpleRunway : SwitchSimple R.runway := by
    have hs := R.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hrun := R.runway_trace state hrunwayGrooved
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    hrun hsplit hrunwayGrooved hsimpleRunway
  have hrun' := hrun
  rw [hsplit] at hrun'
  obtain ⟨middle, hbefore, hafter⟩ := hrun'.split_append
  have hmiddle : middle = (p, state) := by
    have h₁ := hbefore.sound
    have h₂ := hprefixData.1.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hafter with
  | @cons _ _ next _ nextState _ _ harrive hlink tail =>
      have hforward : arrive state p = (x, state) :=
        groove_forward (hrunwayGrooved (p, x) (by
          rw [hsplit]
          exact List.mem_append_right before List.mem_cons_self))
      have hnextState : nextState = state := by
        rw [harrive] at hforward
        exact congrArg Prod.snd hforward
      subst nextState
      have hnext : next = outside := by
        rw [houtside] at hlink
        exact (Option.some.inj hlink).symm
      subst next
      rcases R.selected_arm state with hselected | hselected
      · have hcandy :=
          R.candy_forward_trace state hselected hCandyGrooved
        have hopp : bval R.secondArm = !(state R.actionSwitch) := by
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
        have hcrossed : arrive state R.secondArm =
            (R.mouth, flipAt state R.actionSwitch) := by
          simp [arrive, R.secondArm_branch, hstem, hpin]
        have hs := R.simple
        unfold SwitchSimple at hs
        rw [hsplit] at hs
        simp only [List.map_append, List.map_cons] at hs
        have hs' :
            (before.map passageSwitch ++
              passageSwitch (p, x) ::
                (after.map passageSwitch ++
                  passageSwitch (R.mouth, R.firstArm) ::
                    R.candy.map passageSwitch)).Nodup := by
          simpa [List.append_assoc] using hs
        have hrestNodup :
            (passageSwitch (p, x) ::
              (after.map passageSwitch ++
                passageSwitch (R.mouth, R.firstArm) ::
                  R.candy.map passageSwitch)).Nodup :=
          (List.nodup_append.mp hs').2.1
        have htailSimple : SwitchSimple
            (after ++ (R.mouth, R.firstArm) :: R.candy) := by
          unfold SwitchSimple
          simp only [List.map_append, List.map_cons]
          exact (List.nodup_cons.mp hrestNodup).2
        have hdiscardedForeign :=
          (List.nodup_cons.mp hrestNodup).1
        have havoid : (LocalAction.flip (p / 3)).Avoids
            [after, R.candy] := by
          intro path hpath passage hpassage
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
          intro hEq
          apply hdiscardedForeign
          have hkey : passageSwitch passage =
              passageSwitch (p, x) := by
            simpa [passageSwitch] using hEq
          rcases hpath with rfl | rfl
          · apply List.mem_append_left
            exact List.mem_map.mpr ⟨passage, hpassage, hkey⟩
          · apply List.mem_append_right
            exact List.mem_cons_of_mem _
              (List.mem_map.mpr ⟨passage, hpassage, hkey⟩)
        let C : ManufacturedFlipReflector w outside x := {
          base := state
          mouthState := state
          returnState := state
          afterReturn := flipAt state R.actionSwitch
          runway := after
          candy := R.candy
          mouth := R.mouth
          firstArm := R.firstArm
          secondArm := R.secondArm
          runwayTrace := tail
          candyTrace := hcandy
          simple := htailSimple
          crossed := hcrossed
          arms_ne := R.arms_ne
          entryEdge := houtside
        }
        refine ⟨C, rfl, hdiscardedOldForeign, ?_, ?_⟩
        · change PathGrooves [after, R.candy] state
          exact pathGrooves_pair.mpr ⟨hafterGrooved, hCandyGrooved⟩
        · change (LocalAction.flip (p / 3)).Avoids
            [after, R.candy]
          exact havoid
      · have hreverseGrooved :
            PassagesGrooved state (reversePassages R.candy) := by
          intro passage hpassage
          exact reversePassages_grooved hCandyGrooved passage hpassage
        have hcandy :=
          R.candy_reverse_trace state hselected hCandyGrooved
        have hopp : bval R.firstArm = !(state R.actionSwitch) := by
          rw [hselected]
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
        have hcrossed : arrive state R.firstArm =
            (R.mouth, flipAt state R.actionSwitch) := by
          simp [arrive, R.firstArm_branch, hstem, hpin]
        have hs := R.reverse_support_simple
        unfold SwitchSimple at hs
        rw [hsplit] at hs
        simp only [List.map_append, List.map_cons] at hs
        have hs' :
            (before.map passageSwitch ++
              passageSwitch (p, x) ::
                (after.map passageSwitch ++
                  passageSwitch (R.mouth, R.secondArm) ::
                    (reversePassages R.candy).map
                      passageSwitch)).Nodup := by
          simpa [List.append_assoc] using hs
        have hrestNodup :
            (passageSwitch (p, x) ::
              (after.map passageSwitch ++
                passageSwitch (R.mouth, R.secondArm) ::
                  (reversePassages R.candy).map
                    passageSwitch)).Nodup :=
          (List.nodup_append.mp hs').2.1
        have htailSimple : SwitchSimple
            (after ++
              (R.mouth, R.secondArm) ::
                reversePassages R.candy) := by
          unfold SwitchSimple
          simp only [List.map_append, List.map_cons]
          exact (List.nodup_cons.mp hrestNodup).2
        have hdiscardedForeign :=
          (List.nodup_cons.mp hrestNodup).1
        have havoid : (LocalAction.flip (p / 3)).Avoids
            [after, reversePassages R.candy] := by
          intro path hpath passage hpassage
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpath
          intro hEq
          apply hdiscardedForeign
          have hkey : passageSwitch passage =
              passageSwitch (p, x) := by
            simpa [passageSwitch] using hEq
          rcases hpath with rfl | rfl
          · apply List.mem_append_left
            exact List.mem_map.mpr ⟨passage, hpassage, hkey⟩
          · apply List.mem_append_right
            exact List.mem_cons_of_mem _
              (List.mem_map.mpr ⟨passage, hpassage, hkey⟩)
        let C : ManufacturedFlipReflector w outside x := {
          base := state
          mouthState := state
          returnState := state
          afterReturn := flipAt state R.actionSwitch
          runway := after
          candy := reversePassages R.candy
          mouth := R.mouth
          firstArm := R.secondArm
          secondArm := R.firstArm
          runwayTrace := tail
          candyTrace := hcandy
          simple := htailSimple
          crossed := hcrossed
          arms_ne := Ne.symm R.arms_ne
          entryEdge := houtside
        }
        refine ⟨C, rfl, hdiscardedOldForeign, ?_, ?_⟩
        · change PathGrooves
            [after, reversePassages R.candy] state
          exact pathGrooves_pair.mpr
            ⟨hafterGrooved, hreverseGrooved⟩
        · change (LocalAction.flip (p / 3)).Avoids
            [after, reversePassages R.candy]
          exact havoid

/-- Generic theta half for an arbitrary (not necessarily switch-simple)
flip lobe opposite a manufactured flip reflector.  If the old action switch
occurs on the lobe interior, the first such occurrence is either facing and
is captured by the old lobe, or trailing and repairs itself.  In both cases
one macro-step applies exactly the new lobe's flip. -/
theorem manufactured_flip_arbitrary_lobe_theta_half
    {w : Wiring} {outside mouth entry returnPort : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    {candy : List Passage}
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hnormal : stepN w (candy.length + 2) (mouth, state) =
      some (outside, flipAt state (mouth / 3)))
    (hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch) :
    ∃ travel, 0 < travel ∧
      stepN w travel (outside, state) =
        some (outside, flipAt state (mouth / 3)) := by
  let route := (mouth, entry) :: candy
  have hrouteContact : ∃ passage ∈ route,
      passageSwitch passage = C.actionSwitch := by
    obtain ⟨passage, hpassage, hswitch⟩ := hcontact
    exact ⟨passage, List.mem_cons_of_mem _ hpassage, hswitch⟩
  obtain ⟨before, target, after, hsplit, hbeforeForeign,
      htargetSwitch⟩ :=
    exists_first_satisfying_split
      (fun passage => passageSwitch passage = C.actionSwitch)
      route hrouteContact
  have htrace' := htrace
  change route = before ++ target :: after at hsplit
  change PhysicalTrace w (mouth, state) route
    (returnPort, state) at htrace'
  rw [hsplit] at htrace'
  obtain ⟨middle, hbeforeRaw, hrest⟩ := htrace'.split_append
  have hmiddlePort : middle.1 = target.1 :=
    hrest.head_arrive.1
  have hbeforeGrooved : PassagesGrooved state before := by
    intro passage hpassage
    exact hgrooved passage (by
      change passage ∈ route
      rw [hsplit]
      exact List.mem_append_left _ hpassage)
  have hprefix : PhysicalTrace w (mouth, state) before
      (target.1, state) := by
    have hreplay := hbeforeRaw.replay_grooved state hbeforeGrooved
    simpa [hmiddlePort] using hreplay
  have hforeign : ∀ passage ∈ before,
      passageSwitch passage ≠ C.actionSwitch := by
    intro passage hpassage
    exact hbeforeForeign passage hpassage
  have htargetMem : target ∈ route := by
    rw [hsplit]
    exact List.mem_append_right before List.mem_cons_self
  have hstem := htrace.passage_stem_endpoint target htargetMem
  rcases target with ⟨p, x⟩
  simp only [passageSwitch] at htargetSwitch
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  have hOldMouth : C.mouth = 3 * C.actionSwitch := by
    have hm := C.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  have hnormalRoute :
      stepN w (candy.length + 2) (mouth, state) =
        some (outside, flipAt state (mouth / 3)) := hnormal
  have hfault : ∃ faultTravel,
      stepN w faultTravel
          (mouth, flipAt state C.actionSwitch) =
        some (outside, flipAt state (mouth / 3)) := by
    rcases hstem with hpStem | hxStem
    · have hpMouth : p = C.mouth := by omega
      clear hpStem
      subst p
      have hcapture := C.capture_from_mouth state
        (pathGrooves_pair.mp hCpaths).1
        (pathGrooves_pair.mp hCpaths).2
      have hcaptured := theta_capture_after_unvisited_prefix
        hprefix hforeign hcapture
      refine ⟨before.length +
          (C.candy.length + 2 + C.runway.length) +
            (candy.length + 2), ?_⟩
      rw [stepN_add, hcaptured]
      exact hnormalRoute
    · have hxMouth : x = C.mouth := by omega
      clear hxStem
      subst x
      have htargetGroove : arrive state C.mouth = (p, state) :=
        hgrooved (p, C.mouth) (by
          change (p, C.mouth) ∈ route
          rw [hsplit]
          exact List.mem_append_right before List.mem_cons_self)
      have hforward : arrive state p = (C.mouth, state) :=
        groove_forward htargetGroove
      have hpbranch : p % 3 ≠ 0 := by
        intro hpmod
        have hne := arrive_exit_ne state p
        rw [hforward] at hne
        apply hne
        omega
      obtain ⟨next, hlink⟩ : ∃ next,
          w.link C.mouth = some next := by
        cases after with
        | nil =>
            exact ⟨returnPort, by
              simpa [lastPassageExit] using hrest.last_link⟩
        | cons passage rest =>
            rcases passage with ⟨next, y⟩
            exact ⟨next, hrest.linked.1⟩
      have hone : PhysicalTrace w (p, state) [(p, C.mouth)]
          (next, state) :=
        PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
      have hlead := hprefix.append hone
      let tailSteps := after.length + 1
      have hrouteLength : candy.length + 1 =
          before.length + 1 + after.length := by
        have hlen := congrArg List.length hsplit
        dsimp [route] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      have htotal : candy.length + 2 =
          before.length + 1 + tailSteps := by
        dsimp [tailSteps]
        omega
      have hsuffix : stepN w tailSteps (next, state) =
          some (outside, flipAt state (mouth / 3)) := by
        apply suffix_after_physical_prefix hlead
        · simpa using htotal
        · exact hnormalRoute
      have hrepair := flipped_prefix_trailing_then hprefix
        hforeign htargetSwitch hpbranch hforward hlink hsuffix
      exact ⟨before.length + 1 + tailSteps, hrepair⟩
  obtain ⟨faultTravel, hfault⟩ := hfault
  have hCrun := (C.toSupported.run state hCpaths).1
  change stepN w C.toSupported.travel (outside, state) =
      some (mouth, flipAt state C.actionSwitch) at hCrun
  refine ⟨C.toSupported.travel + faultTravel, ?_, ?_⟩
  · have hCpos : 0 < C.toSupported.travel := by
      change 0 < 2 * C.runway.length + C.candy.length + 2
      omega
    omega
  · rw [stepN_add, hCrun]
    exact hfault

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
    cases hcandy : candy with
    | nil =>
        have htrace' := htrace
        rw [hcandy] at htrace'
        have hlast := htrace'.last_link
        have hbackLink : w.link returnPort = some entry :=
          w.symm _ _ (by
            simpa [lastPassageExit] using hlast)
        simpa [hcandy, reversePassages] using
          (PhysicalTrace.cons hmouthForward hbackLink
            (PhysicalTrace.nil _))
    | cons passage rest =>
        rcases passage with ⟨p, x⟩
        have htrace' := htrace
        rw [hcandy] at htrace'
        have hgrooved' : PassagesGrooved
            (flipAt state (mouth / 3)) ((p, x) :: rest) := by
          simpa [hcandy] using hCandyFlip
        have hfirstLink : w.link entry = some p :=
          htrace'.linked.1
        have hlast :
            w.link (lastPassageExit x rest) = some returnPort := by
          simpa [lastPassageExit] using htrace'.last_link
        have hbackLink :
            w.link returnPort = some (lastPassageExit x rest) :=
          w.symm _ _ hlast
        have hhead : PhysicalTrace w
            (mouth, flipAt state (mouth / 3))
            [(mouth, returnPort)]
            (lastPassageExit x rest,
              flipAt state (mouth / 3)) :=
          PhysicalTrace.cons hmouthForward hbackLink
            (PhysicalTrace.nil _)
        have hreverse := physicalTrace_retrace_linked_passages w
          (flipAt state (mouth / 3)) p x entry rest
          htrace'.linked.2 hgrooved' hfirstLink
        simpa [hcandy, reversePassages] using hhead.append hreverse
  exact ⟨hreverseTrace, hfullReverseGrooved, hrestore⟩

/-- If the old flip action occurs inside an arbitrary opposite lobe, the two
orientation-normalized theta halves form a genuine period.  This theorem is
the non-simple-candy analogue of `manufactured_one_sided_theta_period`. -/
theorem manufactured_flip_arbitrary_lobe_period
    {w : Wiring} {outside mouth entry returnPort : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch) :
    EventuallyPeriodic w
      (outside, flipAt state (mouth / 3)) := by
  have hCandy : PassagesGrooved state candy := by
    intro passage hpassage
    exact hgrooved passage (List.mem_cons_of_mem _ hpassage)
  have hnormal := (hLobe state hCandy).1
  obtain ⟨forwardTravel, hforwardPositive, hforward⟩ :=
    manufactured_flip_arbitrary_lobe_theta_half C state hCpaths
      hgrooved htrace hnormal hcontact
  have hCflip : PathGrooves C.toSupported.paths
      (flipAt state (mouth / 3)) :=
    hCpaths.after_avoiding_action hNewAvoidsC
  have hCandyFlip :
      PassagesGrooved (flipAt state (mouth / 3)) candy :=
    grooved_after_flip_other hCandy hCandyForeign
  obtain ⟨hreverseTrace, hreverseGrooved, _hrestore⟩ :=
    arbitrary_lobe_reverse_trace hentryBranch hentrySwitch
      hgrooved htrace hcrossed hCandyForeign
  have hmap :
      (reversePassages candy).map passageSwitch =
        (candy.map passageSwitch).reverse := by
    cases htrace with
    | @cons _ _ _ _ _ _ _ _ _ tail =>
        exact map_passageSwitch_reversePassages tail
  have hcontactReverse : ∃ passage ∈ reversePassages candy,
      passageSwitch passage = C.actionSwitch := by
    obtain ⟨old, hold, holdSwitch⟩ := hcontact
    have hkeyMem : C.actionSwitch ∈ candy.map passageSwitch :=
      List.mem_map.mpr ⟨old, hold, holdSwitch⟩
    have hreverseKey : C.actionSwitch ∈
        (reversePassages candy).map passageSwitch := by
      rw [hmap]
      exact List.mem_reverse.mpr hkeyMem
    obtain ⟨passage, hpassage, hswitch⟩ :=
      List.mem_map.mp hreverseKey
    exact ⟨passage, hpassage, hswitch⟩
  have hnormalReverse :
      stepN w ((reversePassages candy).length + 2)
        (mouth, flipAt state (mouth / 3)) =
          some (outside,
            flipAt (flipAt state (mouth / 3)) (mouth / 3)) := by
    have hrun :=
      (hLobe (flipAt state (mouth / 3)) hCandyFlip).1
    simpa [reversePassages_length] using hrun
  obtain ⟨reverseTravel, hreversePositive, hreverse⟩ :=
    manufactured_flip_arbitrary_lobe_theta_half C
      (flipAt state (mouth / 3)) hCflip hreverseGrooved
      hreverseTrace hnormalReverse hcontactReverse
  have hreverse' : stepN w reverseTravel
      (outside, flipAt state (mouth / 3)) =
        some (outside, state) := by
    change stepN w reverseTravel
        (outside, flipAt state (mouth / 3)) =
      some (outside,
        flipAt (flipAt state (mouth / 3)) (mouth / 3)) at hreverse
    rw [flipAt_flipAt state (mouth / 3)] at hreverse
    exact hreverse
  have hperiod : stepN w (reverseTravel + forwardTravel)
      (outside, flipAt state (mouth / 3)) =
        some (outside, flipAt state (mouth / 3)) := by
    rw [stepN_add, hreverse']
    exact hforward
  exact eventuallyPeriodic_of_period (by omega) hperiod

/-- A changed-forward splice through the runway of an old flip reflector is
periodic.  Trimming at the touched passage yields an opposite manufactured
flip reflector.  Disjoint actions give the ordinary paired period; an old
mouth occurrence inside the arbitrary spliced candy is handled by the
orientation-normalized arbitrary-lobe theta period above. -/
theorem manufactured_flip_runway_splice_periodic
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hRpaths : PathGrooves R.toSupported.paths state)
    {entry mouth returnPort outside : Nat} {candy : List Passage}
    (hrunway : (entry, mouth) ∈ R.runway)
    (hmouthLink : w.link mouth = some outside)
    (hentryBranch : entry % 3 ≠ 0)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandy : PassagesGrooved state candy)
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3))) :
    EventuallyPeriodic w
      (outside, flipAt state (mouth / 3)) := by
  obtain ⟨before, after, hsplit⟩ := List.append_of_mem hrunway
  obtain ⟨C, hCAction, _hActionsNe, hCpaths, hNewAvoidsC⟩ :=
    R.suffix_after_runway_passage state hRpaths
      hsplit hmouthLink
  have hentrySwitch : entry / 3 = mouth / 3 := by
    have hheadGroove : arrive state entry = (mouth, state) :=
      hgrooved (mouth, entry) List.mem_cons_self
    have hswitch := arrive_exit_switch state entry
    rw [hheadGroove] at hswitch
    exact hswitch.symm
  have hNewAvoidsC' :
      (LocalAction.flip (mouth / 3)).Avoids
        C.toSupported.paths := by
    simpa [hentrySwitch] using hNewAvoidsC
  by_cases hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch
  · exact manufactured_flip_arbitrary_lobe_period C state hCpaths
      hNewAvoidsC' hentryBranch hentrySwitch hgrooved htrace
      hcrossed hCandyForeign hLobe hcontact
  · let L : SupportedReflector w mouth outside := {
      travel := candy.length + 2
      paths := [candy]
      action := .flip (mouth / 3)
      run := by
        intro current hpaths
        have hCandyCurrent : PassagesGrooved current candy :=
          hpaths candy (by simp)
        obtain ⟨hstep, hnext⟩ := hLobe current hCandyCurrent
        constructor
        · exact hstep
        · intro path hpath
          simp only [List.mem_singleton] at hpath
          subst path
          exact hnext
    }
    have hOldAvoidsL : C.toSupported.action.Avoids L.paths := by
      change (LocalAction.flip C.actionSwitch).Avoids [candy]
      intro path hpath passage hpassage
      simp only [List.mem_singleton] at hpath
      subst path
      intro hEq
      exact hcontact ⟨passage, hpassage, hEq⟩
    have hCflip : PathGrooves C.toSupported.paths
        (flipAt state (mouth / 3)) :=
      hCpaths.after_avoiding_action hNewAvoidsC'
    have hCandyFlip :
        PassagesGrooved (flipAt state (mouth / 3)) candy :=
      grooved_after_flip_other hCandy hCandyForeign
    have hLflip : PathGrooves L.paths
        (flipAt state (mouth / 3)) := by
      intro path hpath
      simp only [L, List.mem_singleton] at hpath
      subst path
      exact hCandyFlip
    have hperiod := C.toSupported.paired_period L
      hOldAvoidsL hNewAvoidsC'
      (flipAt state (mouth / 3)) hCflip hLflip
    have hpositive :
        0 < 2 * (C.toSupported.travel + L.travel) := by
      dsimp [L]
      omega
    exact eventuallyPeriodic_of_period hpositive hperiod

/-- The flip-reflector residual has now been reduced to a candy contact.
Every changed-forward splice whose old selected passage lies on the runway
is periodic; otherwise the exact selected passage is retained and certified
not to lie on that runway. -/
theorem ManufacturedReflector.ChangedForwardMerge.eventuallyPeriodic_or_flip_candy
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R)) :
    EventuallyPeriodic w
        (g, (ManufacturedReflector.flip R).activatedState) ∨
      ∃ entry mouth state,
        (entry, mouth) ∈
          (ManufacturedReflector.flip R).orientedRoute state ∧
        (entry, mouth) ∉ R.runway := by
  obtain ⟨entry, mouth, returnPort, outside, candy, state,
      _leadSteps, _tailSteps, horiented, hentryBranch, _hmouthStem,
      hmouthLink, _harms, hgrooved, htrace, hcrossed, hRpaths,
      hCandy, hCandyForeign, hLobe, hreach, _hcomplete⟩ :=
    hmerge.spliced_lobe_reflector
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · left
    have hperiodic := manufactured_flip_runway_splice_periodic R
      state hRpaths hrunway hmouthLink hentryBranch hgrooved
      htrace hcrossed hCandy hCandyForeign hLobe
    exact hperiodic.prepend hreach
  · right
    exact ⟨entry, mouth, state, horiented, hrunway⟩

/-- A branch-to-stem passage on a flip reflector's selected route that is
not on its runway is an actual candy passage, possibly with the recorded
orientation reversed.  The selected mouth arm itself cannot be such a
passage because its first endpoint is the reflector's stem. -/
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

/-- The final changed-forward splice is periodic whenever the protected old
reflector is the degenerate identity reflector.  A runway contact leaves a
strict identity-reflector suffix opposite the newly spliced flip lobe.  A
core contact makes the lobe's outside edge equal to its own mouth, so two
lobe traversals close directly. -/
theorem ManufacturedReflector.ChangedForwardMerge.eventuallyPeriodic_of_stay
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedStayReflector w e g}
    (hmerge : A.ChangedForwardMerge (.stay R)) :
    EventuallyPeriodic w
      (g, (ManufacturedReflector.stay R).activatedState) := by
  obtain ⟨entry, mouth, _return, outside, candy, state, leadSteps,
      _tailSteps, horiented, hentryBranch, hmouthStem, hmouthLink,
      _harms, _hfullGrooved, _hfullTrace, _hcrossed, hRpaths,
      hCandy, hCandyForeign, hLobe, hreach, _hcomplete⟩ :=
    hmerge.spliced_lobe_reflector
  have hCandyFlip :
      PassagesGrooved (flipAt state (mouth / 3)) candy :=
    grooved_after_flip_other hCandy hCandyForeign
  have hOldRoute :=
    (ManufacturedReflector.stay R).orientedRoute_trace state hRpaths
  have hOldSimple :=
    (ManufacturedReflector.stay R).orientedRoute_simple state
  have hOldGrooved := hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward : arrive state entry = (mouth, state) :=
    groove_forward (hOldGrooved (entry, mouth) horiented)
  have hentryMouthSwitch : entry / 3 = mouth / 3 := by
    have hswitch := arrive_exit_switch state entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  change (entry, mouth) ∈
      R.runway ++ [(R.mouth, R.arm)] at horiented
  rcases List.mem_append.mp horiented with hrunway | hcore
  · obtain ⟨before, after, hsplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨C, hCpaths, hAvoid⟩ :=
      R.suffix_after_runway_passage state hRpaths
        hsplit hmouthLink
    have hAvoid' :
        (LocalAction.flip (mouth / 3)).Avoids
          C.toSupported.paths := by
      simpa [hentryMouthSwitch] using hAvoid
    let L : SupportedReflector w mouth outside := {
      travel := candy.length + 2
      paths := [candy]
      action := .flip (mouth / 3)
      run := by
        intro current hpaths
        have hgrooved : PassagesGrooved current candy :=
          hpaths candy (by simp)
        obtain ⟨hstep, hnext⟩ := hLobe current hgrooved
        constructor
        · exact hstep
        · intro path hpath
          simp only [List.mem_singleton] at hpath
          subst path
          exact hnext
    }
    have hCflip : PathGrooves C.toSupported.paths
        (flipAt state (mouth / 3)) :=
      hCpaths.after_avoiding_action hAvoid'
    have hLflip : PathGrooves L.paths
        (flipAt state (mouth / 3)) := by
      intro path hpath
      simp only [L, List.mem_singleton] at hpath
      subst path
      exact hCandyFlip
    have hperiod := C.toSupported.paired_period L
      (by change True; trivial) hAvoid'
      (flipAt state (mouth / 3)) hCflip hLflip
    have hpositive :
        0 < 2 * (C.toSupported.travel + L.travel) := by
      dsimp [L]
      omega
    exact (eventuallyPeriodic_of_period hpositive hperiod).prepend hreach
  · simp only [List.mem_singleton] at hcore
    have hentryEq : entry = R.mouth :=
      congrArg Prod.fst hcore
    have hmouthEq : mouth = R.arm :=
      congrArg Prod.snd hcore
    subst entry
    subst mouth
    have houtsideEq : outside = R.arm := by
      rw [R.selfLink] at hmouthLink
      exact (Option.some.inj hmouthLink).symm
    subst outside
    have hfirst :=
      (hLobe (flipAt state (R.arm / 3)) hCandyFlip).1
    have hfirst' := hfirst
    change stepN w (candy.length + 2)
        (R.arm, flipAt state (R.arm / 3)) =
          some (R.arm,
            flipAt (flipAt state (R.arm / 3)) (R.arm / 3)) at hfirst'
    rw [flipAt_flipAt state (R.arm / 3)] at hfirst'
    have hfirst'' :
        stepN w (candy.length + 2)
          (R.arm, flipAt state (R.arm / 3)) =
            some (R.arm, state) := by
      exact hfirst'
    have hsecond := (hLobe state hCandy).1
    have hperiod :
        stepN w ((candy.length + 2) + (candy.length + 2))
          (R.arm, flipAt state (R.arm / 3)) =
            some (R.arm, flipAt state (R.arm / 3)) := by
      rw [stepN_add, hfirst'']
      exact hsecond
    have hpositive :
        0 < (candy.length + 2) + (candy.length + 2) := by
      omega
    exact (eventuallyPeriodic_of_period hpositive hperiod).prepend hreach

/-- **Exact open track core.**  Complete repair is periodic, every backward
or mouth contact is periodic, and the raw two-reflector system therefore has
only the two named forward merges left.  This is the current general-`N`
frontier of the direct track proof. -/
theorem manufactured_pair_eventuallyPeriodic_or_forward_merges
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodic w (g, B.activatedState) ∨
      A.FacingForwardMerge B ∨ A.ChangedForwardMerge B := by
  rcases manufactured_pair_protected_repair_outcomes A B hA hB with
    hperiodic | hfacing | hchanged | hcomplete
  · exact Or.inl hperiodic
  · exact Or.inr (Or.inl hfacing)
  · exact Or.inr (Or.inr hchanged)
  · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
    exact Or.inl
      (A.completed_route_with_pair_support_periodic B
        B.baseState B.activatedState finalState hA
        hrepair hAfinal hBfinal)

/-- **Single-residual track reduction.**  The no-change forward merge has an
explicit period, so protected repair of two manufactured reflectors can fail
to be periodic only at the state-changing, self-repairing forward splice. -/
theorem manufactured_pair_eventuallyPeriodic_or_changed_forward_merge
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodic w (g, B.activatedState) ∨
      A.ChangedForwardMerge B := by
  rcases manufactured_pair_eventuallyPeriodic_or_forward_merges
      A B hA hB with hperiodic | hfacing | hchanged
  · exact Or.inl hperiodic
  · exact Or.inl hfacing.eventuallyPeriodic
  · exact Or.inr hchanged

/-- Provenance of a current-route facing obstruction.  It is a support groove
that changed between the second reflector's base and activated states.  The
unique responsible event is therefore either the final repeated-mouth event,
or one outward exploration passage.  In the outward case the changing lazy
passage must exit through the facing passage's stem, so the contact is
literally backward relative to that old oriented route. -/
theorem ManufacturedReflector.current_facing_change_location
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (base state : Tongues)
    (hbase : B.baseState = base)
    (hactivated : state = B.activatedState)
    (hpaths : PathGrooves A.toSupported.paths base)
    (hfacing : A.FacingDiversion state state) :
    ∃ oriented ∈ A.orientedRoute state,
      arrive state oriented.2 ≠ (oriented.1, state) ∧
      oriented.1 % 3 = 0 ∧
      ∃ path ∈ A.toSupported.paths, ∃ old ∈ path,
        (oriented = old ∨ oriented = (old.2, old.1)) ∧
        (passageSwitch oriented = B.preReturn.1 / 3 ∨
          ∃ approach p suffix u v,
            B.exploration =
              approach ++ (p, oriented.1) :: suffix ∧
            passageSwitch (p, oriented.1) =
              passageSwitch oriented ∧
            PhysicalTrace w (e, B.baseState) approach (p, u) ∧
            arrive u p = (oriented.1, v) ∧
            v (p / 3) ≠ u (p / 3)) := by
  obtain ⟨oriented, horiented, hbroken, hstem,
      path, hpath, old, hold, horient⟩ :=
    A.current_facing_has_support_witness state hfacing
  have holdBase := hpaths path hpath old hold
  have horientedBase :
      arrive base oriented.2 = (oriented.1, base) := by
    rcases horient with hsame | hreverse
    · simpa [hsame] using holdBase
    · simpa [hreverse] using groove_forward holdBase
  have hchange :=
    broken_groove_changes_switch horientedBase hbroken
  have hchangeB :
      B.activatedState (passageSwitch oriented) ≠
        B.baseState (passageSwitch oriented) := by
    intro hEq
    apply hchange
    calc
      state (passageSwitch oriented) =
          B.activatedState (passageSwitch oriented) :=
        congrFun hactivated (passageSwitch oriented)
      _ = B.baseState (passageSwitch oriented) := hEq
      _ = base (passageSwitch oriented) :=
        congrFun hbase (passageSwitch oriented)
  refine ⟨oriented, horiented, hbroken, hstem,
    path, hpath, old, hold, horient, ?_⟩
  rcases B.activated_change_location hchangeB with
      hreturn | houtward
  · exact Or.inl hreturn
  · obtain ⟨approach, p, x, suffix, u, v,
      hsplit, hswitch, htrace, harrive,
      _hbefore, _hafter, hchanged⟩ := houtward
    have hpSwitch : p / 3 = passageSwitch oriented := by
      simpa [passageSwitch] using hswitch
    have hchangedP : v (p / 3) ≠ u (p / 3) := by
      rw [hpSwitch]
      exact hchanged
    obtain ⟨_hpBranch, hx, _hv, _hback⟩ :=
      changed_arrival_is_trailing harrive hchangedP
    have hxStem : x = oriented.1 := by
      simp only [passageSwitch] at hpSwitch
      omega
    rw [hxStem] at hsplit hswitch harrive
    exact Or.inr ⟨approach, p, suffix, u, v,
      hsplit, hswitch, htrace, harrive, hchangedP⟩

/-- Named form of `repair_or_facing_diversion`. -/
theorem ManufacturedReflector.repair_or_facing_diversion_named
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (selector state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths selector) :
    A.FacingDiversion selector state ∨
    ∃ travel finalState,
      stepN w travel (g, state) =
        some (e, A.toSupported.action.apply finalState) ∧
      PathGrooves A.toSupported.paths finalState := by
  simpa [ManufacturedReflector.FacingDiversion] using
    A.repair_or_facing_diversion selector state hpaths

/-- **Current-route repair.**  Unlike the selector-frozen form above, this
replays the route chosen by the train's current action tongue.  The aligned
reference supplied by `current_route_reference` removes the private action
switch as a spurious obstruction.  Hence either a genuinely broken passage
on the current route is reached facing-first, or the reflector repairs and
completes to the opposite boundary. -/
theorem ManufacturedReflector.repair_current_route_or_facing
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (base state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths base) :
    A.FacingDiversion state state ∨
    ∃ travel finalState,
      stepN w travel (g, state) =
        some (e, A.toSupported.action.apply finalState) ∧
      PathGrooves A.toSupported.paths finalState := by
  obtain ⟨reference, hreferencePaths, hroute, hfinish,
      hreferenceRouteGrooved, _hguard⟩ :=
    A.current_route_reference base state hpaths
  have hreferenceTrace :=
    A.orientedRoute_trace reference hreferencePaths
  rw [hroute, hfinish] at hreferenceTrace
  have hsimple := A.orientedRoute_simple state
  rcases hreferenceTrace.repair_forward_damage_or_facing
      hsimple hreferenceRouteGrooved state with hfacing | hrepaired
  · exact Or.inl (by
      simpa [ManufacturedReflector.FacingDiversion] using hfacing)
  · right
    obtain ⟨finalState, hrepairTrace, hfinalRouteGrooved⟩ := hrepaired
    have hfinalPaths : PathGrooves A.toSupported.paths finalState :=
      A.support_grooves_of_orientedRoute state finalState
        hfinalRouteGrooved
    have hreferenceRouteGrooved' :
        PassagesGrooved reference (A.orientedRoute reference) := by
      rw [hroute]
      exact hreferenceRouteGrooved
    have hfinalReferenceRouteGrooved :
        PassagesGrooved finalState (A.orientedRoute reference) := by
      rw [hroute]
      exact hfinalRouteGrooved
    have horiented := A.oriented_data_eq_of_route_grooved
      reference finalState hreferenceRouteGrooved'
        hfinalReferenceRouteGrooved
    have hrouteFinal := A.orientedRoute_trace finalState hfinalPaths
    have hrouteFinal' : PhysicalTrace w (g, finalState)
        (A.orientedRoute state)
        (A.orientedFinish state, finalState) := by
      rw [horiented.1, horiented.2, hroute, hfinish] at hrouteFinal
      exact hrouteFinal
    have hsplit : A.orientedRoute finalState =
        A.orientedRoute state ++ [] := by
      rw [horiented.1, hroute]
      simp
    obtain ⟨tailSteps, _hlen, htail⟩ :=
      A.complete_after_oriented_prefix finalState hfinalPaths
        hsplit hrouteFinal'
    refine ⟨(A.orientedRoute state).length + tailSteps,
      finalState, ?_, hfinalPaths⟩
    rw [stepN_add, hrepairTrace.sound]
    exact htail

/-- Trace-valued current-route repair.  In the obstruction branch this keeps
the *first* facing passage, the exact prefix by which the train reaches it,
and the other branch selected there.  This is strictly stronger than
`repair_current_route_or_facing` and is the induction interface for the
remaining theta overlap. -/
theorem ManufacturedReflector.repair_current_route_until_first_facing
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (base state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths base) :
    (∃ before p x after contact other,
      A.orientedRoute state = before ++ (p, x) :: after ∧
      PhysicalTrace w (g, state) before (p, contact) ∧
      (∀ passage ∈ before,
        passageSwitch passage ≠ passageSwitch (p, x)) ∧
      p % 3 = 0 ∧
      arrive contact x ≠ (p, contact) ∧
      state (passageSwitch (p, x)) ≠
        base (passageSwitch (p, x)) ∧
      arrive contact p = (other, contact) ∧ other ≠ x) ∨
    ∃ travel finalState,
      stepN w travel (g, state) =
        some (e, A.toSupported.action.apply finalState) ∧
      PathGrooves A.toSupported.paths finalState := by
  obtain ⟨reference, hreferencePaths, hroute, hfinish,
      hreferenceRouteGrooved, hguard⟩ :=
    A.current_route_reference base state hpaths
  have hreferenceTrace :=
    A.orientedRoute_trace reference hreferencePaths
  rw [hroute, hfinish] at hreferenceTrace
  have hsimple := A.orientedRoute_simple state
  rcases hreferenceTrace.repair_until_first_facing
      hsimple hreferenceRouteGrooved state with hfirst | hrepaired
  · obtain ⟨before, p, x, after, contact, other,
        hsplit, hprefix, hforeign, hstem, hbroken,
        harrive, hother⟩ := hfirst
    have hreferenceGroove :
        arrive reference x = (p, reference) :=
      hreferenceRouteGrooved (p, x) (by
        rw [hsplit]
        exact List.mem_append_right before List.mem_cons_self)
    have hswitch : x / 3 = passageSwitch (p, x) := by
      have hs := arrive_exit_switch reference x
      rw [hreferenceGroove] at hs
      exact hs.symm
    have hcontactState : contact (passageSwitch (p, x)) =
        state (passageSwitch (p, x)) :=
      hprefix.preserves _ hforeign
    have hstateReference : state (passageSwitch (p, x)) ≠
        reference (passageSwitch (p, x)) := by
      intro heq
      apply hbroken
      apply groove_transfer hreferenceGroove
      rw [hswitch, hcontactState]
      exact heq
    have hreferenceBase : reference (passageSwitch (p, x)) =
        base (passageSwitch (p, x)) := by
      by_cases heq : reference (passageSwitch (p, x)) =
          base (passageSwitch (p, x))
      · exact heq
      · exfalso
        exact hstateReference (hguard _ heq).symm
    have hstateBase : state (passageSwitch (p, x)) ≠
        base (passageSwitch (p, x)) := by
      intro heq
      apply hstateReference
      exact heq.trans hreferenceBase.symm
    exact Or.inl ⟨before, p, x, after, contact, other,
      hsplit, hprefix, hforeign, hstem, hbroken,
      hstateBase, harrive, hother⟩
  · right
    obtain ⟨finalState, hrepairTrace, hfinalRouteGrooved⟩ := hrepaired
    have hfinalPaths : PathGrooves A.toSupported.paths finalState :=
      A.support_grooves_of_orientedRoute state finalState
        hfinalRouteGrooved
    have hreferenceRouteGrooved' :
        PassagesGrooved reference (A.orientedRoute reference) := by
      rw [hroute]
      exact hreferenceRouteGrooved
    have hfinalReferenceRouteGrooved :
        PassagesGrooved finalState (A.orientedRoute reference) := by
      rw [hroute]
      exact hfinalRouteGrooved
    have horiented := A.oriented_data_eq_of_route_grooved
      reference finalState hreferenceRouteGrooved'
        hfinalReferenceRouteGrooved
    have hrouteFinal := A.orientedRoute_trace finalState hfinalPaths
    have hrouteFinal' : PhysicalTrace w (g, finalState)
        (A.orientedRoute state)
        (A.orientedFinish state, finalState) := by
      rw [horiented.1, horiented.2, hroute, hfinish] at hrouteFinal
      exact hrouteFinal
    have hsplit : A.orientedRoute finalState =
        A.orientedRoute state ++ [] := by
      rw [horiented.1, hroute]
      simp
    obtain ⟨tailSteps, _hlen, htail⟩ :=
      A.complete_after_oriented_prefix finalState hfinalPaths
        hsplit hrouteFinal'
    refine ⟨(A.orientedRoute state).length + tailSteps,
      finalState, ?_, hfinalPaths⟩
    rw [stepN_add, hrepairTrace.sound]
    exact htail

/-- **Global repair residual.**  Lift the damaged-reflector macro dichotomy
all the way back to the original train start.  After the two manufactured
reflector journeys, either the old selected route exposes one concrete facing
diversion, or a further finite journey repairs its full support and carries
the train to the opposite boundary.  This theorem retains all construction
data needed by the remaining theta argument. -/
theorem long_run_eventually_periodic_or_facing_diversion_or_repaired
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1) :
    EventuallyPeriodic w start ∨
      ∃ (A : ManufacturedReflector w start.1 e)
          (B : ManufacturedReflector w e start.1)
          (stateA stateB : Tongues) (firstTravel secondTravel : Nat),
        A.baseState = start.2 ∧
        stateA = A.activatedState ∧
        stepN w firstTravel start = some (e, stateA) ∧
        PathGrooves A.toSupported.paths stateA ∧
        B.baseState = stateA ∧
        stateB = B.activatedState ∧
        stepN w secondTravel (e, stateA) = some (start.1, stateB) ∧
        PathGrooves B.toSupported.paths stateB ∧
        A.ForwardOrientedFault B ∧
        (A.FacingDiversion stateB stateB ∨
          ∃ repairTravel repaired,
            stepN w (firstTravel + secondTravel + repairTravel) start =
              some (e, A.toSupported.action.apply repaired) ∧
            PathGrooves A.toSupported.paths repaired) := by
  rcases long_run_eventually_periodic_or_forward_fault
      hN hlive hentry with hperiodic | hresidual
  · exact Or.inl hperiodic
  · obtain ⟨A, B, stateA, stateB, firstTravel, secondTravel,
      hbaseA, hactivatedA, hreachA, hgroovesA,
      hbaseB, hactivatedB, hreachB, hgroovesB, hforward⟩ := hresidual
    right
    refine ⟨A, B, stateA, stateB, firstTravel, secondTravel,
      hbaseA, hactivatedA, hreachA, hgroovesA,
      hbaseB, hactivatedB, hreachB, hgroovesB, hforward, ?_⟩
    rcases A.repair_current_route_or_facing
        stateA stateB hgroovesA with hfacing | hrepaired
    · exact Or.inl hfacing
    · right
      obtain ⟨repairTravel, repaired, hrepair, hgroovesRepaired⟩ :=
        hrepaired
      refine ⟨repairTravel, repaired, ?_, hgroovesRepaired⟩
      rw [stepN_add, stepN_add, hreachA]
      simp only [Option.bind_some]
      rw [hreachB]
      exact hrepair

end GeneralN
