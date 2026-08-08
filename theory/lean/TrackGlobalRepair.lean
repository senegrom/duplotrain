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
    (∃ before p x after contact fresh,
      A.orientedRoute B.activatedState =
        before ++ (p, x) :: after ∧
      PhysicalTrace w (g, B.activatedState) before (p, contact) ∧
      PathGrooves B.toSupported.paths contact ∧
      p % 3 = 0 ∧
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
          contact, fresh, hsplit, hprefix, hBcontact, hp,
          harriveFresh, by simpa [hotherFresh] using hother,
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
