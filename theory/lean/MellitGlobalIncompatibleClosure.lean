import MellitGlobalNoveltyBound
import MellitEarlySecondRepeatAssembly
import CrossingCallerWindowExtraction

/-!
# Global closure of the incompatible Mellit pair

The compatible branch of Mellit's second turnaround already has the sharp
all-horizon bound: the first manufacturing journey contributes at most one
new repeated-writer vector and the reached pair contributes its four Gray
corners.  This file isolates what failure of compatibility means in the raw
track language.

For an arbitrary opposite pair, non-compatibility is not an abstract
negation: one of the two nontrivial local actions is a flip and its action
switch occurs on a concrete support passage of the other reflector.  For the
literal direct lobe produced by the BABA endpoint theorem, the reverse
avoidance is automatic because its reusable support is empty.  The apparent
remaining support contact is impossible: the direct lobe saturates all three
ports of its action switch, while the opposite manufactured route is
switch-simple.  The only endpoint not immediately ruled out by simplicity is
a singleton identity core, whose self-link contradicts the lobe's
branch-to-branch edge.

Consequently the opposite pair is compatible without an extra hypothesis,
and the final theorem gives the unconditional all-horizon bound five.  No
six-event cardinality claim, periodic-tail assumption, or small-N computation
is used.
-/

namespace GeneralN

/-- The two local actions of an opposite manufactured pair preserve one
another's reusable supports. -/
def MellitPairCompatible
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) : Prop :=
  A.toSupported.action.Avoids B.toSupported.paths ∧
    B.toSupported.action.Avoids A.toSupported.paths

/-- Concrete raw witness to failure of pair compatibility.  The disjunction
records its orientation: either `A`'s flip switch lies on `B`'s support, or
`B`'s flip switch lies on `A`'s support. -/
structure MellitGlobalSupportIntersection
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) : Prop where
  witness :
    (∃ k,
      A.toSupported.action = LocalAction.flip k ∧
      ∃ path ∈ B.toSupported.paths, ∃ passage ∈ path,
        passageSwitch passage = k) ∨
    (∃ k,
      B.toSupported.action = LocalAction.flip k ∧
      ∃ path ∈ A.toSupported.paths, ∃ passage ∈ path,
        passageSwitch passage = k)

/-- Negating avoidance exposes an actual support passage and also proves
that the offending local action is a flip. -/
private theorem action_contact_of_not_avoids
    {action : LocalAction} {paths : List (List Passage)}
    (hnot : ¬ action.Avoids paths) :
    ∃ k, action = LocalAction.flip k ∧
      ∃ path ∈ paths, ∃ passage ∈ path,
        passageSwitch passage = k := by
  cases action with
  | stay =>
      exact (hnot trivial).elim
  | flip k =>
      exact ⟨k, rfl, contact_of_not_avoids_flip hnot⟩

/-- Every manufactured reflector's activated state grooves the reusable
support retained by the constructor.  This restores information that some
later residue packages intentionally omit.

For an identity reflector the complete simple exploration is already grooved
in its return state.  For a flip reflector it is grooved in `returnState`;
the activating trailing passage changes only the excluded mouth switch, so
all runway and candy grooves transfer to `afterReturn`. -/
theorem ManufacturedReflector.activated_support_grooves
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w g e) :
    PathGrooves B.toSupported.paths B.activatedState := by
  cases B with
  | stay R =>
      change PathGrooves
        [R.runway, [(R.mouth, R.arm)]] R.returnState
      have hgrooved :=
        (R.runwayTrace.append R.coreTrace).grooved_of_switchSimple R.simple
      change PassagesGrooved R.returnState
        (R.runway ++ [(R.mouth, R.arm)]) at hgrooved
      apply pathGrooves_pair.mpr
      constructor
      · intro passage hpassage
        exact hgrooved passage (List.mem_append_left _ hpassage)
      · intro passage hpassage
        exact hgrooved passage (List.mem_append_right _ hpassage)
  | flip R =>
      change PathGrooves [R.runway, R.candy] R.afterReturn
      have hgrooved :=
        (R.runwayTrace.append R.candyTrace).grooved_of_switchSimple R.simple
      change PassagesGrooved R.returnState
        (R.runway ++ (R.mouth, R.firstArm) :: R.candy) at hgrooved
      have hreturnPaths : PathGrooves
          [R.runway, R.candy] R.returnState := by
        apply pathGrooves_pair.mpr
        constructor
        · intro passage hpassage
          exact hgrooved passage (List.mem_append_left _ hpassage)
        · intro passage hpassage
          exact hgrooved passage (List.mem_append_right _
            (List.mem_cons_of_mem _ hpassage))
      intro path hpath passage hpassage
      have hold := hreturnPaths path hpath passage hpassage
      apply groove_transfer hold
      have hforeign := R.support_foreign path hpath passage hpassage
      have hne : passageSwitch passage ≠ R.secondArm / 3 := by
        intro heq
        apply hforeign
        exact heq.trans R.secondArm_switch
      have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
        have hs := arrive_exit_switch R.returnState passage.2
        rw [hold] at hs
        exact hs.symm
      have hne2 : passage.2 / 3 ≠ R.secondArm / 3 := by
        rw [hexitSwitch]
        exact hne
      exact arrive_preserves_other R.crossed hne2

/-! ## The direct lobe saturates its switch

When both retained paths of a manufactured flip reflector are empty, its
mouth is the starting stem, its two branch ports are linked to one another,
and its stem is linked to the opposite boundary.  Thus every port at that
switch is already accounted for.  The next three lemmas turn that elementary
picture into a statement about arbitrary switch-simple manufactured support.
-/

private theorem direct_lobe_stem_eq
    {w : Wiring} {g e : Nat}
    (D : ManufacturedFlipReflector w g e)
    (hRunway : D.runway = []) :
    g = 3 * D.actionSwitch := by
  have htrace := D.runwayTrace
  rw [hRunway] at htrace
  have hsame : (g, D.base) = (D.mouth, D.mouthState) := by
    simpa [stepN] using htrace.sound
  have hg : g = D.mouth := congrArg Prod.fst hsame
  have hm := D.mouth_is_stem
  unfold ManufacturedFlipReflector.actionSwitch
  omega

/-- Every branch at the direct lobe's action switch has the other branch as
its unique physical partner. -/
private theorem direct_lobe_branch_partner
    {w : Wiring} {g e p : Nat}
    (D : ManufacturedFlipReflector w g e)
    (hCandy : D.candy = [])
    (hswitch : p / 3 = D.actionSwitch)
    (hbranch : p % 3 ≠ 0) :
    ∃ q,
      q / 3 = D.actionSwitch ∧
      q % 3 ≠ 0 ∧ q ≠ p ∧ w.link p = some q := by
  have htrace := D.candyTrace
  rw [hCandy] at htrace
  have hedge : w.link D.firstArm = some D.secondArm := by
    simpa [lastPassageExit] using htrace.last_link
  have hfirstSwitch := D.firstArm_switch
  have hsecondSwitch := D.secondArm_switch
  have hfirstBranch := D.firstArm_branch
  have hsecondBranch := D.secondArm_branch
  have harms := D.arms_ne
  have hp : p = D.firstArm ∨ p = D.secondArm := by
    omega
  rcases hp with rfl | rfl
  · exact ⟨D.secondArm, hsecondSwitch, hsecondBranch,
      D.arms_ne.symm, hedge⟩
  · exact ⟨D.firstArm, hfirstSwitch, hfirstBranch,
      D.arms_ne, w.symm _ _ hedge⟩

/-- A manufactured support route cannot use the saturated switch of an
opposite direct lobe.  The proof is purely physical.

If the route enters the lobe stem, its preceding simple prefix would have to
leave through the route's own first port.  If it leaves the lobe stem, its
preceding edge is the other branch of the same switch.  Both contradict
switch simplicity.  At an empty prefix the same matching equations give the
contradiction directly.  The sole remaining singleton route could only be a
degenerate identity core; its self-link conflicts with the lobe's
branch-to-branch link. -/
private theorem direct_lobe_support_contact_false
    {w : Wiring} {g e : Nat}
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hBpaths : PathGrooves B.toSupported.paths state)
    {path : List Passage} {old : Passage}
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = D.actionSwitch) : False := by
  classical
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute state hpath hold
  rcases oriented with ⟨p, x⟩
  rcases old with ⟨oldP, oldX⟩
  have hroute := B.orientedRoute_trace state hBpaths
  have hrouteSimple := B.orientedRoute_simple state
  have hrouteGrooved := hroute.grooved_of_switchSimple hrouteSimple
  have hback : arrive state x = (p, state) :=
    hrouteGrooved (p, x) horiented
  have hforward : arrive state p = (x, state) := groove_forward hback
  have holdGroove : arrive state oldX = (oldP, state) :=
    hBpaths path hpath (oldP, oldX) hold
  have horientedSwitch : passageSwitch (p, x) = D.actionSwitch := by
    have holdSame := arrive_exit_switch state oldX
    rw [holdGroove] at holdSame
    rcases horientation with horientation | horientation
    · have hpEq := congrArg Prod.fst horientation
      have hxEq := congrArg Prod.snd horientation
      simp only at hpEq hxEq
      simp only [passageSwitch] at hswitch ⊢
      omega
    · have hpEq := congrArg Prod.fst horientation
      have hxEq := congrArg Prod.snd horientation
      simp only at hpEq hxEq
      simp only [passageSwitch] at hswitch ⊢
      omega
  have hgStem := direct_lobe_stem_eq D hRunway
  have hstem := hroute.passage_stem_endpoint (p, x) horiented
  have hstem' : p = g ∨ x = g := by
    rcases hstem with hpStem | hxStem
    · left
      simp only [passageSwitch] at hpStem horientedSwitch
      omega
    · right
      simp only [passageSwitch] at hxStem horientedSwitch
      omega
  obtain ⟨before, after, hsplit⟩ := List.append_of_mem horiented
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    hroute hsplit hrouteGrooved hrouteSimple
  have hprefixTrace : PhysicalTrace w (e, state) before (p, state) := by
    simpa using hprefixData.1
  have hprefixForeign : ∀ passage ∈ before,
      passageSwitch passage ≠ passageSwitch (p, x) := by
    simpa using hprefixData.2
  rcases hstem' with hpStem | hxStem
  · subst p
    have hxSwitch : x / 3 = D.actionSwitch := by
      have hsame := arrive_exit_switch state g
      rw [hforward] at hsame
      simp only [passageSwitch] at horientedSwitch
      omega
    have hxBranch : x % 3 ≠ 0 := by
      intro hx0
      have hne := arrive_exit_ne state g
      rw [hforward] at hne
      apply hne
      omega
    obtain ⟨q, hqSwitch, hqBranch, hqNe, hxq⟩ :=
      direct_lobe_branch_partner D hCandy hxSwitch hxBranch
    cases before with
    | cons first rest =>
        rcases first with ⟨a, b⟩
        have hlast := hprefixTrace.last_link
        have hgLast := w.symm _ _ hlast
        have hge := w.symm _ _ D.entryEdge
        have hlastEq : lastPassageExit b rest = e := by
          rw [hge] at hgLast
          exact (Option.some.inj hgLast).symm
        have hprefixSimple : SwitchSimple ((a, b) :: rest) := by
          unfold SwitchSimple at hrouteSimple ⊢
          rw [hsplit] at hrouteSimple
          simp only [List.map_append, List.map_cons] at hrouteSimple
          exact (List.nodup_append.mp hrouteSimple).1
        have hne :=
          hprefixTrace.simple_last_exit_ne_first_entry hprefixSimple
        have hstart : e = a := hprefixTrace.head_arrive.1
        apply hne
        omega
    | nil =>
        have hsame : (e, state) = (g, state) := by
          simpa [stepN] using hprefixTrace.sound
        have hep : e = g := congrArg Prod.fst hsame
        cases after with
        | cons next rest =>
            rcases next with ⟨r, y⟩
            have hlinked := hroute.linked
            rw [hsplit] at hlinked
            have hxr : w.link x = some r := hlinked.1
            have hrq : r = q := by
              rw [hxq] at hxr
              exact (Option.some.inj hxr).symm
            have hs := hrouteSimple
            rw [hsplit] at hs
            unfold SwitchSimple at hs
            simp only [List.nil_append, List.map_cons,
              List.nodup_cons] at hs
            apply hs.1
            have heq : passageSwitch (r, y) = passageSwitch (g, x) := by
              simp only [passageSwitch]
              rw [hrq, hqSwitch]
              exact horientedSwitch.symm
            rw [← heq]
            exact List.mem_cons_self
        | nil =>
            have hsingle : B.orientedRoute state = [(g, x)] := by
              simpa using hsplit
            cases B with
            | flip R =>
                by_cases hselected :
                    state R.actionSwitch = bval R.firstArm
                · have hlen := congrArg List.length hsingle
                  simp [ManufacturedReflector.orientedRoute,
                    hselected] at hlen
                  have hrunwayZero : R.runway.length = 0 := by omega
                  have hcandyZero : R.candy.length = 0 := by omega
                  have hrunwayNil : R.runway = [] := by
                    cases hR : R.runway with
                    | nil => rfl
                    | cons passage rest =>
                        rw [hR] at hrunwayZero
                        simp at hrunwayZero
                  have hcandyNil : R.candy = [] := by
                    cases hC : R.candy with
                    | nil => rfl
                    | cons passage rest =>
                        rw [hC] at hcandyZero
                        simp at hcandyZero
                  change path ∈ [R.runway, R.candy] at hpath
                  rw [hrunwayNil, hcandyNil] at hpath
                  simp only [List.mem_cons, List.not_mem_nil,
                    or_false] at hpath
                  rcases hpath with rfl | rfl <;> cases hold
                · have hlen := congrArg List.length hsingle
                  simp [ManufacturedReflector.orientedRoute,
                    hselected, reversePassages_length] at hlen
                  have hrunwayZero : R.runway.length = 0 := by omega
                  have hcandyZero : R.candy.length = 0 := by omega
                  have hrunwayNil : R.runway = [] := by
                    cases hR : R.runway with
                    | nil => rfl
                    | cons passage rest =>
                        rw [hR] at hrunwayZero
                        simp at hrunwayZero
                  have hcandyNil : R.candy = [] := by
                    cases hC : R.candy with
                    | nil => rfl
                    | cons passage rest =>
                        rw [hC] at hcandyZero
                        simp at hcandyZero
                  change path ∈ [R.runway, R.candy] at hpath
                  rw [hrunwayNil, hcandyNil] at hpath
                  simp only [List.mem_cons, List.not_mem_nil,
                    or_false] at hpath
                  rcases hpath with rfl | rfl <;> cases hold
            | stay R =>
                have hlen : R.runway.length + 1 = 1 := by
                  simpa [ManufacturedReflector.orientedRoute] using
                    congrArg List.length hsingle
                have hrunwayZero : R.runway.length = 0 := by omega
                have hrunwayNil : R.runway = [] := by
                  cases hR : R.runway with
                  | nil => rfl
                  | cons passage rest =>
                      rw [hR] at hrunwayZero
                      simp at hrunwayZero
                have hsingle' := hsingle
                simp [ManufacturedReflector.orientedRoute,
                  hrunwayNil] at hsingle'
                have hxArm : x = R.arm := by
                  exact hsingle'.2.symm
                subst x
                have hEq : q = R.arm := by
                  rw [R.selfLink] at hxq
                  exact (Option.some.inj hxq).symm
                exact hqNe hEq
  · subst x
    have hpBranch : p % 3 ≠ 0 := by
      intro hp0
      have hne := arrive_exit_ne state p
      rw [hforward] at hne
      apply hne
      simp only [passageSwitch] at horientedSwitch
      omega
    have hpSwitch : p / 3 = D.actionSwitch := by
      simpa [passageSwitch] using horientedSwitch
    obtain ⟨q, hqSwitch, hqBranch, hqNe, hpq⟩ :=
      direct_lobe_branch_partner D hCandy hpSwitch hpBranch
    cases before with
    | nil =>
        have hsame : (e, state) = (p, state) := by
          simpa [stepN] using hprefixTrace.sound
        have hep : e = p := congrArg Prod.fst hsame
        have hEq : g = q := by
          have hedge := D.entryEdge
          rw [hep, hpq] at hedge
          exact (Option.some.inj hedge).symm
        omega
    | cons first rest =>
        rcases first with ⟨a, b⟩
        have hlast := hprefixTrace.last_link
        have hpLast := w.symm _ _ hlast
        have hqLast : q = lastPassageExit b rest := by
          rw [hpq] at hpLast
          exact Option.some.inj hpLast
        have hmem := hprefixTrace.last_exit_switch_mem
        have hkMem : D.actionSwitch ∈
            (((a, b) :: rest).map passageSwitch) := by
          rw [← hqSwitch, hqLast]
          exact hmem
        obtain ⟨prior, hprior, hpriorSwitch⟩ :=
          List.mem_map.mp hkMem
        apply hprefixForeign prior hprior
        exact hpriorSwitch.trans horientedSwitch.symm

/-- The reusable support of an opposite manufactured reflector is disjoint
from the action switch of a literal direct lobe. -/
theorem direct_lobe_action_avoids_opposite_support
    {w : Wiring} {g e : Nat}
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hBpaths : PathGrooves B.toSupported.paths state) :
    (LocalAction.flip D.actionSwitch).Avoids
      B.toSupported.paths := by
  change ∀ path ∈ B.toSupported.paths, ∀ passage ∈ path,
    passageSwitch passage ≠ D.actionSwitch
  intro path hpath passage hpassage hswitch
  exact direct_lobe_support_contact_false D B state
    hRunway hCandy hBpaths hpath hpassage hswitch

/-- Public compatibility certificate for a literal direct lobe and any
opposite manufactured reflector reached in a state grooving its support. -/
theorem direct_lobe_opposite_pair_compatible
    {w : Wiring} {g e : Nat}
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hBpaths : PathGrooves B.toSupported.paths state) :
    MellitPairCompatible (ManufacturedReflector.flip D) B := by
  constructor
  · simpa [ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported] using
        direct_lobe_action_avoids_opposite_support
          D B state hRunway hCandy hBpaths
  · change B.toSupported.action.Avoids [D.runway, D.candy]
    rw [hRunway, hCandy]
    cases B.toSupported.action <;> simp [LocalAction.Avoids]

/-- The named pure-crossing residue is empty: its support witness contradicts
direct-lobe saturation.  The `RawOverlappingFiveWindowReduction` data and the
second conjunct of the residue are intentionally unused; the obstruction is
already local and physical. -/
theorem RawOverlappingFiveWindowReduction.early_direct_lobe_pure_crossing_false
    {w : Wiring} {N g e K : Nat}
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (H : EarlyDirectLobePureCrossingResidue (K := K) C D B) : False := by
  obtain ⟨⟨path, hpath, passage, hpassage, hswitch⟩, _⟩ := H
  exact direct_lobe_support_contact_false D B B.activatedState
    hRunway hCandy B.activated_support_grooves
      hpath hpassage hswitch

/-- Every opposite pair is support-compatible or has a concrete oriented
support intersection.  This is a pure matching statement over physical
support passages. -/
theorem manufactured_pair_compatible_or_support_intersection
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) :
    MellitPairCompatible A B ∨
      MellitGlobalSupportIntersection A B := by
  classical
  by_cases hAB :
      A.toSupported.action.Avoids B.toSupported.paths
  · by_cases hBA :
        B.toSupported.action.Avoids A.toSupported.paths
    · exact Or.inl ⟨hAB, hBA⟩
    · exact Or.inr ⟨Or.inr
        (action_contact_of_not_avoids hBA)⟩
  · exact Or.inr ⟨Or.inl
      (action_contact_of_not_avoids hAB)⟩

/-- The literal second-repeat theorem, with the non-cycle branch split into
the compatible case and a concrete support intersection.  All reach,
groove, periodicity, and first-turnaround charge data from Mellit's theorem
are retained. -/
theorem mellit_second_repeat_cycle_compatible_or_support_intersection
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {state : Tongues} {finish : Nat × Tongues}
    {passages : List Passage}
    (hstate : state = A.activatedState)
    (hA : PathGrooves A.toSupported.paths state)
    (htrace : PhysicalTrace w (e, state) passages finish)
    (hnonsimple : ¬ SwitchSimple passages) :
    (∃ atRepeat visited,
        stepN w visited (e, state) = some atRepeat ∧
        SettlesOnSimpleCycle w atRepeat) ∨
      ∃ (B : ManufacturedReflector w e g)
          (atRepeat : Nat × Tongues) (visited backSteps : Nat),
        stepN w visited (e, state) = some atRepeat ∧
        stepN w (visited + backSteps) (e, state) =
          some (g, B.activatedState) ∧
        PathGrooves A.toSupported.paths B.baseState ∧
        PathGrooves B.toSupported.paths B.activatedState ∧
        EventuallyPeriodic w (g, B.activatedState) ∧
        (rawRepeatedWriterNovelTimes w N (g, A.baseState)
          (A.exploration.length + A.runway.length + 1)).length ≤ 1 ∧
        (MellitPairCompatible A B ∨
          MellitGlobalSupportIntersection A B) := by
  rcases mellit_second_repeat_with_first_turnaround_bound
      A hN hstate hA htrace hnonsimple with hcycle | hpair
  · exact Or.inl hcycle
  · obtain ⟨B, atRepeat, visited, backSteps, hvisited, hreach,
      hAbase, hBactivated, hperiodic, hfirst⟩ := hpair
    exact Or.inr ⟨B, atRepeat, visited, backSteps, hvisited,
      hreach, hAbase, hBactivated, hperiodic, hfirst,
      manufactured_pair_compatible_or_support_intersection A B⟩

/-- **Global direct-lobe closure.**

The direct lobe has empty support, so the opposite action automatically
avoids it.  Direct-lobe saturation proves the converse avoidance, so the
global five-novelty theorem applies.  The disjunctive result is retained as a
compatibility API for existing callers; its right alternative is uninhabited.
-/
theorem RawOverlappingFiveWindowReduction.first_turnaround_then_direct_pair_le_five_or_pure_support_crossing
    {w : Wiring} {N h g e K : Nat}
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (P : ManufacturedReflector w h g)
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hPpaths : PathGrooves P.toSupported.paths P.activatedState)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hBpaths : PathGrooves
      B.toSupported.paths B.activatedState)
    (hJourney : stepN w
      (P.exploration.length + P.runway.length + 1)
      (h, P.baseState) = some (g, B.activatedState))
    (_hreach : stepN w K start =
      some (g, B.activatedState)) :
    (∀ H,
      (rawRepeatedWriterNovelTimes w N
        (h, P.baseState) H).length ≤ 5) ∨
      EarlyDirectLobePureCrossingResidue (K := K) C D B := by
  have hDpaths : PathGrooves
      (ManufacturedReflector.flip D).toSupported.paths
        B.activatedState := by
    change PathGrooves [D.runway, D.candy] B.activatedState
    rw [hRunway, hCandy]
    simp [PathGrooves, PassagesGrooved]
  have hcompatible := direct_lobe_opposite_pair_compatible
    D B B.activatedState hRunway hCandy hBpaths
  exact Or.inl
    (first_turnaround_then_compatible_pair_repeatedWriterNovelty_le_five
      P (.flip D) B B.activatedState hN hPpaths hDpaths hBpaths
      hcompatible.1 hcompatible.2 hJourney)

/-- The direct second-repeat branch has the sharp all-horizon bound five,
unconditionally.  The former pure-support-crossing hypothesis has disappeared
because `early_direct_lobe_pure_crossing_false` proves that predicate empty. -/
theorem RawOverlappingFiveWindowReduction.first_turnaround_then_direct_pair_repeatedWriterNovelty_le_five
    {w : Wiring} {N h g e K : Nat}
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (P : ManufacturedReflector w h g)
    (D : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hPpaths : PathGrooves P.toSupported.paths P.activatedState)
    (hRunway : D.runway = [])
    (hCandy : D.candy = [])
    (hBpaths : PathGrooves
      B.toSupported.paths B.activatedState)
    (hJourney : stepN w
      (P.exploration.length + P.runway.length + 1)
      (h, P.baseState) = some (g, B.activatedState))
    (hreach : stepN w K start =
      some (g, B.activatedState)) :
    ∀ H,
      (rawRepeatedWriterNovelTimes w N
        (h, P.baseState) H).length ≤ 5 := by
  rcases C.first_turnaround_then_direct_pair_le_five_or_pure_support_crossing
      P D B hN hPpaths hRunway hCandy hBpaths hJourney hreach with
    hbound | hpure
  · exact hbound
  · exact (C.early_direct_lobe_pure_crossing_false
      D B hRunway hCandy hpure).elim

end GeneralN
