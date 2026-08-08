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
        (A.FacingDiversion stateA stateB ∨
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
    rcases A.repair_or_facing_diversion_named
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
