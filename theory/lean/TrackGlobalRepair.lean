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
      PassagesGrooved reference (A.orientedRoute state) := by
  cases A with
  | stay R =>
      have htrace :=
        (ManufacturedReflector.stay R).orientedRoute_trace base hpaths
      have hgrooved := htrace.grooved_of_switchSimple
        ((ManufacturedReflector.stay R).orientedRoute_simple base)
      exact ⟨base, hpaths, rfl, rfl, hgrooved⟩
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
        exact ⟨base, hpaths, hroute, hfinish, hgrooved⟩
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
        exact ⟨reference, hreferencePaths,
          hroute, hfinish, hgrooved⟩

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
      hreferenceRouteGrooved⟩ :=
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
