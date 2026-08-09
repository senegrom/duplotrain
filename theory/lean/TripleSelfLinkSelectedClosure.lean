import TripleSelfLinkCycleClosure

/-!
# Preserving the selected self-link through the opposite reflector

The raw first-revisit theorem returns an activated opposite reflector.  To
apply the quantitative self-link tail, its activated state must still select
the self-linked branch.  This file proves that transport from the physical
manufactured-reflector data: activation cannot change the switch owning the
incoming stem edge.  In the flip case the only remaining possible change is
the reflector action itself, and `actionSwitch_ne_self_link` excludes it.
-/

namespace GeneralN

/-! ## Endpoint geometry of a manufactured reflector -/

/-- A manufactured reflector cannot finish its switch-simple exploration at
the same port at which that exploration started.  A nonempty runway would
repeat the start/mouth switch; an empty runway would identify a stem with the
distinct return arm. -/
theorem ManufacturedReflector.preReturn_port_ne_start
    {w : Wiring} {g e : Nat} (A : ManufacturedReflector w g e) :
    A.preReturn.1 ≠ g := by
  cases A with
  | flip R =>
      change R.secondArm ≠ g
      intro heq
      cases hrunway : R.runway with
      | nil =>
          have htrace := R.runwayTrace
          rw [hrunway] at htrace
          have hcfg : (g, R.base) = (R.mouth, R.mouthState) := by
            simpa [stepN] using htrace.sound
          have hgm : g = R.mouth := congrArg Prod.fst hcfg
          have hsecondBranch := R.secondArm_branch
          have hmouthStem := R.mouth_is_stem
          rw [heq, hgm] at hsecondBranch
          exact hsecondBranch hmouthStem
      | cons passage rest =>
          rcases passage with ⟨p, x⟩
          have htrace := R.runwayTrace
          rw [hrunway] at htrace
          have hgp : g = p := htrace.head_arrive.1
          have hleft : g / 3 ∈ R.runway.map passageSwitch := by
            apply List.mem_map.mpr
            refine ⟨(p, x), ?_, ?_⟩
            · simp [hrunway]
            · simp [passageSwitch, hgp]
          have hmouthSwitch : R.mouth / 3 = g / 3 := by
            calc
              R.mouth / 3 = R.actionSwitch := rfl
              _ = R.secondArm / 3 := R.secondArm_switch.symm
              _ = g / 3 := by rw [heq]
          have hright : g / 3 ∈
              (((R.mouth, R.firstArm) :: R.candy).map passageSwitch) := by
            apply List.mem_map.mpr
            exact ⟨(R.mouth, R.firstArm), List.mem_cons_self,
              by simp [passageSwitch, hmouthSwitch]⟩
          have hs := R.simple
          unfold SwitchSimple at hs
          rw [List.map_append] at hs
          have hparts := List.nodup_append.mp hs
          exact hparts.2.2 (g / 3) hleft (g / 3) hright rfl
  | stay R =>
      change R.arm ≠ g
      intro heq
      obtain ⟨after, hcoreHead⟩ := R.coreTrace.head_arrive.2
      have harmSwitch : R.arm / 3 = R.mouth / 3 := by
        have hs := arrive_exit_switch R.mouthState R.mouth
        rw [hcoreHead] at hs
        exact hs
      cases hrunway : R.runway with
      | nil =>
          have htrace := R.runwayTrace
          rw [hrunway] at htrace
          have hcfg : (g, R.base) = (R.mouth, R.mouthState) := by
            simpa [stepN] using htrace.sound
          have hgm : g = R.mouth := congrArg Prod.fst hcfg
          have hne := arrive_exit_ne R.mouthState R.mouth
          rw [hcoreHead] at hne
          exact hne (heq.trans hgm)
      | cons passage rest =>
          rcases passage with ⟨p, x⟩
          have htrace := R.runwayTrace
          rw [hrunway] at htrace
          have hgp : g = p := htrace.head_arrive.1
          have hleft : g / 3 ∈ R.runway.map passageSwitch := by
            apply List.mem_map.mpr
            refine ⟨(p, x), ?_, ?_⟩
            · simp [hrunway]
            · simp [passageSwitch, hgp]
          have hmouthSwitch : R.mouth / 3 = g / 3 := by
            rw [← harmSwitch, heq]
          have hright : g / 3 ∈
              ([(R.mouth, R.arm)].map passageSwitch) := by
            simp [passageSwitch, hmouthSwitch]
          have hs := R.simple
          unfold SwitchSimple at hs
          rw [List.map_append] at hs
          have hparts := List.nodup_append.mp hs
          exact hparts.2.2 (g / 3) hleft (g / 3) hright rfl

/-! ## A changed incoming-stem switch would force an impossible return -/

/-- A genuinely changing exploration passage at the switch of the incoming
stem edge is impossible.  Such a passage is trailing, so it exits through
that stem and the immutable edge returns immediately to the exploration's
start port.  A remaining suffix repeats the start switch; an empty suffix
contradicts `preReturn_port_ne_start`. -/
theorem ManufacturedReflector.changed_entry_switch_passage_false
    {w : Wiring} {g e : Nat} (A : ManufacturedReflector w g e)
    (hstem : e = 3 * (e / 3))
    {before after : List Passage} {p x : Nat} {u v : Tongues}
    (hsplit : A.exploration = before ++ (p, x) :: after)
    (hbefore : PhysicalTrace w (g, A.baseState) before (p, u))
    (harrive : arrive u p = (x, v))
    (hswitch : p / 3 = e / 3)
    (hchanged : v (p / 3) ≠ u (p / 3)) : False := by
  obtain ⟨_hpBranch, hxStem, _hv, _hback⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hxe : x = e := by
    rw [hxStem, hswitch, ← hstem]
  have hfull := A.exploration_trace
  rw [hsplit] at hfull
  obtain ⟨middle, hprefix, hrest⟩ := hfull.split_append
  have hmiddle : middle = (p, u) := by
    apply Option.some.inj
    exact hprefix.sound.symm.trans hbefore.sound
  subst middle
  cases hrest with
  | @cons _ _ next _ nextState _ _ harrive' hlink tail =>
      have hnext : next = g := by
        rw [hxe, A.entryEdge] at hlink
        exact (Option.some.inj hlink).symm
      subst next
      cases hafter : after with
      | nil =>
          have htail : (g, nextState) = A.preReturn := by
            have hs := tail.sound
            rw [hafter] at hs
            simpa [stepN] using Option.some.inj hs
          exact A.preReturn_port_ne_start
            (by simpa using congrArg Prod.fst htail.symm)
      | cons passage rest =>
          rcases passage with ⟨q, y⟩
          have htail' : PhysicalTrace w (g, nextState)
              ((q, y) :: rest) A.preReturn := by
            simpa [hafter] using tail
          have hgq : g = q := htail'.head_arrive.1
          have hsplit' : A.exploration =
              (before ++ [(p, x)]) ++ ((q, y) :: rest) := by
            rw [hsplit, hafter]
            simp [List.append_assoc]
          have hsimple := A.exploration_simple
          rw [hsplit'] at hsimple
          unfold SwitchSimple at hsimple
          rw [List.map_append] at hsimple
          have hparts := List.nodup_append.mp hsimple
          have hleft : g / 3 ∈
              (before ++ [(p, x)]).map passageSwitch := by
            cases hbeforeList : before with
            | nil =>
                have hpEq : p = g := by
                  have hs := hbefore.sound
                  rw [hbeforeList] at hs
                  have hcfg : (g, A.baseState) = (p, u) := by
                    simpa [stepN] using Option.some.inj hs
                  exact (congrArg Prod.fst hcfg).symm
                apply List.mem_map.mpr
                exact ⟨(p, x), by simp, by simp [passageSwitch, hpEq]⟩
            | cons first more =>
                rcases first with ⟨a, b⟩
                have hbefore' : PhysicalTrace w (g, A.baseState)
                    ((a, b) :: more) (p, u) := by
                  simpa [hbeforeList] using hbefore
                have hga : g = a := hbefore'.head_arrive.1
                apply List.mem_map.mpr
                exact ⟨(a, b), by simp,
                  by simp [passageSwitch, hga]⟩
          have hright : g / 3 ∈
              (((q, y) :: rest).map passageSwitch) := by
            apply List.mem_map.mpr
            exact ⟨(q, y), List.mem_cons_self,
              by simp [passageSwitch, hgq]⟩
          exact hparts.2.2 (g / 3) hleft (g / 3) hright rfl

/-- Activation of an opposite manufactured reflector cannot change the
switch owning its incoming canonical stem when another branch of that switch
is self-linked.  The self-link itself is used only to exclude the flip action
at that switch; exploration changes are ruled out by the preceding theorem. -/
theorem ManufacturedReflector.activated_entry_switch_eq_base
    {w : Wiring} {g branch : Nat}
    (A : ManufacturedReflector w g (3 * (branch / 3)))
    (hbranch : branch % 3 ≠ 0)
    (hself : w.link branch = some branch) :
    A.activatedState (branch / 3) = A.baseState (branch / 3) := by
  apply Classical.byContradiction
  intro hchange
  cases A with
  | flip R =>
      have hloc :=
        ManufacturedReflector.activated_change_location_strict
          (ManufacturedReflector.flip R) hchange
      rcases hloc with hreturn | hexploration
      · have haction : R.actionSwitch = branch / 3 := by
          calc
            R.actionSwitch = R.secondArm / 3 := R.secondArm_switch.symm
            _ = branch / 3 := hreturn.symm
        exact (R.actionSwitch_ne_self_link hbranch hself) haction
      · obtain ⟨before, p, x, after, u, v, hsplit, hswitch,
          hbefore, harrive, _hu, _hv, hchanged, _hforeign⟩ := hexploration
        have hswitch0 : p / 3 = branch / 3 := by
          simpa [passageSwitch] using hswitch
        have hswitch' : p / 3 = (3 * (branch / 3)) / 3 := by
          omega
        have hchanged' : v (p / 3) = u (p / 3) -> False := by
          simpa [hswitch0] using hchanged
        exact ManufacturedReflector.changed_entry_switch_passage_false
          (ManufacturedReflector.flip R) (by omega)
            hsplit hbefore harrive hswitch' hchanged'
  | stay R =>
      have hloc :=
        PhysicalTrace.changed_switch_has_changed_passage
          (ManufacturedReflector.stay R).exploration_trace
          (ManufacturedReflector.stay R).exploration_simple hchange
      obtain ⟨before, p, x, after, u, v, hsplit, hswitch,
        hbefore, harrive, _hu, _hv, hchanged⟩ := hloc
      have hswitch0 : p / 3 = branch / 3 := by
        simpa [passageSwitch] using hswitch
      have hswitch' : p / 3 = (3 * (branch / 3)) / 3 := by
        omega
      have hchanged' : v (p / 3) = u (p / 3) -> False := by
        simpa [hswitch0] using hchanged
      exact ManufacturedReflector.changed_entry_switch_passage_false
        (ManufacturedReflector.stay R) (by omega)
          hsplit hbefore harrive hswitch' hchanged'

/-- The activated opposite reflector returned by the raw first-revisit fork
therefore still selects the original self-linked branch. -/
theorem RawCycleThroughSelfLink.opposite_reflector_state_selected
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close)
    {outside : Nat}
    (A : ManufacturedReflector w outside (3 * (R.branch / 3)))
    (state : Tongues)
    (hbase : A.baseState = R.state)
    (hstate : state = A.activatedState) :
    state (R.branch / 3) = bval R.branch := by
  calc
    state (R.branch / 3) = A.activatedState (R.branch / 3) :=
      congrFun hstate (R.branch / 3)
    _ = A.baseState (R.branch / 3) :=
      A.activated_entry_switch_eq_base R.branch_port R.self_link
    _ = R.state (R.branch / 3) := congrFun hbase (R.branch / 3)
    _ = bval R.branch := R.self_selected

end GeneralN
