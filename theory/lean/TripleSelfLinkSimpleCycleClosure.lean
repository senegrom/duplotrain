import TripleSelfLinkRawTail

/-!
# Retaining and closing the simple-cycle self-link branch

SettlesOnSimpleCycle records only period endpoints. For quantitative novelty
accounting we retain the physical transient and stable switch-simple cycle
traces produced by the first-revisit proof itself.
-/

namespace GeneralN

/-- Exact transient and stable traces for the same-exit simple-cycle case. -/
theorem PhysicalTrace.simple_same_exit_cycle_traces_public
    {w : Wiring} {p x q : Nat} {u₀ u v : Tongues}
    {rest : List Passage}
    (htrace : PhysicalTrace w (p, u₀) ((p, x) :: rest) (q, u))
    (hsimple : SwitchSimple ((p, x) :: rest))
    (hnext : arrive u q = (x, v)) :
    PhysicalTrace w (q, u) ((q, x) :: rest) (q, v) /\
      PhysicalTrace w (q, v) ((q, x) :: rest) (q, v) /\
      SwitchSimple ((q, x) :: rest) := by
  have holdGrooved := htrace.grooved_of_switchSimple hsimple
  have holdLinked := htrace.linked
  have hfinal : w.link (lastPassageExit x rest) = some q :=
    htrace.last_link
  have hheadOld : arrive u x = (p, u) :=
    holdGrooved (p, x) (by simp)
  have hpx : p / 3 = x / 3 := by
    have hs := arrive_exit_switch u x
    rw [hheadOld] at hs
    exact hs
  have hqx : x / 3 = q / 3 := by
    have hs := arrive_exit_switch u q
    rw [hnext] at hs
    exact hs
  unfold SwitchSimple at hsimple
  simp only [List.map_cons, List.nodup_cons] at hsimple
  have hrestGrooved : PassagesGrooved v rest := by
    intro passage hp
    have hold := holdGrooved passage (List.mem_cons_of_mem _ hp)
    have hpassageSwitch : passageSwitch passage ≠ p / 3 := by
      intro hEq
      apply hsimple.1
      apply List.mem_map.mpr
      exact ⟨passage, hp, hEq⟩
    have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch u passage.2
      rw [hold] at hs
      exact hs.symm
    have hforeign : passage.2 / 3 ≠ q / 3 := by
      rw [hexitSwitch, ← hqx, ← hpx]
      exact hpassageSwitch
    have hsame : v (passage.2 / 3) = u (passage.2 / 3) :=
      arrive_preserves_other hnext hforeign
    exact groove_transfer hold hsame
  have hheadNew : arrive v x = (q, v) := by
    have hb := arrive_back u q
    rw [hnext] at hb
    exact hb
  have hnewGrooved : PassagesGrooved v ((q, x) :: rest) := by
    intro passage hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadNew
    · exact hrestGrooved passage htail
  have hnewLinked : LinkedPassages w ((q, x) :: rest) := by
    cases rest with
    | nil => trivial
    | cons passage rest =>
        simpa [LinkedPassages] using holdLinked
  have hstable : PhysicalTrace w (q, v) ((q, x) :: rest) (q, v) :=
    physicalTrace_grooved_passages w v q x q rest
      hnewLinked hnewGrooved hfinal
  have htransient : PhysicalTrace w (q, u) ((q, x) :: rest) (q, v) := by
    cases rest with
    | nil =>
        exact PhysicalTrace.cons hnext
          (by simpa [lastPassageExit] using hfinal)
          (PhysicalTrace.nil (q, v))
    | cons passage rest =>
        rcases passage with ⟨r, y⟩
        have hxy : w.link x = some r := holdLinked.1
        have htailLinked : LinkedPassages w ((r, y) :: rest) :=
          hnewLinked.2
        have htailGrooved : PassagesGrooved v ((r, y) :: rest) := by
          intro passage hp
          exact hnewGrooved passage (List.mem_cons_of_mem _ hp)
        have htailFinal : w.link (lastPassageExit y rest) = some q := by
          simpa [lastPassageExit] using hfinal
        exact PhysicalTrace.cons hnext hxy
          (physicalTrace_grooved_passages w v r y q rest
            htailLinked htailGrooved htailFinal)
  have hsimpleCycle : SwitchSimple ((q, x) :: rest) := by
    unfold SwitchSimple
    simp only [List.map_cons, passageSwitch]
    have hpq : p / 3 = q / 3 := hpx.trans hqx
    constructor
    · intro a ha hEq
      apply hsimple.1
      have hheadEq : passageSwitch (p, x) = a := by
        calc
          passageSwitch (p, x) = p / 3 := rfl
          _ = q / 3 := hpq
          _ = a := hEq
      rw [hheadEq]
      exact ha
    · exact hsimple.2
  exact ⟨htransient, hstable, hsimpleCycle⟩

/-- Trace-retaining form of the activated first-revisit normal form. -/
theorem first_revisit_cycle_traces_or_activated_reflector
    (w : Wiring) {start : Prod Nat Tongues}
    {runway path : List Passage}
    {p x q y e : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hexcursion :
      PhysicalTrace w (p, u₀) ((p, x) :: path) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: path))
    (hsw : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v))
    (hentry : w.link e = some start.1) :
    (exists cycle settled,
      cycle ≠ [] /\
      PhysicalTrace w (q, u) cycle (q, settled) /\
      PhysicalTrace w (q, settled) cycle (q, settled) /\
      SwitchSimple cycle) \/
    (exists (A : ManufacturedReflector w start.1 e) (state : Tongues),
      PathGrooves A.toSupported.paths state /\
      A.baseState = start.2 /\
      state = A.activatedState /\
      stepN w (runway.length + 1) (q, u) = some (e, state) /\
      (forall j, j ∉ A.exploration.map passageSwitch ->
        state j = start.2 j)) := by
  have hsimpleExcursion : SwitchSimple ((p, x) :: path) := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).2.1
  have holdStem :
      p = 3 * passageSwitch (p, x) \/
        x = 3 * passageSwitch (p, x) :=
    hexcursion.passage_stem_endpoint (p, x) List.mem_cons_self
  have hrepeatStem :
      q = 3 * passageSwitch (q, y) \/
        y = 3 * passageSwitch (q, y) := by
    have hs := arrive_stem_endpoint u q
    rw [hrepeat] at hs
    exact hs
  have hsw' : passageSwitch (p, x) = passageSwitch (q, y) := by
    simpa [passageSwitch] using hsw
  have hshare : p = q \/ p = y \/ x = q \/ x = y :=
    recorded_passages_share_port holdStem hrepeatStem hsw'
  have hfar : w.link start.1 = some e := w.symm _ _ hentry
  have hsupport := crossed_revisit_support_grooved
    hrunway hexcursion hsimple hsw hrepeat
  have hpreserves :
      forall j, j ∉ (runway ++ (p, x) :: path).map passageSwitch ->
        v j = start.2 j := by
    intro j hforeign
    have hu := (hrunway.append hexcursion).preserves j (by
      intro passage hp hEq
      apply hforeign
      exact List.mem_map.mpr ⟨passage, hp, hEq⟩)
    have hjq : j ≠ q / 3 := by
      intro hEq
      apply hforeign
      apply List.mem_map.mpr
      refine ⟨(p, x), List.mem_append_right runway List.mem_cons_self, ?_⟩
      simp only [passageSwitch]
      omega
    exact (arrive_preserves_other hrepeat hjq).trans hu
  rcases hshare with hpq | hpy | hxq | hxy
  · subst q
    left
    have hgrooved :=
      hexcursion.grooved_of_switchSimple hsimpleExcursion
    have hstable : PhysicalTrace w (p, u) ((p, x) :: path) (p, u) :=
      physicalTrace_grooved_passages w u p x p path
        hexcursion.linked hgrooved hexcursion.last_link
    exact ⟨(p, x) :: path, u, by simp, hstable, hstable, hsimpleExcursion⟩
  · subst y
    have hback := hrunway.simple_cross_exit_retraces_prefix
      hexcursion hsimple hrepeat
    rw [hfar] at hback
    by_cases hxq : x = q
    · subst q
      have hpathNil := same_exit_excursion_path_nil
        hexcursion hsimpleExcursion
      subst path
      have hfullGrooved :=
        (hrunway.append hexcursion).grooved_of_switchSimple hsimple
      have hold : arrive u x = (p, u) :=
        hfullGrooved (p, x)
          (List.mem_append_right runway List.mem_cons_self)
      have holdGroove := hold
      rw [hrepeat] at hold
      injection hold with _ huv
      subst v
      have hself : w.link x = some x := by
        simpa [lastPassageExit] using hexcursion.last_link
      let A : ManufacturedStayReflector w start.1 e := {
        base := start.2
        mouthState := u₀
        returnState := u
        runway := runway
        mouth := p
        arm := x
        runwayTrace := by simpa using hrunway
        coreTrace := by simpa using hexcursion
        simple := hsimple
        stemEndpoint := hexcursion.passage_stem_endpoint
          (p, x) List.mem_cons_self
        selfLink := hself
        entryEdge := hentry
      }
      refine Or.inr ⟨.stay A, u, ?_, rfl, rfl, hback, ?_⟩
      change PathGrooves [runway, [(p, x)]] u
      apply pathGrooves_pair.mpr
      exact ⟨(pathGrooves_pair.mp hsupport).1,
        passagesGrooved_singleton.mpr holdGroove⟩
      simpa [ManufacturedReflector.exploration] using hpreserves
    · let A : ManufacturedFlipReflector w start.1 e := {
        base := start.2
        mouthState := u₀
        returnState := u
        afterReturn := v
        runway := runway
        candy := path
        mouth := p
        firstArm := x
        secondArm := q
        runwayTrace := by simpa using hrunway
        candyTrace := hexcursion
        simple := hsimple
        crossed := hrepeat
        arms_ne := hxq
        entryEdge := hentry
      }
      refine Or.inr ⟨.flip A, v, ?_, rfl, rfl, hback, ?_⟩
      change PathGrooves [runway, path] v
      exact hsupport
      simpa [ManufacturedReflector.exploration] using hpreserves
  · subst q
    have hfull := hrunway.append hexcursion
    have hgrooved := hfull.grooved_of_switchSimple hsimple
    have hold : arrive u x = (p, u) :=
      hgrooved (p, x)
        (List.mem_append_right runway List.mem_cons_self)
    have holdGroove := hold
    rw [hrepeat] at hold
    injection hold with hyp huv
    subst y
    subst v
    have hback := hrunway.simple_cross_exit_retraces_prefix
      hexcursion hsimple (by simpa using hrepeat)
    rw [hfar] at hback
    have hpathNil := same_exit_excursion_path_nil
      hexcursion hsimpleExcursion
    subst path
    have hself : w.link x = some x := by
      simpa [lastPassageExit] using hexcursion.last_link
    let A : ManufacturedStayReflector w start.1 e := {
      base := start.2
      mouthState := u₀
      returnState := u
      runway := runway
      mouth := p
      arm := x
      runwayTrace := by simpa using hrunway
      coreTrace := by simpa using hexcursion
      simple := hsimple
      stemEndpoint := hexcursion.passage_stem_endpoint
        (p, x) List.mem_cons_self
      selfLink := hself
      entryEdge := hentry
    }
    refine Or.inr ⟨.stay A, u, ?_, rfl, rfl, hback, ?_⟩
    change PathGrooves [runway, [(p, x)]] u
    apply pathGrooves_pair.mpr
    exact ⟨(pathGrooves_pair.mp hsupport).1,
      passagesGrooved_singleton.mpr holdGroove⟩
    simpa [ManufacturedReflector.exploration] using hpreserves
  · subst y
    left
    obtain ⟨htransient, hstable, hsimpleCycle⟩ :=
      hexcursion.simple_same_exit_cycle_traces_public hsimpleExcursion hrepeat
    exact ⟨(q, x) :: path, v, by simp,
      htransient, hstable, hsimpleCycle⟩

end GeneralN
