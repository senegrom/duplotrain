import SharpCertificateClosure

/-!
# Retaining and closing the simple-cycle self-link branch

SettlesOnSimpleCycle records only period endpoints. For quantitative novelty
accounting we retain the physical transient and stable switch-simple cycle
traces produced by the first-revisit proof itself.
-/

namespace GeneralN

/-- Same-exit cycle closure with the transient two-phase law retained. -/
theorem PhysicalTrace.simple_same_exit_cycle_traces_with_phase
    {w : Wiring} {p x q : Nat} {u₀ u v : Tongues}
    {rest : List Passage}
    (htrace : PhysicalTrace w (p, u₀) ((p, x) :: rest) (q, u))
    (hsimple : SwitchSimple ((p, x) :: rest))
    (hnext : arrive u q = (x, v)) :
    PhysicalTrace w (q, u) ((q, x) :: rest) (q, v) ∧
      PhysicalTrace w (q, v) ((q, x) :: rest) (q, v) ∧
      SwitchSimple ((q, x) :: rest) ∧
      (∀ d, d ≤ ((q, x) :: rest).length → ∃ port phase,
        stepN w d (q, u) = some (port, phase) ∧
          (phase = u ∨ phase = v)) := by
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
    cases hstable with
    | @cons _ _ next _ nextState _ _ ha hl tail =>
        have heq : nextState = v := by
          have hf := groove_forward hheadNew
          exact congrArg Prod.snd (ha.symm.trans hf)
        exact PhysicalTrace.cons hnext hl (by simpa only [heq] using tail)
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
  have hphase : ∀ d, d ≤ ((q, x) :: rest).length → ∃ port phase,
      stepN w d (q, u) = some (port, phase) ∧ (phase = u ∨ phase = v) := by
    intro d hd
    cases d with
    | zero => exact ⟨q, u, rfl, Or.inl rfl⟩
    | succ n =>
        obtain ⟨port, hr⟩ := hstable.grooved_prefix_tongues v hnewGrooved hd
        exact ⟨port, v, (stepN_after_arrival hnext (by omega)).trans hr, Or.inr rfl⟩
  exact ⟨htransient, hstable, hsimpleCycle, hphase⟩

/-- Split a long run at its first revisit and apply the activated normal
form: after a switch-simple lead, either a two-phase simple cycle follows or
a manufactured reflector is activated. -/
theorem first_revisit_fork
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    ∃ (lead : List Passage) (q : Nat) (u : Tongues),
      PhysicalTrace w start lead (q, u) ∧ SwitchSimple lead ∧
      ((∃ cycle settled, cycle ≠ [] ∧
          PhysicalTrace w (q, u) cycle (q, settled) ∧
          PhysicalTrace w (q, settled) cycle (q, settled) ∧
          SwitchSimple cycle ∧
          (∀ d, d ≤ cycle.length → ∃ port phase,
            stepN w d (q, u) = some (port, phase) ∧
              (phase = u ∨ phase = settled)) ∧
          (∀ d, 0 < d → ∃ port, stepN w d (q, u) = some (port, settled))) ∨
        (∃ (A : ManufacturedReflector w start.1 e) (state : Tongues),
          PathGrooves A.toSupported.paths state ∧
          A.baseState = start.2 ∧
          state = A.activatedState ∧
          (∀ j, j ∉ A.exploration.map passageSwitch → state j = start.2 j))) := by
  obtain ⟨before, old, repeated, after, middle,
      hbeforeTrace, hafterTrace, hsimple, hold, hsameSwitch⟩ :=
    first_revisit_of_long_run hN hlive
  obtain ⟨runway, path, hsplit⟩ := List.append_of_mem hold
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  subst before
  obtain ⟨atOld, hrunway, hexcursion⟩ := hbeforeTrace.split_append
  have hatOldPort : atOld.1 = p := hexcursion.head_arrive.1
  rcases atOld with ⟨oldPort, u₀⟩
  simp only at hatOldPort
  subst oldPort
  obtain ⟨v, hrepeat⟩ := hafterTrace.head_arrive.2
  have hmiddlePort : middle.1 = q := hafterTrace.head_arrive.1
  rcases middle with ⟨middlePort, u⟩
  simp only at hmiddlePort
  subst middlePort
  have hsw : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  refine ⟨_, _, _, hbeforeTrace, hsimple, ?_⟩
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
  by_cases hxq : x = q
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
    refine Or.inr ⟨.stay A, u, ?_, rfl, rfl, ?_⟩
    · change PathGrooves [runway, [(p, x)]] u
      apply pathGrooves_pair.mpr
      exact ⟨(pathGrooves_pair.mp hsupport).1,
        passagesGrooved_singleton.mpr holdGroove⟩
    · simpa [ManufacturedReflector.exploration] using hpreserves
  rcases hshare with hpq | hpy | hxq' | hxy
  · subst q
    left
    have hgrooved :=
      hexcursion.grooved_of_switchSimple hsimpleExcursion
    have hstable : PhysicalTrace w (p, u) ((p, x) :: path) (p, u) :=
      physicalTrace_grooved_passages w u p x p path
        hexcursion.linked hgrooved hexcursion.last_link
    have hphase : forall d, d ≤ ((p, x) :: path).length ->
        exists port phase,
        stepN w d (p, u) = some (port, phase) /\
          (phase = u \/ phase = u) := by
      intro d hd
      obtain ⟨port, hrun⟩ :=
        hstable.grooved_prefix_tongues u hgrooved hd
      exact ⟨port, u, hrun, Or.inl rfl⟩
    have hall : forall d, exists port,
        stepN w d (p, u) = some (port, u) :=
      hstable.grooved_loop_all_time (by simp) hgrooved
    exact ⟨(p, x) :: path, u, by simp, hstable, hstable,
      hsimpleExcursion, hphase, fun d _ => hall d⟩
  · subst y
    let A : ManufacturedFlipReflector w start.1 e := {
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
    refine Or.inr ⟨.flip A, v, ?_, rfl, rfl, ?_⟩
    · change PathGrooves [runway, path] v
      exact hsupport
    · simpa [ManufacturedReflector.exploration] using hpreserves
  · exact absurd hxq' hxq
  · subst y
    left
    obtain ⟨htransient, hstable, hsimpleCycle, hphase⟩ :=
      hexcursion.simple_same_exit_cycle_traces_with_phase
        hsimpleExcursion hrepeat
    exact ⟨(q, x) :: path, v, by simp, htransient, hstable,
      hsimpleCycle, hphase, fun d hpositive => by
        obtain ⟨port, hr⟩ := hstable.grooved_loop_all_time (by simp)
          (hstable.grooved_of_switchSimple hsimpleCycle) d
        exact ⟨port, (stepN_after_arrival hrepeat hpositive).trans hr⟩⟩

end GeneralN
