import SharpCertificateClosure

/-!
# Retaining and closing the simple-cycle self-link branch

A cycle branch settles at its first arrival. Its positive-time constant-vector
contract is all downstream counting needs; the other branch retains the
manufactured reflector and its construction history.
-/

namespace GeneralN

/-- A same-exit revisit installs a grooved loop at its very first arrival. -/
theorem PhysicalTrace.simple_same_exit_cycle_all_time
    {w : Wiring} {p x q : Nat} {u₀ u v : Tongues} {rest : List Passage}
    (htrace : PhysicalTrace w (p, u₀) ((p, x) :: rest) (q, u))
    (hsimple : SwitchSimple ((p, x) :: rest))
    (hnext : arrive u q = (x, v)) :
    ∀ d, 0 < d → ∃ port, stepN w d (q, u) = some (port, v) := by
  have hold := htrace.grooved_of_switchSimple hsimple
  have hhead := hold (p, x) List.mem_cons_self
  have hpx := arrive_exit_switch u x
  have hqx := arrive_exit_switch u q
  rw [hhead] at hpx
  rw [hnext] at hqx
  have hrest : PassagesGrooved v rest := by
    apply PassagesGrooved.transfer
      (fun passage hp => hold passage (List.mem_cons_of_mem _ hp))
    intro passage hp
    apply arrive_preserves_other hnext
    intro heq
    have hs := hsimple
    simp only [SwitchSimple, List.map_cons, List.nodup_cons] at hs
    exact hs.1 (List.mem_map.mpr ⟨passage, hp, by
      change passageSwitch passage = p / 3
      omega⟩)
  have hg : PassagesGrooved v ((q, x) :: rest) := by
    intro passage hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simpa only [hnext] using arrive_back u q
    · exact hrest passage hp
  have hl : LinkedPassages w ((q, x) :: rest) := by
    have h := htrace.linked
    cases rest <;> simp_all [LinkedPassages]
  have hstable := physicalTrace_grooved_passages w v q x q rest hl hg htrace.last_link
  intro d hd
  obtain ⟨port, hr⟩ := hstable.grooved_loop_all_time (by simp) hg d
  exact ⟨port, (stepN_after_arrival hnext hd).trans hr⟩

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
      ((∃ settled, ∀ d, 0 < d → ∃ port,
          stepN w d (q, u) = some (port, settled)) ∨
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
    exact ⟨u, fun d _ => hstable.grooved_loop_all_time (by simp) hgrooved d⟩
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
    exact ⟨v, hexcursion.simple_same_exit_cycle_all_time hsimpleExcursion hrepeat⟩

end GeneralN
