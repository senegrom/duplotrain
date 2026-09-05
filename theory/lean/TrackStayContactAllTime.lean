import TrackThetaPointwiseCore

/-!
# Absolute phase law for a flip reflector meeting a stay reflector

The intersecting stay/flip cases were the last reflector-pair geometries still
charged by physical travel.  They actually have only two tongue phases.  The
flip traversal creates one alternate vector; the disturbed stay traversal
either captures that flip or repairs it at the unique contacted passage, and
all remaining motion is grooved in the original vector.
-/

namespace GeneralN

theorem stay_twoPhase_concat
    {w : Wiring} {start middle : Nat × Tongues}
    {left right : Nat} {u v : Tongues}
    (hleft : stepN w left start = some middle)
    (hleftPhase : ∀ d, d ≤ left → ∃ port phase,
      stepN w d start = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (hrightPhase : ∀ d, d ≤ right → ∃ port phase,
      stepN w d middle = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (d : Nat) (hd : d ≤ left + right) :
    ∃ port phase, stepN w d start = some (port, phase) ∧
      (phase = u ∨ phase = v) := by
  by_cases hdl : d ≤ left
  · exact hleftPhase d hdl
  · let r := d - left
    have hr : r ≤ right := by
      dsimp [r]
      omega
    have hdecomp : d = left + r := by
      dsimp [r]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hrightPhase r hr
    refine ⟨port, phase, ?_, hphase⟩
    rw [hdecomp, stepN_add, hleft]
    exact hrun

/-- A complete manufactured stay-reflector traversal carries its incoming
vector at every intermediate time. -/
theorem ManufacturedStayReflector.travel_state_stepN
    {w : Wiring} {g e : Nat}
    (B : ManufacturedStayReflector w g e)
    (state : Tongues)
    (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
    {d : Nat} (hd : d ≤ 2 * B.runway.length + 2) :
    ∃ port, stepN w d (g, state) = some (port, state) := by
  have hpaths : PathGrooves
      (ManufacturedReflector.stay B).toSupported.paths state := hB
  have hrun :=
    ((ManufacturedReflector.stay B).toSupported.run state hpaths).1
  have hd' : d ≤ (ManufacturedReflector.stay B).toSupported.travel := hd
  obtain ⟨middle, hmiddle⟩ := stepN_prefix_some hd' hrun
  rcases middle with ⟨port, phase⟩
  have hphase :=
    (ManufacturedReflector.stay B).travel_two_phase_tongues
      state hpaths hd'
  have hseen : tonguesAt w (g, state) d = phase := by
    simp [tonguesAt, hmiddle]
  have hphaseState : phase = state := by
    rcases hphase with h | h
    · exact hseen.symm.trans h
    · have h' : tonguesAt w (g, state) d = state := by
        simpa [ManufacturedReflector.toSupported,
          ManufacturedStayReflector.toSupported, LocalAction.apply] using h
      exact hseen.symm.trans h'
  exact ⟨port, by simpa [hphaseState] using hmiddle⟩

/-- Pointwise form of the generic disturbed-runway dichotomy when the normal
traversal is tongue-constant. -/
theorem runway_fault_dichotomy_general_pointwise_stay
    {w : Wiring} {g e total tailSteps : Nat}
    (A : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    {base : Tongues} {runway : List Passage}
    {newFinish finish : Nat × Tongues}
    (htrace : PhysicalTrace w (e, base) runway newFinish)
    (hgrooved : PassagesGrooved state runway)
    (hsimple : SwitchSimple runway)
    (passage : Passage)
    {before after : List Passage}
    (hoccurs : runway = before ++ passage :: after)
    (hsw : passageSwitch passage = A.actionSwitch)
    (hdecomp : total = before.length + 1 + tailSteps)
    (hnormal : stepN w total (e, state) = some finish)
    (hnormalPhase : ∀ d, d ≤ total →
      ∃ port, stepN w d (e, state) = some (port, state)) :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) ∨
    (stepN w total (e, flipAt state A.actionSwitch) = some finish ∧
      ∀ d, d ≤ total → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) := by
  rcases passage with ⟨p, x⟩
  have hmem : (p, x) ∈ runway := by
    rw [hoccurs]
    exact List.mem_append_right before List.mem_cons_self
  have hprefixData := simple_grooved_trace_prefix_to_occurrence
    htrace hoccurs hgrooved hsimple
  have hstem := htrace.passage_stem_endpoint (p, x) hmem
  change p = 3 * (p / 3) ∨ x = 3 * (p / 3) at hstem
  change p / 3 = A.actionSwitch at hsw
  have hmouth : A.mouth = 3 * A.actionSwitch := by
    have hs := A.mouth_is_stem
    unfold ManufacturedFlipReflector.actionSwitch
    omega
  rcases hstem with hp | hx
  · have hpMouth : p = A.mouth := by omega
    subst p
    left
    have hforeign : ∀ old ∈ before,
        passageSwitch old ≠ A.actionSwitch := by
      intro old hold
      have hne := hprefixData.2 old hold
      simpa [passageSwitch,
        ManufacturedFlipReflector.actionSwitch] using hne
    have hbeforeSimple : SwitchSimple before := by
      unfold SwitchSimple at hsimple ⊢
      rw [hoccurs] at hsimple
      simp only [List.map_append, List.map_cons] at hsimple
      exact (List.nodup_append.mp hsimple).1
    have hbeforeGrooved : PassagesGrooved state before :=
      hprefixData.1.grooved_of_switchSimple hbeforeSimple
    have hbeforeGroovedFlip :
        PassagesGrooved (flipAt state A.actionSwitch) before :=
      grooved_after_flip_other hbeforeGrooved hforeign
    have hbeforeFlip := hprefixData.1.flip_unvisited hforeign
    have hcapture := A.capture_from_mouth state
      (pathGrooves_pair.mp hA).1 (pathGrooves_pair.mp hA).2
    let capture := A.candy.length + 2 + A.runway.length
    let travel := before.length + capture
    have htravel : stepN w travel
        (e, flipAt state A.actionSwitch) = some (e, state) := by
      dsimp [travel, capture]
      exact theta_capture_after_unvisited_prefix
        hprefixData.1 hforeign hcapture
    refine ⟨travel, htravel, ?_⟩
    intro d hd
    by_cases hdpre : d ≤ before.length
    · obtain ⟨port, hrun⟩ :=
        hbeforeFlip.grooved_prefix_tongues
          (flipAt state A.actionSwitch) hbeforeGroovedFlip hdpre
      exact ⟨port, flipAt state A.actionSwitch, hrun, Or.inl rfl⟩
    · let r := d - before.length
      have hr : r ≤ capture := by
        dsimp [travel] at hd
        dsimp [r]
        omega
      have hdecomp' : d = before.length + r := by
        dsimp [r]
        omega
      obtain ⟨port, phase, hrun, hphase⟩ :=
        A.capture_from_mouth_two_phase state
          (pathGrooves_pair.mp hA).1
          (pathGrooves_pair.mp hA).2 (by
            simpa [capture] using hr)
      refine ⟨port, phase, ?_, hphase⟩
      rw [hdecomp', stepN_add, hbeforeFlip.sound]
      exact hrun
  · have hgrooveBack : arrive state x = (p, state) :=
      hgrooved (p, x) hmem
    have hforward : arrive state p = (x, state) :=
      groove_forward hgrooveBack
    have hpbranch : p % 3 ≠ 0 := by
      intro hpmod
      have hne := arrive_exit_ne state p
      rw [hforward] at hne
      apply hne
      omega
    have hforeign : ∀ old ∈ before,
        passageSwitch old ≠ A.actionSwitch := by
      intro old hold
      have hne := hprefixData.2 old hold
      simpa [passageSwitch, hsw] using hne
    obtain ⟨q, hlink⟩ : ∃ q, w.link x = some q := by
      cases after with
      | nil =>
          have htrace' := htrace
          rw [hoccurs] at htrace'
          obtain ⟨middle, hbeforeTrace, htargetTrace⟩ :=
            htrace'.split_append
          have hlast := htargetTrace.last_link
          exact ⟨newFinish.1,
            by simpa [lastPassageExit] using hlast⟩
      | cons next rest =>
          rcases next with ⟨q, y⟩
          have hlinked : LinkedPassages w
              (before ++ (p, x) :: (q, y) :: rest) := by
            rw [← hoccurs]
            exact htrace.linked
          exact ⟨q, linked_after_occurrence hlinked⟩
    have htarget : PhysicalTrace w (p, state)
        [(p, x)] (q, state) :=
      PhysicalTrace.cons hforward hlink (PhysicalTrace.nil _)
    have hprefixTarget := hprefixData.1.append htarget
    have hsuffix : stepN w tailSteps (q, state) = some finish := by
      have hprefixLen :
          (before ++ [(p, x)]).length = before.length + 1 := by simp
      apply suffix_after_physical_prefix hprefixTarget
      · simpa [hprefixLen] using hdecomp
      · exact hnormal
    have hrepair := flipped_prefix_trailing_then hprefixData.1 hforeign
      hsw hpbranch hforward hlink hsuffix
    have hendpoint : stepN w total
        (e, flipAt state A.actionSwitch) = some finish := by
      rwa [← hdecomp] at hrepair
    right
    refine ⟨hendpoint, ?_⟩
    intro d hd
    have hbeforeSimple : SwitchSimple before := by
      unfold SwitchSimple at hsimple ⊢
      rw [hoccurs] at hsimple
      simp only [List.map_append, List.map_cons] at hsimple
      exact (List.nodup_append.mp hsimple).1
    have hbeforeGrooved : PassagesGrooved state before :=
      hprefixData.1.grooved_of_switchSimple hbeforeSimple
    have hbeforeGroovedFlip :
        PassagesGrooved (flipAt state A.actionSwitch) before :=
      grooved_after_flip_other hbeforeGrooved hforeign
    by_cases hdpre : d ≤ before.length
    · obtain ⟨port, hrun⟩ :=
        (hprefixData.1.flip_unvisited hforeign).grooved_prefix_tongues
          (flipAt state A.actionSwitch) hbeforeGroovedFlip hdpre
      exact ⟨port, flipAt state A.actionSwitch, hrun, Or.inl rfl⟩
    · have hone : stepN w 1 (p, state) = some (q, state) := by
        simp [stepN, step, hforward, hlink]
      have hmidGrooved : stepN w (before.length + 1)
          (e, state) = some (q, state) := by
        rw [stepN_add, hprefixData.1.sound]
        simpa using hone
      have hrepairArrive :
          arrive (flipAt state A.actionSwitch) p = (x, state) := by
        rw [← hsw]
        exact flipped_passage_forward_trailing hforward hpbranch
      have honeFlip : stepN w 1
          (p, flipAt state A.actionSwitch) = some (q, state) := by
        simp [stepN, step, hrepairArrive, hlink]
      have hmidFlip : stepN w (before.length + 1)
          (e, flipAt state A.actionSwitch) = some (q, state) := by
        rw [stepN_add, (hprefixData.1.flip_unvisited hforeign).sound]
        simpa using honeFlip
      let r := d - (before.length + 1)
      have hdecomp' : d = (before.length + 1) + r := by
        dsimp [r]
        omega
      have habs : (before.length + 1) + r ≤ total := by
        omega
      obtain ⟨port, hrunAbs⟩ :=
        hnormalPhase ((before.length + 1) + r) habs
      rw [stepN_add, hmidGrooved] at hrunAbs
      simp only [Option.bind_some] at hrunAbs
      refine ⟨port, state, ?_, Or.inr rfl⟩
      rw [hdecomp', stepN_add, hmidFlip]
      exact hrunAbs

section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedFlipReflector w g e)
  (B : ManufacturedStayReflector w e g)
  (state : Tongues)
  (hA : PathGrooves [A.runway, A.candy] state)
  (hB : PathGrooves [B.runway, [(B.mouth, B.arm)]] state)
  (hcontact : ∃ path ∈ [B.runway, [(B.mouth, B.arm)]],
    ∃ passage ∈ path,
      passageSwitch passage = A.actionSwitch)
include w g e A B state hA hB hcontact

/-- Pointwise disturbed-support dichotomy for a stay reflector. -/
theorem manufactured_stay_support_fault_dichotomy_pointwise :
    (∃ travel,
      stepN w travel (e, flipAt state A.actionSwitch) =
        some (e, state) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) ∨
    (stepN w (2 * B.runway.length + 2)
        (e, flipAt state A.actionSwitch) = some (g, state) ∧
      ∀ d, d ≤ 2 * B.runway.length + 2 → ∃ port phase,
        stepN w d (e, flipAt state A.actionSwitch) =
          some (port, phase) ∧
        (phase = flipAt state A.actionSwitch ∨ phase = state)) := by
  have hnormal := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + 2) (e, state) =
      some (g, state) at hnormal
  have hnormalPhase : ∀ d, d ≤ 2 * B.runway.length + 2 →
      ∃ port, stepN w d (e, state) = some (port, state) := by
    intro d hd
    exact B.travel_state_stepN state hB hd
  obtain ⟨path, hp, passage, hmem, hsw⟩ := hcontact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · obtain ⟨before, after, hoccurs⟩ := List.append_of_mem hmem
    have hsimpleRunway : SwitchSimple B.runway := by
      have hs := B.simple
      unfold SwitchSimple at hs ⊢
      simp only [List.map_append] at hs
      exact (List.nodup_append.mp hs).1
    have hRlen : B.runway.length =
        before.length + 1 + after.length := by
      rw [hoccurs]
      simp only [List.length_append, List.length_cons]
      omega
    let tailSteps := after.length + 2 + B.runway.length
    have hdecomp : 2 * B.runway.length + 2 =
        before.length + 1 + tailSteps := by
      dsimp [tailSteps]
      omega
    exact runway_fault_dichotomy_general_pointwise_stay
      (total := 2 * B.runway.length + 2)
      (tailSteps := tailSteps) A state hA B.runwayTrace
      (pathGrooves_pair.mp hB).1 hsimpleRunway passage
      hoccurs hsw hdecomp hnormal hnormalPhase
  · simp only [List.mem_singleton] at hmem
    subst passage
    let route := B.runway ++ [(B.mouth, B.arm)]
    have hrun := B.runway_trace state (pathGrooves_pair.mp hB).1
    have hgrooveBack := passagesGrooved_singleton.mp
      (pathGrooves_pair.mp hB).2
    have hforward := groove_forward hgrooveBack
    have htarget : PhysicalTrace w (B.mouth, state)
        [(B.mouth, B.arm)] (B.arm, state) :=
      PhysicalTrace.cons hforward B.selfLink (PhysicalTrace.nil _)
    have hrouteTrace := hrun.append htarget
    have hrouteGrooved := hrouteTrace.grooved_of_switchSimple B.simple
    have hoccurs : route =
        B.runway ++ (B.mouth, B.arm) :: [] := by rfl
    have hdecomp : 2 * B.runway.length + 2 =
        B.runway.length + 1 + (B.runway.length + 1) := by omega
    exact runway_fault_dichotomy_general_pointwise_stay
      (total := 2 * B.runway.length + 2)
      (tailSteps := B.runway.length + 1) A state hA hrouteTrace
      hrouteGrooved B.simple (B.mouth, B.arm)
      hoccurs hsw hdecomp hnormal hnormalPhase

/-- A flip reflector followed by an intersecting stay reflector has exactly
its original and action-flipped tongue phases for all time. -/
theorem manufactured_flip_then_stay_all_time_two_phase :
    ∀ d, ∃ port phase,
      stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = flipAt state A.actionSwitch) := by
  let alternate := flipAt state A.actionSwitch
  have hArun := (A.toSupported.run state hA).1
  change stepN w (2 * A.runway.length + A.candy.length + 2)
      (g, state) = some (e, alternate) at hArun
  have hAphase : ∀ d,
      d ≤ 2 * A.runway.length + A.candy.length + 2 →
      ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = alternate) := by
    intro d hd
    simpa [alternate] using A.travel_two_phase_stepN state hA hd
  have hBnormal := (B.toSupported.run state hB).1
  change stepN w (2 * B.runway.length + 2) (e, state) =
      some (g, state) at hBnormal
  have hBphase : ∀ d, d ≤ 2 * B.runway.length + 2 →
      ∃ port phase, stepN w d (e, state) = some (port, phase) ∧
        (phase = state ∨ phase = alternate) := by
    intro d hd
    obtain ⟨port, hrun⟩ := B.travel_state_stepN state hB hd
    exact ⟨port, state, hrun, Or.inl rfl⟩
  rcases manufactured_stay_support_fault_dichotomy_pointwise
      A B state hA hB hcontact with hcapture | hrepair
  · obtain ⟨capture, hcaptureEnd, hcapturePhase⟩ := hcapture
    let first := (2 * A.runway.length + A.candy.length + 2) + capture
    let period := first + (2 * B.runway.length + 2)
    have hfirstEnd : stepN w first (g, state) = some (e, state) := by
      dsimp [first]
      rw [stepN_add, hArun]
      exact hcaptureEnd
    have hperiod : stepN w period (g, state) = some (g, state) := by
      dsimp [period]
      rw [stepN_add, hfirstEnd]
      exact hBnormal
    have hfirstPhase : ∀ d, d ≤ first → ∃ port phase,
        stepN w d (g, state) = some (port, phase) ∧
          (phase = state ∨ phase = alternate) := by
      intro d hd
      apply stay_twoPhase_concat hArun hAphase
      · intro r hr
        obtain ⟨port, phase, hrun, hphase⟩ := hcapturePhase r hr
        refine ⟨port, phase, hrun, ?_⟩
        rcases hphase with h | h
        · exact Or.inr (by simpa [alternate] using h)
        · exact Or.inl h
      · simpa [first] using hd
    have hwindow : ∀ d, d ≤ period → ∃ port phase,
        stepN w d (g, state) = some (port, phase) ∧
          (phase = state ∨ phase = alternate) := by
      intro d hd
      exact stay_twoPhase_concat hfirstEnd hfirstPhase hBphase d
        (by simpa [period] using hd)
    have hpositive : 0 < period := by
      dsimp [period, first]
      omega
    exact periodic_two_phase_prefix_tongues
      hpositive hperiod hwindow
  · obtain ⟨hrepairEnd, hrepairPhase⟩ := hrepair
    let period := (2 * A.runway.length + A.candy.length + 2) +
      (2 * B.runway.length + 2)
    have hperiod : stepN w period (g, state) = some (g, state) := by
      dsimp [period]
      rw [stepN_add, hArun]
      exact hrepairEnd
    have hwindow : ∀ d, d ≤ period → ∃ port phase,
        stepN w d (g, state) = some (port, phase) ∧
          (phase = state ∨ phase = alternate) := by
      intro d hd
      apply stay_twoPhase_concat hArun hAphase
      · intro r hr
        obtain ⟨port, phase, hrun, hphase⟩ := hrepairPhase r hr
        refine ⟨port, phase, hrun, ?_⟩
        rcases hphase with h | h
        · exact Or.inr (by simpa [alternate] using h)
        · exact Or.inl h
      · simpa [period] using hd
    have hpositive : 0 < period := by
      dsimp [period]
      omega
    exact periodic_two_phase_prefix_tongues
      hpositive hperiod hwindow

end

/-- The opposite orientation, with the stay traversal first, has the same two
absolute phases. -/
theorem manufactured_stay_then_flip_contact_all_time_two_phase
    {w : Wiring} {g e : Nat}
    (A : ManufacturedStayReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, [(A.mouth, A.arm)]] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [A.runway, [(A.mouth, A.arm)]],
      ∃ passage ∈ path,
        passageSwitch passage = B.actionSwitch) :
    ∀ d, ∃ port phase,
      stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = flipAt state B.actionSwitch) := by
  have hArun := (A.toSupported.run state hA).1
  change stepN w (2 * A.runway.length + 2) (g, state) =
      some (e, state) at hArun
  have hAphase : ∀ d, d ≤ 2 * A.runway.length + 2 →
      ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = flipAt state B.actionSwitch) := by
    intro d hd
    obtain ⟨port, hrun⟩ := A.travel_state_stepN state hA hd
    exact ⟨port, state, hrun, Or.inl rfl⟩
  have htail := manufactured_flip_then_stay_all_time_two_phase
    B A state hB hA hcontact
  intro d
  by_cases hpre : d ≤ 2 * A.runway.length + 2
  · exact hAphase d hpre
  · let r := d - (2 * A.runway.length + 2)
    have hdecomp : d = (2 * A.runway.length + 2) + r := by
      dsimp [r]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := htail r
    refine ⟨port, phase, ?_, hphase⟩
    rw [hdecomp, stepN_add, hArun]
    exact hrun

end GeneralN
