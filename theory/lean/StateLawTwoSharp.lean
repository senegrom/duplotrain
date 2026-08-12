import StateLawTwoCandidate
import ShortSuffixCount
import NoveltyChargeBound
import ArbitraryStartDirectLift

/-!
# Sharp coefficient-two state bound

This file tightens the raw general-N bound while keeping the sharper
N+6 GeneralN.StateLaw explicitly open.
-/

namespace GeneralN


private theorem runwaytwo_period_stepN_some
    {w : Wiring} {start : Nat × Tongues} {period d : Nat}
    (hpositive : 0 < period)
    (hperiod : stepN w period start = some start) :
    ∃ finish, stepN w d start = some finish := by
  have hfar : stepN w ((d + 1) * period) start = some start :=
    stepN_mul_period_pair_novelty hperiod (d + 1)
  have hbound : d ≤ (d + 1) * period := by
    have hone : 1 ≤ period := by omega
    have hmul := Nat.mul_le_mul_left (d + 1) hone
    simp only [Nat.mul_one] at hmul
    omega
  exact stepN_prefix_some hbound hfar

/-- Shift an all-time four-phase law into an ambient run when the first and
third listed phases are already historical. -/
theorem absolute_two_novelty_of_historical_first_third_four_phase
    {w : Wiring} {N K localPort : Nat}
    {start : Nat × Tongues} {u v₁ v₂ v₃ : Tongues}
    {times : List Nat} {history : List (List Bool)}
    (hreach : stepN w K start = some (localPort, u))
    (hlive : ∀ d, ∃ finish, stepN w d (localPort, u) = some finish)
    (hphase : ∀ d, tonguesAt w (localPort, u) d ∈ [u, v₁, v₂, v₃])
    (hu : VectorCount.restrict N u ∈ history)
    (hv₂ : VectorCount.restrict N v₂ ∈ history)
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 2 := by
  refine ⟨[VectorCount.restrict N v₁,
      VectorCount.restrict N v₃], by simp, ?_⟩
  intro j hj
  by_cases hjK : j < K
  · exact List.mem_append_left _ (hlead j hj hjK)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    have hshift := tonguesAt_add_of_reaches hreach (hlive d)
    rw [← hjEq] at hshift
    have hlocal := hphase d
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlocal
    rcases hlocal with hu' | hv₁' | hv₂' | hv₃'
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hshift, hu'] using hu
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, hshift, hv₁']
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hshift, hv₂'] using hv₂
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, hshift, hv₃']

/-- Shift an all-time four-phase law when the first and fourth phases are
already historical. -/
theorem absolute_two_novelty_of_historical_first_fourth_four_phase
    {w : Wiring} {N K localPort : Nat}
    {start : Nat × Tongues} {u v₁ v₂ v₃ : Tongues}
    {times : List Nat} {history : List (List Bool)}
    (hreach : stepN w K start = some (localPort, u))
    (hlive : ∀ d, ∃ finish, stepN w d (localPort, u) = some finish)
    (hphase : ∀ d, tonguesAt w (localPort, u) d ∈ [u, v₁, v₂, v₃])
    (hu : VectorCount.restrict N u ∈ history)
    (hv₃ : VectorCount.restrict N v₃ ∈ history)
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 2 := by
  refine ⟨[VectorCount.restrict N v₁,
      VectorCount.restrict N v₂], by simp, ?_⟩
  intro j hj
  by_cases hjK : j < K
  · exact List.mem_append_left _ (hlead j hj hjK)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    have hshift := tonguesAt_add_of_reaches hreach (hlive d)
    rw [← hjEq] at hshift
    have hlocal := hphase d
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlocal
    rcases hlocal with hu' | hv₁' | hv₂' | hv₃'
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hshift, hu'] using hu
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, hshift, hv₁']
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, hshift, hv₂']
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hshift, hv₃'] using hv₃

/-- Intersecting runway actions need only the two nonhistorical Gray corners
when both the entering alternate and base state are already recorded. -/
theorem manufactured_flip_arbitrary_lobe_absolute_two_novelty
    {w : Wiring} {outside mouth entry returnPort N : Nat}
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
    (hmouthLink : w.link mouth = some outside)
    (hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start =
      some (outside, flipAt state (mouth / 3)))
    (times : List Nat) (history : List (List Bool))
    (hentryHistorical : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history)
    (hstateHistorical : VectorCount.restrict N state ∈ history)
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 2 := by
  obtain ⟨period, hperiodPositive, hperiod, _hwindow⟩ :=
    manufactured_flip_arbitrary_lobe_four_phase_period C state hCpaths
      hNewAvoidsC hentryBranch hentrySwitch hgrooved htrace hcrossed
      hCandyForeign hLobe hmouthLink hcontact
  apply absolute_two_novelty_of_historical_first_third_four_phase
    (u := flipAt state (mouth / 3))
    (v₁ := flipAt (flipAt state (mouth / 3)) C.actionSwitch)
    (v₂ := state)
    (v₃ := flipAt state C.actionSwitch)
    hreach
  · intro d
    exact runwaytwo_period_stepN_some hperiodPositive hperiod
  · intro d
    exact manufactured_flip_arbitrary_lobe_all_time_four_phase_tongues
      C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
      hgrooved htrace hcrossed hCandyForeign hLobe hmouthLink
      hcontact d
  · exact hentryHistorical
  · exact hstateHistorical
  · exact hlead

/-- Disjoint runway actions likewise leave only the two middle Gray corners
fresh once the entering alternate and base state are historical. -/
theorem manufactured_suffix_explicit_lobe_absolute_two_novelty
    {w : Wiring} {outside mouth entry returnPort N : Nat}
    (C : ManufacturedFlipReflector w outside mouth)
    (state : Tongues)
    (hCpaths : PathGrooves C.toSupported.paths state)
    (hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
      C.toSupported.paths)
    (hActionsNe : mouth / 3 ≠ C.actionSwitch)
    {candy : List Passage}
    (hentryBranch : entry % 3 ≠ 0)
    (hentrySwitch : entry / 3 = mouth / 3)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandyForeignNew : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hCandyForeignOld : ∀ passage ∈ candy,
      passageSwitch passage ≠ C.actionSwitch)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hmouthLink : w.link mouth = some outside)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start =
      some (outside, flipAt state (mouth / 3)))
    (times : List Nat) (history : List (List Bool))
    (hentryHistorical : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history)
    (hstateHistorical : VectorCount.restrict N state ∈ history)
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 2 := by
  let L : SupportedReflector w mouth outside := {
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
      · intro path hp
        simp only [List.mem_singleton] at hp
        subst path
        exact hnext
  }
  have hOldAvoidsL : C.toSupported.action.Avoids L.paths := by
    change (LocalAction.flip C.actionSwitch).Avoids [candy]
    intro path hp passage hpassage
    simp only [List.mem_singleton] at hp
    subst path
    exact hCandyForeignOld passage hpassage
  have hCNew : PathGrooves C.toSupported.paths
      (flipAt state (mouth / 3)) :=
    hCpaths.after_avoiding_action hNewAvoidsC
  have hCandy : PassagesGrooved state candy := by
    intro passage hp
    exact hgrooved passage (List.mem_cons_of_mem _ hp)
  have hCandyNew : PassagesGrooved
      (flipAt state (mouth / 3)) candy :=
    grooved_after_flip_other hCandy hCandyForeignNew
  have hLNew : PathGrooves L.paths
      (flipAt state (mouth / 3)) := by
    intro path hp
    simp only [L, List.mem_singleton] at hp
    subst path
    exact hCandyNew
  let period := 2 * (C.toSupported.travel + L.travel)
  have hperiodPos : 0 < period := by
    have hCpos := (ManufacturedReflector.flip C).travel_pos
    dsimp [period, L]
    omega
  have hperiod : stepN w period
      (outside, flipAt state (mouth / 3)) =
        some (outside, flipAt state (mouth / 3)) := by
    dsimp [period]
    exact C.toSupported.paired_period L hOldAvoidsL hNewAvoidsC
      (flipAt state (mouth / 3)) hCNew hLNew
  apply absolute_two_novelty_of_historical_first_fourth_four_phase
    (u := flipAt state (mouth / 3))
    (v₁ := flipAt (flipAt state (mouth / 3)) C.actionSwitch)
    (v₂ := flipAt state C.actionSwitch)
    (v₃ := state)
    hreach
  · intro d
    exact runwaytwo_period_stepN_some hperiodPos hperiod
  · intro d
    exact manufactured_suffix_explicit_lobe_all_time_four_phase_tongues
      C state hCpaths hNewAvoidsC hActionsNe hentryBranch
      hentrySwitch hgrooved htrace hcrossed hCandyForeignNew
      hCandyForeignOld hLobe hmouthLink d
  · exact hentryHistorical
  · exact hstateHistorical
  · exact hlead



/-- A protected changed-forward flip merge has a three-vector historical lead
and at most two fresh tail vectors. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_three_history_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hA : PathGrooves A.toSupported.paths
      (ManufacturedReflector.flip R).baseState)
    (hBstart : PathGrooves (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hmerge : A.ChangedForwardMerge (.flip R))
    (times : List Nat) :
    ∃ history : List (List Bool),
      history.length ≤ 3 ∧
      NoveltyCoverOn w N
        (g, (ManufacturedReflector.flip R).activatedState)
        times history 2 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, hApproachReplay, hApproachSimple,
      hApproachGrooved, hApproachForeign, _hCandyEq,
      hentryBranch, _hmouthStem, hmouthLink, harms,
      hfullGrooved, hfullTrace, hcrossed, hRpaths, _hCandy,
      hCandyForeignNew, hLobe, hreach, _hcomplete,
      hleadLen, _htailLen, _happroachLe,
      hActiveApproach, hApproachRoute⟩ :=
    hmerge.spliced_lobe_reflector_active_lead
  let initial := (ManufacturedReflector.flip R).activatedState
  let alternate := flipAt state (mouth / 3)
  let history := [VectorCount.restrict N initial,
    VectorCount.restrict N state,
    VectorCount.restrict N alternate]
  have hphase := A.repair_prefix_two_phase (.flip R) hA hBstart
    hActiveApproach hApproachSimple hApproachRoute hRpaths
  have hleadHistorical : ∀ j, j < leadSteps →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈ history := by
    intro j hj
    have hjApproach : j ≤ approach.length := by
      rw [hleadLen] at hj
      omega
    obtain ⟨port, phase, hrun, hphaseEq⟩ := hphase j hjApproach
    have hvec : restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j =
        VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hrun]
    rw [hvec]
    rcases hphaseEq with hinit | hstate
    · have hinit' : phase = initial := by simpa [initial] using hinit
      simp [history, hinit']
    · simp [history, hstate]
  have hentryHistorical : VectorCount.restrict N alternate ∈ history := by
    simp [history]
  have hstateHistorical : VectorCount.restrict N state ∈ history := by
    simp [history]
  refine ⟨history, by simp [history], ?_⟩
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨C, _hCAction, hEntryOldNe, hCpaths,
        hNewAvoidsCRaw, _htravel⟩ :=
      R.suffix_after_runway_passage_with_travel state hRpaths
        hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch state entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe : mouth / 3 ≠ C.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
        C.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsCRaw
    by_cases hcontact : ∃ passage ∈ candy,
        passageSwitch passage = C.actionSwitch
    · apply manufactured_flip_arbitrary_lobe_absolute_two_novelty
        C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
        hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
        hmouthLink hcontact hreach times history hentryHistorical
        hstateHistorical
      intro j _hj hjLead
      exact hleadHistorical j hjLead
    · have hCandyForeignOld : ∀ passage ∈ candy,
          passageSwitch passage ≠ C.actionSwitch := by
        intro passage hp hEq
        exact hcontact ⟨passage, hp, hEq⟩
      apply manufactured_suffix_explicit_lobe_absolute_two_novelty
        C state hCpaths hNewAvoidsC hActionsNe hentryBranch
        hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach
        times history hentryHistorical hstateHistorical
      intro j _hj hjLead
      exact hleadHistorical j hjLead
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        horiented hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved hApproachReplay hApproachGrooved
      hApproachForeign hcrossed hmouthLink harms hreach
      N history hentryHistorical times (by
        intro j _hj hjLead
        exact hleadHistorical j hjLead)
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

/-- **Protected changed-forward flip count:** at most five distinct restricted
tongue vectors. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_distinct_le_five
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hA : PathGrooves A.toSupported.paths
      (ManufacturedReflector.flip R).baseState)
    (hBstart : PathGrooves (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (hmerge : A.ChangedForwardMerge (.flip R))
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).activatedState))).Nodup) :
    times.length ≤ 5 := by
  obtain ⟨history, hhistory, hcover⟩ :=
    hmerge.flip_three_history_two_novelty hA hBstart times
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  omega



/-- State-changing protected contact, retaining a constant backward-contact
count instead of the old `N+2` route-window count. -/
theorem ManufacturedReflector.protected_changed_contact_three_or_forward
    {w : Wiring} {N g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {u v : Tongues}
    {approach suffix : List Passage}
    {path : List Passage} {old : Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState)
      approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3)) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ 3) ∨
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
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple
      exact (List.nodup_append.mp hrouteSimple).1
    have happroachForeign : ∀ passage ∈ approach,
        passageSwitch passage ≠ p / 3 := by
      unfold SwitchSimple at hrouteSimple
      simp only [List.map_append, List.map_cons] at hrouteSimple
      have hparts := List.nodup_append.mp hrouteSimple
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (p / 3) (by simp [passageSwitch])
      exact hne hEq
    have happroachV : PhysicalTrace w
        (g, flipAt B.activatedState (p / 3)) approach (p, v) := by
      rw [hflip]
      exact happroach.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have happroachGroovedU : PassagesGrooved u approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplayU :
        PhysicalTrace w (g, u) approach (p, u) :=
      happroach.replay_grooved u happroachGroovedU
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes, (stepN w k (p, u)).isSome) →
        (tailTimes.map (restrictedTonguesAt w N (p, u))).Nodup →
        tailTimes.length ≤ 2 := by
      intro tailTimes _ htailNodup
      exact backward_contact_tail_distinct_le_two
        hrecorded hrecordedGroovedV B.entryEdge
        (by simpa [hbackward] using harrive)
        happroachReplayU happroachGroovedV tailTimes htailNodup
    exact Or.inl (fun times hlive hnd =>
      two_phase_prefix_then_direct_tail_distinct_le_succ
        happroach.sound hphase htail (by omega) times hlive hnd)
  · obtain ⟨hforwardExit, repaired, hrepair, hgroove⟩ := hforward
    exact Or.inr ⟨oriented, repaired, horiented,
      horientedGroove, horientedSwitch,
      hforwardExit, hrepair, hgroove⟩

/-- No-change protected contact, retaining the constant backward-contact
count. -/
theorem ManufacturedReflector.protected_facing_contact_three_or_forward
    {w : Wiring} {N g e p marker fresh : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {contact : Tongues}
    {approach suffix path : List Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, marker) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState)
      approach (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact)) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ 3) ∨
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
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple
      exact (List.nodup_append.mp hrouteSimple).1
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplay :
        PhysicalTrace w (g, contact) approach (p, contact) :=
      happroach.replay_grooved contact happroachGrooved
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes, (stepN w k (p, contact)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (p, contact))).Nodup →
        tailTimes.length ≤ 2 := by
      intro tailTimes _ htailNodup
      exact backward_contact_tail_distinct_le_two
        hrecorded hrecordedGrooved B.entryEdge harrive
        happroachReplay happroachGrooved tailTimes htailNodup
    exact Or.inl (fun times hlive hnd =>
      two_phase_prefix_then_direct_tail_distinct_le_succ
        happroach.sound hphase htail (by omega) times hlive hnd)
  · right
    simpa [hreverse] using horiented

/-- Protected-repair classification in which every early exit already carries
its constant three-vector count. -/
theorem manufactured_pair_protected_repair_constant_outcomes
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      times.length ≤ 3) ∨
      A.FacingForwardMerge B ∨
      A.ChangedForwardMerge B ∨
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
      intro times hlive hnd
      exact ManufacturedReflector.return_change_facing_distinct_le_three
        A B hA hB hsplit hprefix hBcontact hp
        hreturn.1 hreturn.2 times hlive hnd
    · obtain ⟨oldApproach, fresh, oldSuffix, oldU, oldV, path,
          _holdSplit, _holdSwitch, _holdTrace, _holdArrive,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases A.protected_facing_contact_three_or_forward B hA hB
          hsplit hprefix hBcontact hpath hold harriveFresh with
        hcount | hforward
      · exact Or.inl hcount
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
      rcases A.protected_changed_contact_three_or_forward B hA hB
          hsplit hprefix hBu harrive hpath hold hswitch hchange with
        hcount | hforward
      · exact Or.inl hcount
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

theorem manufactured_pair_protected_repair_distinct_le_five
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 5 := by
  rcases manufactured_pair_protected_repair_constant_outcomes
      A B hA hB with hcount | hrest
  · have hc := hcount times hlive hnd
    omega
  · rcases hrest with hfacing | hrest
    · have hc := hfacing.distinct_le_three hA hB times hlive hnd
      omega
    · rcases hrest with hchanged | hcomplete
      · cases B with
        | stay R =>
            have hc := hchanged.stay_distinct_le_three
              hA hB times hlive hnd
            omega
        | flip R =>
            exact hchanged.flip_distinct_le_five hA hB times hnd
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact A.completed_protected_route_with_pair_distinct_le_five
          B hA hB hrepair hAfinal hBfinal times hlive hnd

private theorem ketc_nodup_of_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

private theorem ketc_live_distinct_le_of_stepN_none
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    {times : List Nat}
    (hnone : stepN w L start = none)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ L := by
  have htimesNodup : times.Nodup :=
    ketc_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  apply nodup_nat_lt_length htimesNodup
  intro k hk
  by_cases hlt : k < L
  · exact hlt
  · have hkEq : k = L + (k - L) := by omega
    have hnoneK : stepN w k start = none := by
      rw [hkEq, stepN_add, hnone]
      simp
    have hkLive := hlive k hk
    rw [hnoneK] at hkLive
    simp at hkLive

/-- Boundary-aware terminating branch.  The manufactured journey endpoint is
already present in its sharp history, so a suffix dead after N+1 steps costs
2*N+2 rather than 2*N+3. -/
private theorem one_manufacturing_journey_then_dead_suffix_distinct_le_two_mul_add_two
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (A : ManufacturedReflector w start.1 e)
    (stateA : Tongues)
    (hbaseA : A.baseState = start.2)
    (hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hgroovesA : PathGrooves A.toSupported.paths stateA)
    (hdead : stepN w (N + 1) (e, stateA) = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 2 := by
  let travel := A.exploration.length + A.runway.length + 1
  let history := A.sharpConstructionHistory N
  have hreach : stepN w travel start = some (e, stateA) := by
    simpa [travel] using hreachA
  have hgroovesActivated :
      PathGrooves A.toSupported.paths A.activatedState := by
    rw [← hactivatedA]
    exact hgroovesA
  have hprefixCover : ∀ d, d ≤ travel →
      restrictedTonguesAt w N start d ∈ history := by
    intro d hd
    have hm := A.manufacturing_journey_mem_sharpHistory
      (N := N) hgroovesActivated (j := d)
        (by simpa [travel] using hd)
    simpa [history, hbaseA] using hm
  have hboundary :
      VectorCount.restrict N stateA ∈ history := by
    dsimp [history]
    simp [ManufacturedReflector.sharpConstructionHistory, hactivatedA]
  have hhistory : history.length ≤ N + 2 := by
    dsimp [history]
    exact A.sharpConstructionHistory_length hN
  exact short_suffix_after_boundary_history_distinct_le_two_mul_add_two
    hreach history hprefixCover hboundary hhistory hdead
      times hlive hnd

/-- General all-run known-edge assembly from a direct protected-repair cap. -/
theorem known_edge_all_run_distinct_le_of_protected_cap
    {w : Wiring} {N tailCap : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hcap : 2 ≤ tailCap)
    (hprotected : ∀ {g e : Nat}
      (A : ManufacturedReflector w g e)
      (B : ManufacturedReflector w e g),
      PathGrooves A.toSupported.paths B.baseState →
      PathGrooves B.toSupported.paths B.activatedState →
      ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (g, B.activatedState)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N
            (g, B.activatedState))).Nodup →
        tailTimes.length ≤ tailCap)
    {e : Nat} {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + tailCap + 2 := by
  cases hfirst : stepN w (N + 1) start with
  | none =>
      have hc := ketc_live_distinct_le_of_stepN_none
        (N := N) hfirst hlive hnd
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycleA | hreflectorA
      · have hc := hcycleA times hnd
        omega
      · obtain ⟨A, stateA, _hfirstLe, hgroovesA,
          hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
        have hentryB : w.link start.1 = some e :=
          w.symm _ _ A.entryEdge
        cases hsecond : stepN w (N + 1) (e, stateA) with
        | none =>
            have hc :=
              one_manufacturing_journey_then_dead_suffix_distinct_le_two_mul_add_two
              hN A stateA hbaseA hactivatedA hreachA hgroovesA
                hsecond times hlive hnd
            omega
        | some secondFinish =>
            rcases first_activated_count_outcome_sharp
                (w := w) (N := N) (e := start.1)
                hN hsecond hentryB with hcycleB | hreflectorB
            · have htail : ∀ (tailTimes : List Nat),
                  (∀ k ∈ tailTimes,
                    (stepN w k (e, stateA)).isSome) →
                  (tailTimes.map
                    (restrictedTonguesAt w N (e, stateA))).Nodup →
                  tailTimes.length ≤ N + 2 := by
                intro tailTimes _htailLive htailNodup
                exact hcycleB tailTimes htailNodup
              have hc := one_manufacturing_journey_then_direct_tail_distinct_le
                (tailCap := N + 2)
                hN A stateA hbaseA hactivatedA hreachA hgroovesA
                htail times hlive hnd
              omega
            · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                  hbaseB, hactivatedB, hreachB,
                  _hpreservesB⟩ := hreflectorB
              have hAatBase :
                  PathGrooves A.toSupported.paths B.baseState := by
                simpa [hbaseB] using hgroovesA
              have hBatActivated :
                  PathGrooves B.toSupported.paths B.activatedState := by
                simpa [← hactivatedB] using hgroovesB
              have htail : ∀ (tailTimes : List Nat),
                  (∀ k ∈ tailTimes,
                    (stepN w k (start.1, stateB)).isSome) →
                  (tailTimes.map
                    (restrictedTonguesAt w N
                      (start.1, stateB))).Nodup →
                  tailTimes.length ≤ tailCap := by
                intro tailTimes htailLive htailNodup
                have htailLive' : ∀ k ∈ tailTimes,
                    (stepN w k
                      (start.1, B.activatedState)).isSome := by
                  simpa [← hactivatedB] using htailLive
                have htailNodup' :
                    (tailTimes.map
                      (restrictedTonguesAt w N
                        (start.1, B.activatedState))).Nodup := by
                  simpa [← hactivatedB] using htailNodup
                exact hprotected A B hAatBase hBatActivated
                  tailTimes htailLive' htailNodup'
              have hc :=
                two_manufacturing_journeys_then_boundary_tail_distinct_le
                  hN A B stateA stateB hbaseA hactivatedA
                  hreachA hgroovesA hbaseB hactivatedB hreachB
                  hgroovesB htail (by omega) times hlive hnd
              omega

/-- Five protected vectors give the sharp known-edge coefficient-two
constant `2*N+7`. -/
theorem known_edge_all_run_distinct_le_two_add_seven
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 7 := by
  have hc := known_edge_all_run_distinct_le_of_protected_cap
    hN (tailCap := 5) (by omega)
    (fun A B hA hB tailTimes htailLive htailNodup =>
      manufactured_pair_protected_repair_distinct_le_five
        A B hA hB tailTimes htailLive htailNodup)
    hentry times hlive hnd
  omega


/-- Unconditional raw general-N 2*N+8 state bound.

The known-edge run costs 2*N+7; an arbitrary start contributes at most
its time-zero vector. This does not prove the open N+6 state law. -/
theorem state_law_linear_two_add_eight_sharp
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 8 := by
  apply arbitrary_start_distinct_le_succ_of_all_known_edge
    (cap := 2 * N + 7)
  · intro e localStart hentry localTimes hlocalLive hlocalNodup
    exact known_edge_all_run_distinct_le_two_add_seven
      hN hentry localTimes hlocalLive hlocalNodup
  · exact hlive
  · exact hnd

end GeneralN
