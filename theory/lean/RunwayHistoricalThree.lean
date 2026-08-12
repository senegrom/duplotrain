import RunwaySpliceNovelty
import SharpStateLawAssembly

/-!
# Three fresh vectors for a historical runway entry

The closed runway-splice theorem supplies four explicit Gray corners.  Its
first corner is the state at which the ambient run enters the manufactured
runway/lobe pair.  When that entry has already been recorded in the
construction history, only the other three corners can be globally fresh.

Everything here is stated over raw `Wiring`/`stepN` dynamics.  In particular,
the result is a strengthening of the local changed-forward branch, not an
assumption about the still-open global repair construction.
-/

namespace GeneralN

/-- Shift an all-time four-phase law into an ambient run, removing its first
phase from the novelty budget when that phase is already historical. -/
theorem absolute_three_novelty_of_historical_first_four_phase
    {w : Wiring} {N K localPort : Nat}
    {start : Nat × Tongues} {u v₁ v₂ v₃ : Tongues}
    {times : List Nat} {history : List (List Bool)}
    (hreach : stepN w K start = some (localPort, u))
    (hlive : ∀ d, ∃ finish, stepN w d (localPort, u) = some finish)
    (hphase : ∀ d, tonguesAt w (localPort, u) d ∈ [u, v₁, v₂, v₃])
    (hu : VectorCount.restrict N u ∈ history)
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 3 := by
  refine ⟨[VectorCount.restrict N v₁,
      VectorCount.restrict N v₂,
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
    rcases hlocal with hu' | hv₁ | hv₂ | hv₃
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hshift, hu'] using hu
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, hshift, hv₁]
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, hshift, hv₂]
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, hshift, hv₃]

/-- Every finite prefix of a positive closed period is live. -/
private theorem runway_period_stepN_some
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

/-- Intersecting runway actions still need only three globally fresh vectors
once their common entering corner has already occurred. -/
theorem manufactured_flip_arbitrary_lobe_absolute_three_novelty
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
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 3 := by
  obtain ⟨period, hperiodPositive, hperiod, _hwindow⟩ :=
    manufactured_flip_arbitrary_lobe_four_phase_period C state hCpaths
      hNewAvoidsC hentryBranch hentrySwitch hgrooved htrace hcrossed
      hCandyForeign hLobe hmouthLink hcontact
  apply absolute_three_novelty_of_historical_first_four_phase
    (u := flipAt state (mouth / 3))
    (v₁ := flipAt (flipAt state (mouth / 3)) C.actionSwitch)
    (v₂ := state)
    (v₃ := flipAt state C.actionSwitch)
    hreach
  · intro d
    exact runway_period_stepN_some hperiodPositive hperiod
  · intro d
    exact manufactured_flip_arbitrary_lobe_all_time_four_phase_tongues
      C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
      hgrooved htrace hcrossed hCandyForeign hLobe hmouthLink
      hcontact d
  · exact hentryHistorical
  · exact hlead

/-- Disjoint runway actions likewise need only the three corners other than
the already-historical entry. -/
theorem manufactured_suffix_explicit_lobe_absolute_three_novelty
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
    (hlead : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N start j ∈ history) :
    NoveltyCoverOn w N start times history 3 := by
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
  apply absolute_three_novelty_of_historical_first_four_phase
    (u := flipAt state (mouth / 3))
    (v₁ := flipAt (flipAt state (mouth / 3)) C.actionSwitch)
    (v₂ := flipAt state C.actionSwitch)
    (v₃ := state)
    hreach
  · intro d
    exact runway_period_stepN_some hperiodPos hperiod
  · intro d
    exact manufactured_suffix_explicit_lobe_all_time_four_phase_tongues
      C state hCpaths hNewAvoidsC hActionsNe hentryBranch
      hentrySwitch hgrooved htrace hcrossed hCandyForeignNew
      hCandyForeignOld hLobe hmouthLink d
  · exact hentryHistorical
  · exact hlead

/-- **Historical-entry strengthening of the closed runway/candy theorem.**
The construction lead includes the state at which the splice orbit begins.
Consequently its four explicit Gray corners contain at most three globally
fresh restricted tongue vectors.  Candy contacts retain their sharper
one-vector bound. -/
theorem ManufacturedReflector.ChangedForwardMerge.runway_or_candy_absolute_three_novelty
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R))
    (N : Nat) (history : List (List Bool))
    (hleadHistorical : ∀ j, j ≤ A.toSupported.travel →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈ history)
    (times : List Nat) :
    NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).activatedState)
      times history 3 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, hApproach, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach,
      _hcomplete, hleadLen, _htailLen, happroachLe⟩ :=
    hmerge.spliced_lobe_reflector
  have hleadLe : leadSteps ≤ A.toSupported.travel := by
    rw [hleadLen]
    exact happroachLe
  have hentryHistorical : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history := by
    have hvector : restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState)
        leadSteps =
        VectorCount.restrict N (flipAt state (mouth / 3)) := by
      simp [restrictedTonguesAt, tonguesAt, hreach]
    rw [← hvector]
    exact hleadHistorical leadSteps hleadLe
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
    · apply manufactured_flip_arbitrary_lobe_absolute_three_novelty
        C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
        hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
        hmouthLink hcontact hreach times history hentryHistorical
      intro j hj hjLead
      apply hleadHistorical j
      rw [hleadLen] at hjLead
      omega
    · have hCandyForeignOld : ∀ passage ∈ candy,
          passageSwitch passage ≠ C.actionSwitch := by
        intro passage hp hEq
        exact hcontact ⟨passage, hp, hEq⟩
      apply manufactured_suffix_explicit_lobe_absolute_three_novelty
        C state hCpaths hNewAvoidsC hActionsNe hentryBranch
        hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach
        times history hentryHistorical
      intro j hj hjLead
      apply hleadHistorical j
      rw [hleadLen] at hjLead
      omega
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        horiented hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved hApproach hApproachGrooved
      hApproachForeign hcrossed hmouthLink harms hreach
      N history hentryHistorical times (by
        intro j _hj hjLead
        apply hleadHistorical j
        omega)
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

end GeneralN
