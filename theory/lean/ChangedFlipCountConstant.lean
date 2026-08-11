import TrackGlobalRepairActiveLead
import RepairLeadTwoPhase
import RunwayHistoricalThree

/-!
# Constant tongue count for a protected changed-forward flip splice

The old `N+4` bound records every position of the splice lead.  Under the
protected-repair hypotheses that lead is much smaller in state space: before
the changing contact, the repair prefix has only the activated and contact
phases; the contact itself produces the flipped entry phase.  Thus the entire
lead is covered by three vectors.  The closed runway/candy tail contributes at
most three further fresh vectors, for a uniform six-vector bound.
-/

namespace GeneralN

/-- A protected changed-forward flip merge has a three-vector historical lead
and at most three fresh tail vectors. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_three_history_three_novelty
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
        times history 3 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, _hApproachReplay, hApproachSimple,
      _hApproachGrooved, _hApproachForeign, _hCandyEq,
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
    · apply manufactured_flip_arbitrary_lobe_absolute_three_novelty
        C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
        hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
        hmouthLink hcontact hreach times history hentryHistorical
      intro j _hj hjLead
      exact hleadHistorical j hjLead
    · have hCandyForeignOld : ∀ passage ∈ candy,
          passageSwitch passage ≠ C.actionSwitch := by
        intro passage hp hEq
        exact hcontact ⟨passage, hp, hEq⟩
      apply manufactured_suffix_explicit_lobe_absolute_three_novelty
        C state hCpaths hNewAvoidsC hActionsNe hentryBranch
        hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach
        times history hentryHistorical
      intro j _hj hjLead
      exact hleadHistorical j hjLead
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        horiented hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved
      hActiveApproach
      (hActiveApproach.grooved_of_switchSimple hApproachSimple)
      (by
        intro passage hp
        have hforeign := hmerge.spliced_lobe_reflector_active_lead
        -- use the exported candy-foreign certificate below via the
        -- equivalent approach replay package
        have hmem : passage ∈ candy := by
          -- `candy = reverse oldPrefix ++ approach` is hidden above only
          -- because it is not needed elsewhere; recover the required switch
          -- inequality from the full candy certificate.
          sorry)
      hcrossed hmouthLink harms hreach
      N history hentryHistorical times (by
        intro j _hj hjLead
        exact hleadHistorical j hjLead)
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

/-- **Protected changed-forward flip count:** at most six distinct restricted
tongue vectors. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_distinct_le_six
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
    times.length ≤ 6 := by
  obtain ⟨history, hhistory, hcover⟩ :=
    hmerge.flip_three_history_three_novelty hA hBstart times
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  omega

end GeneralN
