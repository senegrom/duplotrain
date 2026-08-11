import StateLawTwoSharp
import SingleCoordinateFlip
import RunwayHistoricalOne

/-!
# Four-vector protected changed-forward flip count

The protected approach changes only the old reflector's action coordinate.
Consequently its initial phase is either the contact state itself or the old
one-switch Gray corner.  In the first case the lead has two phases and the
runway/lobe tail has at most two fresh corners.  In the second case the lead
has three phases, including the old-action corner, and only the double-flipped
corner remains fresh.  Candy contacts retain their one-vector tail bound.
-/

namespace GeneralN

/-- **Protected changed-forward flip count:** at most four distinct restricted
tongue vectors. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_distinct_le_four
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
    times.length ≤ 4 := by
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
  have hphase := A.repair_prefix_two_phase (.flip R) hA hBstart
    hActiveApproach hApproachSimple hApproachRoute hRpaths
  have hchangesRaw :=
    A.repair_prefix_changes_only_protected_return (.flip R)
      hA hBstart hActiveApproach hApproachSimple
      hApproachRoute hRpaths
  have hchanges : ∀ j, state j ≠ initial j → j = R.actionSwitch := by
    intro j hj
    have h := hchangesRaw j (by simpa [initial] using hj)
    change j = R.secondArm / 3 at h
    exact h.trans R.secondArm_switch
  have hrelation :
      initial = state ∨ initial = flipAt state R.actionSwitch :=
    tongues_eq_or_eq_flipAt_of_changes_only
      (u := initial) (v := state) (k := R.actionSwitch) hchanges
  have hleadHistoricalOf : ∀ history : List (List Bool),
      VectorCount.restrict N initial ∈ history →
      VectorCount.restrict N state ∈ history →
      ∀ j, j < leadSteps →
        restrictedTonguesAt w N
          (g, (ManufacturedReflector.flip R).activatedState) j ∈ history := by
    intro history hinitialHistorical hstateHistorical j hj
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
      simpa [hinit'] using hinitialHistorical
    · simpa [hstate] using hstateHistorical
  rcases hrelation with hsame | hold
  · let history := [VectorCount.restrict N state,
        VectorCount.restrict N alternate]
    have hinitialHistorical :
        VectorCount.restrict N initial ∈ history := by
      simp [history, hsame]
    have hstateHistorical :
        VectorCount.restrict N state ∈ history := by
      simp [history]
    have hentryHistorical :
        VectorCount.restrict N alternate ∈ history := by
      simp [history]
    have hleadHistorical : ∀ j, j < leadSteps →
        restrictedTonguesAt w N
          (g, (ManufacturedReflector.flip R).activatedState) j ∈ history :=
      hleadHistoricalOf history hinitialHistorical hstateHistorical
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
      · have hcover :=
          manufactured_flip_arbitrary_lobe_absolute_two_novelty
            C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
            hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
            hmouthLink hcontact hreach times history hentryHistorical
            hstateHistorical (by
              intro j _hj hjLead
              exact hleadHistorical j hjLead)
        have hcount := noveltyCoverOn_distinct_count hcover hnd
        have hhistory : history.length = 2 := by simp [history]
        omega
      · have hCandyForeignOld : ∀ passage ∈ candy,
            passageSwitch passage ≠ C.actionSwitch := by
          intro passage hp hEq
          exact hcontact ⟨passage, hp, hEq⟩
        have hcover :=
          manufactured_suffix_explicit_lobe_absolute_two_novelty
            C state hCpaths hNewAvoidsC hActionsNe hentryBranch
            hentrySwitch hfullGrooved hfullTrace hcrossed
            hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach
            times history hentryHistorical hstateHistorical (by
              intro j _hj hjLead
              exact hleadHistorical j hjLead)
        have hcount := noveltyCoverOn_distinct_count hcover hnd
        have hhistory : history.length = 2 := by simp [history]
        omega
    · obtain ⟨old, hOldMem, horientation⟩ :=
        R.nonrunway_oriented_branch_entry_is_candy state
          horiented hrunway hentryBranch
      have hentryGrooved : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hone := manufactured_flip_candy_splice_absolute_one_novelty
        R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
        hOldMem horientation hentryGrooved hApproachReplay hApproachGrooved
        hApproachForeign hcrossed hmouthLink harms hreach
        N history hentryHistorical times (by
          intro j _hj hjLead
          exact hleadHistorical j hjLead)
      obtain ⟨fresh, hfresh, hmem⟩ := hone
      have hcover : NoveltyCoverOn w N
          (g, (ManufacturedReflector.flip R).activatedState)
          times history 1 := ⟨fresh, hfresh, hmem⟩
      have hcount := noveltyCoverOn_distinct_count hcover hnd
      have hhistory : history.length = 2 := by simp [history]
      omega
  · let history := [VectorCount.restrict N initial,
        VectorCount.restrict N state,
        VectorCount.restrict N alternate]
    have hinitialHistorical :
        VectorCount.restrict N initial ∈ history := by
      simp [history]
    have hstateHistorical :
        VectorCount.restrict N state ∈ history := by
      simp [history]
    have hentryHistorical :
        VectorCount.restrict N alternate ∈ history := by
      simp [history]
    have hleadHistorical : ∀ j, j < leadSteps →
        restrictedTonguesAt w N
          (g, (ManufacturedReflector.flip R).activatedState) j ∈ history :=
      hleadHistoricalOf history hinitialHistorical hstateHistorical
    by_cases hrunway : (entry, mouth) ∈ R.runway
    · obtain ⟨before, after, hrunwaySplit⟩ :=
        List.append_of_mem hrunway
      obtain ⟨C, hCAction, hEntryOldNe, hCpaths,
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
      have holdHistorical : VectorCount.restrict N
          (flipAt state C.actionSwitch) ∈ history := by
        rw [hCAction, ← hold]
        simp [history]
      by_cases hcontact : ∃ passage ∈ candy,
          passageSwitch passage = C.actionSwitch
      · have hcover :=
          manufactured_flip_arbitrary_lobe_absolute_one_novelty
            C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
            hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
            hmouthLink hcontact hreach times history hentryHistorical
            hstateHistorical holdHistorical (by
              intro j _hj hjLead
              exact hleadHistorical j hjLead)
        have hcount := noveltyCoverOn_distinct_count hcover hnd
        have hhistory : history.length = 3 := by simp [history]
        omega
      · have hCandyForeignOld : ∀ passage ∈ candy,
            passageSwitch passage ≠ C.actionSwitch := by
          intro passage hp hEq
          exact hcontact ⟨passage, hp, hEq⟩
        have hcover :=
          manufactured_suffix_explicit_lobe_absolute_one_novelty
            C state hCpaths hNewAvoidsC hActionsNe hentryBranch
            hentrySwitch hfullGrooved hfullTrace hcrossed
            hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach
            times history hentryHistorical hstateHistorical
            holdHistorical (by
              intro j _hj hjLead
              exact hleadHistorical j hjLead)
        have hcount := noveltyCoverOn_distinct_count hcover hnd
        have hhistory : history.length = 3 := by simp [history]
        omega
    · obtain ⟨old, hOldMem, horientation⟩ :=
        R.nonrunway_oriented_branch_entry_is_candy state
          horiented hrunway hentryBranch
      have hentryGrooved : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hone := manufactured_flip_candy_splice_absolute_one_novelty
        R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
        hOldMem horientation hentryGrooved hApproachReplay hApproachGrooved
        hApproachForeign hcrossed hmouthLink harms hreach
        N history hentryHistorical times (by
          intro j _hj hjLead
          exact hleadHistorical j hjLead)
      obtain ⟨fresh, hfresh, hmem⟩ := hone
      have hcover : NoveltyCoverOn w N
          (g, (ManufacturedReflector.flip R).activatedState)
          times history 1 := ⟨fresh, hfresh, hmem⟩
      have hcount := noveltyCoverOn_distinct_count hcover hnd
      have hhistory : history.length = 3 := by simp [history]
      omega

end GeneralN
