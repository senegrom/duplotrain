import RunwayHistoricalThree
import TrackGlobalRepairSimple

/-!
# Actual-lead count for a changed-forward flip splice

The existing three-novelty theorem asks callers to mark the whole old
reflector traversal as historical.  The splice construction exposes a much
shorter lead: a switch-simple approach followed by the changing contact.
The mouth switch is absent from the approach, so the lead has at most `N`
steps.  Charging precisely that lead and then the three Gray/candy phases gives
`N+4` distinct vectors.
-/

namespace GeneralN

/-- The actual lead of a changed-forward splice contains at most `N` steps. -/
theorem ManufacturedReflector.ChangedForwardMerge.actual_lead_le_switches
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B) :
    ∃ lead : Nat,
      lead ≤ N ∧
      ∃ finish, stepN w lead (g, B.activatedState) = some finish := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, tailSteps, horiented,
      hrouteSplit, hOldTail, hApproach, hApproachSimple,
      hApproachGrooved, hApproachForeign, hCandyEq, hentryBranch,
      hmouthStem, hmouthLink, harms, hfullGrooved, hfullTrace,
      hcrossed, hBpaths, hCandy, hCandyForeign, hLobe, hreach,
      hcomplete, hleadLen, htailLen, happroachLe⟩ :=
    hmerge.spliced_lobe_reflector_simple
  have hmouthLt : mouth / 3 < N := by
    have hports := hN mouth outside hmouthLink
    omega
  have hmouthNotMem : mouth / 3 ∉
      approach.map passageSwitch := by
    intro hm
    obtain ⟨passage, hp, hEq⟩ := List.mem_map.mp hm
    exact hApproachForeign passage hp hEq
  have hkeysNodup :
      (mouth / 3 :: approach.map passageSwitch).Nodup :=
    List.nodup_cons.mpr ⟨hmouthNotMem, hApproachSimple⟩
  have hkeysLt : ∀ s ∈ mouth / 3 :: approach.map passageSwitch,
      s < N := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hmouthLt
    · exact hApproach.passage_switches_lt hN s hs
  have happroachOneLe : approach.length + 1 ≤ N := by
    have hlen := nodup_nat_lt_length hkeysNodup hkeysLt
    simpa using hlen
  refine ⟨leadSteps, ?_, outside, flipAt state (mouth / 3), hreach⟩
  rw [hleadLen]
  exact happroachOneLe

/-- Pointwise novelty cover using only the actual splice lead. -/
theorem ManufacturedReflector.ChangedForwardMerge.actual_lead_three_novelty
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R))
    (times : List Nat) :
    ∃ history : List (List Bool),
      history.length ≤ N + 1 ∧
      NoveltyCoverOn w N
        (g, (ManufacturedReflector.flip R).activatedState)
        times history 3 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, hApproach, hApproachSimple,
      hApproachGrooved, hApproachForeign, _hCandyEq,
      hentryBranch, _hmouthStem, hmouthLink, harms,
      hfullGrooved, hfullTrace, hcrossed, hRpaths, _hCandy,
      hCandyForeignNew, hLobe, hreach, _hcomplete,
      hleadLen, _htailLen, _happroachLe⟩ :=
    hmerge.spliced_lobe_reflector_simple
  have hmouthLt : mouth / 3 < N := by
    have hports := hN mouth outside hmouthLink
    omega
  have hmouthNotMem : mouth / 3 ∉
      approach.map passageSwitch := by
    intro hm
    obtain ⟨passage, hp, hEq⟩ := List.mem_map.mp hm
    exact hApproachForeign passage hp hEq
  have hkeysNodup :
      (mouth / 3 :: approach.map passageSwitch).Nodup :=
    List.nodup_cons.mpr ⟨hmouthNotMem, hApproachSimple⟩
  have hkeysLt : ∀ s ∈ mouth / 3 :: approach.map passageSwitch,
      s < N := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hmouthLt
    · exact hApproach.passage_switches_lt hN s hs
  have hleadLe : leadSteps ≤ N := by
    rw [hleadLen]
    have hlen := nodup_nat_lt_length hkeysNodup hkeysLt
    simpa using hlen
  let history := (List.range (leadSteps + 1)).map
    (restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).activatedState))
  have hhistoryLen : history.length ≤ N + 1 := by
    simp [history]
    omega
  have hleadHistorical : ∀ j, j ≤ leadSteps →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈ history := by
    intro j hj
    exact List.mem_map.mpr
      ⟨j, List.mem_range.mpr (by omega), rfl⟩
  have hentryHistorical : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history := by
    have hvector : restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState)
        leadSteps =
        VectorCount.restrict N (flipAt state (mouth / 3)) := by
      simp [restrictedTonguesAt, tonguesAt, hreach]
    rw [← hvector]
    exact hleadHistorical leadSteps (Nat.le_refl _)
  refine ⟨history, hhistoryLen, ?_⟩
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
      exact hleadHistorical j (Nat.le_of_lt hjLead)
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
      exact hleadHistorical j (Nat.le_of_lt hjLead)
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
        exact hleadHistorical j (Nat.le_of_lt hjLead))
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

/-- **Changed-forward flip count:** at most `N+4` distinct vectors. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_distinct_le_n_add_four_actual
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R))
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).activatedState))).Nodup) :
    times.length ≤ N + 4 := by
  obtain ⟨history, hhistory, hcover⟩ :=
    hmerge.actual_lead_three_novelty hN times
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  omega

end GeneralN
