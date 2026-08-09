import TrackGlobalRepairSimple
import TrackQuantitativeRepairEighteen

/-!
# Seventeen-N protected repair

The fresh approach in a changed-forward splice is a proper prefix of a
switch-simple route.  Together with the contacted switch it therefore uses at
most `N` switches.  This sharpens both residual geometries:

* runway splice: at most `13*N`;
* candy splice: at most `9*N`.

The stay-reflector residual is already `16*N`.  Hence every changed-forward
merge is within `16*N`; the complete-repair branch (`N` repair route plus the
`16*N` reflector-pair lasso) is the sole bottleneck at `17*N`.
-/

namespace GeneralN

/-- Exact runway splice accounting with a proper switch-simple approach. -/
private theorem manufactured_flip_runway_splice_with_lead_within_thirteen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hRpaths : PathGrooves R.toSupported.paths state)
    {entry mouth returnPort outside : Nat}
    {before after approach candy : List Passage}
    {start : Nat × Tongues} {leadSteps : Nat}
    (hrunwaySplit : R.runway = before ++ (entry, mouth) :: after)
    (hmouthLink : w.link mouth = some outside)
    (hentryBranch : entry % 3 ≠ 0)
    (hgrooved : PassagesGrooved state ((mouth, entry) :: candy))
    (htrace : PhysicalTrace w (mouth, state)
      ((mouth, entry) :: candy) (returnPort, state))
    (hcrossed : arrive state returnPort =
      (mouth, flipAt state (mouth / 3)))
    (hCandy : PassagesGrooved state candy)
    (hCandyForeign : ∀ passage ∈ candy,
      passageSwitch passage ≠ mouth / 3)
    (hLobe : IsReflector w mouth outside (candy.length + 2)
      (fun current => PassagesGrooved current candy)
      (fun current => flipAt current (mouth / 3)))
    (hcandyLen : candy.length = before.length + approach.length)
    (hreach : stepN w leadSteps start =
      some (outside, flipAt state (mouth / 3)))
    (hleadLen : leadSteps = approach.length + 1)
    (happroachOneLe : approach.length + 1 ≤ N) :
    EventuallyPeriodicWithin w start (13 * N) := by
  obtain ⟨C, _hCAction, _hActionsNe, hCpaths, hNewAvoidsC,
      htravelExact⟩ :=
    R.suffix_after_runway_passage_with_travel state hRpaths
      hrunwaySplit hmouthLink
  have hentrySwitch : entry / 3 = mouth / 3 := by
    have hheadGroove : arrive state entry = (mouth, state) :=
      hgrooved (mouth, entry) List.mem_cons_self
    have hswitch := arrive_exit_switch state entry
    rw [hheadGroove] at hswitch
    exact hswitch.symm
  have hNewAvoidsC' :
      (LocalAction.flip (mouth / 3)).Avoids
        C.toSupported.paths := by
    simpa [hentrySwitch] using hNewAvoidsC
  have hRtravel : R.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip R).travel_le_two_mul_switches hN
  have hNpos : 0 < N := by
    have hports := hN mouth outside hmouthLink
    omega
  by_cases hcontact : ∃ passage ∈ candy,
      passageSwitch passage = C.actionSwitch
  · have hlocal := manufactured_flip_arbitrary_lobe_within C state hCpaths
      hNewAvoidsC' hentryBranch hentrySwitch hgrooved htrace
      hcrossed hCandyForeign hLobe hcontact
    have hbudget :
        leadSteps +
            4 * (C.toSupported.travel + (candy.length + 2)) ≤
          13 * N := by
      rw [hleadLen, hcandyLen]
      omega
    exact (hlocal.prepend hreach).weaken hbudget
  · let L : SupportedReflector w mouth outside := {
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
        · intro path hpath
          simp only [List.mem_singleton] at hpath
          subst path
          exact hnext
    }
    have hOldAvoidsL : C.toSupported.action.Avoids L.paths := by
      change (LocalAction.flip C.actionSwitch).Avoids [candy]
      intro path hpath passage hpassage
      simp only [List.mem_singleton] at hpath
      subst path
      intro hEq
      exact hcontact ⟨passage, hpassage, hEq⟩
    have hCflip : PathGrooves C.toSupported.paths
        (flipAt state (mouth / 3)) :=
      hCpaths.after_avoiding_action hNewAvoidsC'
    have hCandyFlip :
        PassagesGrooved (flipAt state (mouth / 3)) candy :=
      grooved_after_flip_other hCandy hCandyForeign
    have hLflip : PathGrooves L.paths
        (flipAt state (mouth / 3)) := by
      intro path hpath
      simp only [L, List.mem_singleton] at hpath
      subst path
      exact hCandyFlip
    have hperiod := C.toSupported.paired_period L
      hOldAvoidsL hNewAvoidsC'
      (flipAt state (mouth / 3)) hCflip hLflip
    have hpositive :
        0 < 2 * (C.toSupported.travel + L.travel) := by
      dsimp [L]
      omega
    have hlocal : EventuallyPeriodicWithin w
        (outside, flipAt state (mouth / 3))
        (2 * (C.toSupported.travel + (candy.length + 2))) := by
      exact eventuallyPeriodicWithin_of_period hpositive (by
        dsimp [L]
        omega) hperiod
    have hbudget :
        leadSteps +
            2 * (C.toSupported.travel + (candy.length + 2)) ≤
          13 * N := by
      rw [hleadLen, hcandyLen]
      omega
    exact (hlocal.prepend hreach).weaken hbudget

/-- A flip-reflector changed-forward merge closes within `13*N`. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_within_thirteen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R)) :
    EventuallyPeriodicWithin w
      (g, (ManufacturedReflector.flip R).activatedState) (13 * N) := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, hApproach, hApproachSimple,
      hApproachGrooved, hApproachForeign, hCandyEq,
      hentryBranch, _hmouthStem, hmouthLink, harms,
      hfullGrooved, hfullTrace, hcrossed, hRpaths, hCandy,
      hCandyForeign, hLobe, hreach, _hcomplete, hleadLen,
      _htailLen, _happroachLe⟩ :=
    hmerge.spliced_lobe_reflector_simple
  have hNpos : 0 < N := by
    have hports := hN mouth outside hmouthLink
    omega
  have hApproachOneLe : approach.length + 1 ≤ N := by
    have hmouthLt : mouth / 3 < N := by
      have hports := hN mouth outside hmouthLink
      omega
    have hmouthNotMem : mouth / 3 ∉ approach.map passageSwitch := by
      intro hm
      obtain ⟨passage, hpassage, hEq⟩ := List.mem_map.mp hm
      exact hApproachForeign passage hpassage hEq
    have hkeysNodup :
        (mouth / 3 :: approach.map passageSwitch).Nodup :=
      List.nodup_cons.mpr ⟨hmouthNotMem, hApproachSimple⟩
    have hkeysLt : ∀ s ∈ mouth / 3 :: approach.map passageSwitch,
        s < N := by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hmouthLt
      · exact hApproach.passage_switches_lt hN s hs
    have hlen := nodup_nat_lt_length hkeysNodup hkeysLt
    simpa using hlen
  have hleadLe : leadSteps ≤ N := by
    rw [hleadLen]
    exact hApproachOneLe
  have hcandyLen : candy.length =
      oldPrefix.length + approach.length := by
    rw [hCandyEq]
    simp [reversePassages_length]
  have hrouteSimple :=
    (ManufacturedReflector.flip R).orientedRoute_simple state
  have hOldTailSimple : SwitchSimple oldTail := by
    unfold SwitchSimple at hrouteSimple ⊢
    rw [hrouteSplit] at hrouteSimple
    simp only [List.map_append, List.map_cons] at hrouteSimple
    have hrest := (List.nodup_append.mp hrouteSimple).2.1
    exact (List.nodup_cons.mp hrest).2
  have holdTailLe : oldTail.length ≤ N :=
    hOldTail.switchSimple_length_le_switches hN hOldTailSimple
  have hrunwaySimple : SwitchSimple R.runway := by
    have hs := R.simple
    unfold SwitchSimple at hs ⊢
    simp only [List.map_append] at hs
    exact (List.nodup_append.mp hs).1
  have hrunwayLe : R.runway.length ≤ N :=
    R.runwayTrace.switchSimple_length_le_switches hN hrunwaySimple
  have happLe : approach.length ≤ N := by omega
  let cycleSteps :=
    oldTail.length + R.runway.length + approach.length + 2
  have hcycleLe : cycleSteps ≤ 4 * N := by
    dsimp [cycleSteps]
    omega
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    have hprefixLen :=
      R.runway_split_prefix_length state hrouteSplit hrunwaySplit
    have hcandyTight :
        candy.length = before.length + approach.length := by
      omega
    exact manufactured_flip_runway_splice_with_lead_within_thirteen
      hN R state hRpaths hrunwaySplit hmouthLink hentryBranch
      hfullGrooved hfullTrace hcrossed hCandy hCandyForeign hLobe
      hcandyTight hreach hleadLen hApproachOneLe
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        horiented hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    by_cases hcontact : ∃ passage ∈ approach,
        passageSwitch passage = R.actionSwitch
    · have hperiodic :=
        manufactured_flip_candy_splice_periodic_of_approach_contact
          R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
          hold horientation hentryGrooved hApproach hApproachGrooved
          hApproachForeign hcrossed hmouthLink harms hcontact
      have hperiod : stepN w cycleSteps
          (outside, flipAt state (mouth / 3)) =
            some (outside, flipAt state (mouth / 3)) := by
        simpa [cycleSteps] using hperiodic.2
      have hlocal : EventuallyPeriodicWithin w
          (outside, flipAt state (mouth / 3)) (4 * N) :=
        eventuallyPeriodicWithin_of_period (by
          dsimp [cycleSteps]
          omega) hcycleLe hperiod
      exact (hlocal.prepend hreach).weaken (by omega)
    · have hApproachForeignOld : ∀ passage ∈ approach,
          passageSwitch passage ≠ R.actionSwitch := by
        intro passage hpassage hEq
        exact hcontact ⟨passage, hpassage, hEq⟩
      have hperiodic :=
        manufactured_flip_candy_splice_periodic_of_approach_foreign
          R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
          hold horientation hentryGrooved hApproach hApproachForeign
          hApproachForeignOld hcrossed hmouthLink
      obtain ⟨settled, hcycleLead, hcyclePeriod⟩ := hperiodic.2
      have hcycleLead' : stepN w cycleSteps
          (outside, flipAt state (mouth / 3)) = some settled := by
        simpa [cycleSteps] using hcycleLead
      have hcyclePeriod' : stepN w cycleSteps settled = some settled := by
        simpa [cycleSteps] using hcyclePeriod
      have hlocal : EventuallyPeriodicWithin w
          (outside, flipAt state (mouth / 3)) (8 * N) :=
        ⟨cycleSteps, cycleSteps, settled, by
          dsimp [cycleSteps]
          omega, by omega, hcycleLead', hcyclePeriod'⟩
      exact (hlocal.prepend hreach).weaken (by omega)

/-- Every changed-forward merge closes within `16*N`. -/
theorem ManufacturedReflector.ChangedForwardMerge.within_sixteen_sharp
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B) :
    EventuallyPeriodicWithin w (g, B.activatedState) (16 * N) := by
  cases B with
  | stay R => exact hmerge.stay_within_sixteen hN
  | flip R => exact (hmerge.flip_within_thirteen hN).weaken (by omega)

/-- Damaged support is repaired or absorbed within `17*N`. -/
theorem manufactured_pair_protected_repair_within_seventeen
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState) :
    EventuallyPeriodicWithin w (g, B.activatedState) (17 * N) := by
  rcases manufactured_pair_protected_repair_quantitative_outcomes
      hN A B hA hB with hperiodic | hrest
  · exact hperiodic.weaken (by omega)
  · rcases hrest with hfacing | hrest
    · exact (hfacing.within_twelve hN).weaken (by omega)
    · rcases hrest with hchanged | hcomplete
      · exact (hchanged.within_sixteen_sharp hN).weaken (by omega)
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact A.completed_route_with_pair_support_within_seventeen
          hN B B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal

end GeneralN
