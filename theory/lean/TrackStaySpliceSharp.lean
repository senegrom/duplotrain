import TrackGlobalRepairSimple

/-!
# A changed-forward stay splice closes within nine N

The old `16*N` estimate treated the fresh lobe and retained suffix as if their
routes were arbitrary.  The strengthened splice certificate exposes two
switch-simple prefixes:

* the old prefix before the contact, including the contact switch, uses at
  most `N` switches;
* the fresh approach, including that same contacted switch, uses at most `N`
  switches.

Hence the spliced lobe has travel at most `2*N`.  The retained stay suffix has
travel at most `2*N`, its paired period costs at most `8*N`, and the approach
lead costs at most `N`.
-/

namespace GeneralN

/-- A state-changing forward splice into an identity reflector has a lasso of
size at most `9*N`. -/
theorem ManufacturedReflector.ChangedForwardMerge.stay_within_nine
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedStayReflector w e g}
    (hmerge : A.ChangedForwardMerge (.stay R)) :
    EventuallyPeriodicWithin w
      (g, (ManufacturedReflector.stay R).activatedState) (9 * N) := by
  obtain ⟨entry, mouth, _return, outside, oldPrefix, _oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, _hOldTail, hApproach, hApproachSimple,
      _hApproachGrooved, hApproachForeign, hCandyEq,
      _hentryBranch, _hmouthStem, hmouthLink, _harms,
      _hfullGrooved, _hfullTrace, _hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete, hleadLen, _htailLen, _happroachLe⟩ :=
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
  have hCandyLen : candy.length =
      oldPrefix.length + approach.length := by
    rw [hCandyEq]
    simp [reversePassages_length]
  have hCandyFlip :
      PassagesGrooved (flipAt state (mouth / 3)) candy :=
    grooved_after_flip_other hCandy hCandyForeign
  have hOldRoute :=
    (ManufacturedReflector.stay R).orientedRoute_trace state hRpaths
  have hOldSimple :=
    (ManufacturedReflector.stay R).orientedRoute_simple state
  have hOldLen :
      ((ManufacturedReflector.stay R).orientedRoute state).length ≤ N :=
    hOldRoute.switchSimple_length_le_switches hN hOldSimple
  have hOldPrefixOneLe : oldPrefix.length + 1 ≤ N := by
    rw [hrouteSplit] at hOldLen
    simp only [List.length_append, List.length_cons] at hOldLen
    omega
  have hLobeTravel : candy.length + 2 ≤ 2 * N := by
    rw [hCandyLen]
    omega
  have hOldGrooved := hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward : arrive state entry = (mouth, state) :=
    groove_forward (hOldGrooved (entry, mouth) horiented)
  have hentryMouthSwitch : entry / 3 = mouth / 3 := by
    have hswitch := arrive_exit_switch state entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  change (entry, mouth) ∈
      R.runway ++ [(R.mouth, R.arm)] at horiented
  rcases List.mem_append.mp horiented with hrunway | hcore
  · obtain ⟨before, after, hsplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨C, hCpaths, hAvoid⟩ :=
      R.suffix_after_runway_passage state hRpaths
        hsplit hmouthLink
    have hAvoid' :
        (LocalAction.flip (mouth / 3)).Avoids
          C.toSupported.paths := by
      simpa [hentryMouthSwitch] using hAvoid
    let L : SupportedReflector w mouth outside := {
      travel := candy.length + 2
      paths := [candy]
      action := .flip (mouth / 3)
      run := by
        intro current hpaths
        have hgrooved : PassagesGrooved current candy :=
          hpaths candy (by simp)
        obtain ⟨hstep, hnext⟩ := hLobe current hgrooved
        constructor
        · exact hstep
        · intro path hpath
          simp only [List.mem_singleton] at hpath
          subst path
          exact hnext
    }
    have hCflip : PathGrooves C.toSupported.paths
        (flipAt state (mouth / 3)) :=
      hCpaths.after_avoiding_action hAvoid'
    have hLflip : PathGrooves L.paths
        (flipAt state (mouth / 3)) := by
      intro path hpath
      simp only [L, List.mem_singleton] at hpath
      subst path
      exact hCandyFlip
    have hperiod := C.toSupported.paired_period L
      (by change True; trivial) hAvoid'
      (flipAt state (mouth / 3)) hCflip hLflip
    have hpositive :
        0 < 2 * (C.toSupported.travel + L.travel) := by
      dsimp [L]
      omega
    have hCtravel : C.toSupported.travel ≤ 2 * N := by
      simpa [ManufacturedReflector.toSupported] using
        (ManufacturedReflector.stay C).travel_le_two_mul_switches hN
    have hLtravel : L.travel ≤ 2 * N := by
      dsimp [L]
      exact hLobeTravel
    exact ⟨leadSteps, 2 * (C.toSupported.travel + L.travel),
      (outside, flipAt state (mouth / 3)), hpositive, by omega,
      hreach, hperiod⟩
  · simp only [List.mem_singleton] at hcore
    have hentryEq : entry = R.mouth :=
      congrArg Prod.fst hcore
    have hmouthEq : mouth = R.arm :=
      congrArg Prod.snd hcore
    subst entry
    subst mouth
    have houtsideEq : outside = R.arm := by
      rw [R.selfLink] at hmouthLink
      exact (Option.some.inj hmouthLink).symm
    subst outside
    have hfirst :=
      (hLobe (flipAt state (R.arm / 3)) hCandyFlip).1
    have hfirst' := hfirst
    change stepN w (candy.length + 2)
        (R.arm, flipAt state (R.arm / 3)) =
          some (R.arm,
            flipAt (flipAt state (R.arm / 3)) (R.arm / 3)) at hfirst'
    rw [flipAt_flipAt state (R.arm / 3)] at hfirst'
    have hsecond := (hLobe state hCandy).1
    have hperiod :
        stepN w ((candy.length + 2) + (candy.length + 2))
          (R.arm, flipAt state (R.arm / 3)) =
            some (R.arm, flipAt state (R.arm / 3)) := by
      rw [stepN_add, hfirst']
      exact hsecond
    have hpositive :
        0 < (candy.length + 2) + (candy.length + 2) := by
      omega
    exact ⟨leadSteps,
      (candy.length + 2) + (candy.length + 2),
      (R.arm, flipAt state (R.arm / 3)), hpositive,
      by omega, hreach, hperiod⟩

end GeneralN
