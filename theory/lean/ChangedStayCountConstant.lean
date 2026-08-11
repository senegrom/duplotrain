import TrackGlobalRepairActiveLead
import RepairLeadTwoPhase
import TwoPhasePrefixTailCount
import TrackStaySpliceAllTime

/-!
# Constant tongue count for protected changed-forward stay splices

Start the splice tail at the contact port, one step before the changed tongue
is installed.  Time zero has the contact state; the first step installs the
single flipped tongue; every later state is one of those same two phases.
The protected repair approach is itself two-phase and shares its contact
endpoint with that tail, so the whole branch costs at most three vectors.
-/

namespace GeneralN

private theorem stayconstant_twoPhase_concat
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
    simpa using hrun

/-- Joint certificate: the exact active repair approach and its exact
pre-contact stay-splice tail are exported from the same splice witnesses. -/
theorem ManufacturedReflector.ChangedForwardMerge.stay_active_precontact_two_phase
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedStayReflector w e g}
    (hmerge : A.ChangedForwardMerge (.stay R)) :
    ∃ approach returnPort state k,
      PhysicalTrace w
        (g, (ManufacturedReflector.stay R).activatedState)
        approach (returnPort, state) ∧
      SwitchSimple approach ∧
      (∀ passage ∈ approach,
        passage ∈ A.orientedRoute
          (ManufacturedReflector.stay R).activatedState) ∧
      PathGrooves (ManufacturedReflector.stay R).toSupported.paths state ∧
      ∀ d, ∃ port phase,
        stepN w d (returnPort, state) = some (port, phase) ∧
        (phase = flipAt state k ∨ phase = state) := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, _oldTail,
      approach, candy, state, _leadSteps, _tailSteps, horiented,
      _hrouteSplit, _hOldTail, _hApproachReplay, hApproachSimple,
      _hApproachGrooved, _hApproachForeign, _hCandyEq,
      hentryBranch, _hmouthStem, hmouthLink, _harms,
      hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, _hreach,
      _hcomplete, _hleadLen, _htailLen, _happroachLe,
      hActiveApproach, hApproachRoute⟩ :=
    hmerge.spliced_lobe_reflector_active_lead
  let k := mouth / 3
  let alternate := flipAt state k
  have hCandyFlip : PassagesGrooved alternate candy := by
    dsimp [alternate, k]
    exact grooved_after_flip_other hCandy hCandyForeign
  have hOldRoute :=
    (ManufacturedReflector.stay R).orientedRoute_trace state hRpaths
  have hOldSimple :=
    (ManufacturedReflector.stay R).orientedRoute_simple state
  have hOldGrooved := hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward : arrive state entry = (mouth, state) :=
    groove_forward (hOldGrooved (entry, mouth) horiented)
  have hentryMouthSwitch : entry / 3 = mouth / 3 := by
    have hswitch := arrive_exit_switch state entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  have hallAfter : ∀ d, ∃ port phase,
      stepN w d (outside, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = state) := by
    change (entry, mouth) ∈ R.runway ++ [(R.mouth, R.arm)] at horiented
    rcases List.mem_append.mp horiented with hrunway | hcore
    · obtain ⟨before, after, hsplit⟩ := List.append_of_mem hrunway
      obtain ⟨C, hCpaths, hAvoid⟩ :=
        R.suffix_after_runway_passage state hRpaths hsplit hmouthLink
      have hAvoid' : (LocalAction.flip k).Avoids C.toSupported.paths := by
        dsimp [k]
        simpa [hentryMouthSwitch] using hAvoid
      have hCalt : PathGrooves C.toSupported.paths alternate := by
        dsimp [alternate]
        exact hCpaths.after_avoiding_action hAvoid'
      let cTravel := C.toSupported.travel
      let lTravel := candy.length + 2
      have hCaltEnd : stepN w cTravel (outside, alternate) =
          some (mouth, alternate) := by
        dsimp [cTravel]
        exact (C.toSupported.run alternate hCalt).1
      have hCstateEnd : stepN w cTravel (outside, state) =
          some (mouth, state) := by
        dsimp [cTravel]
        exact (C.toSupported.run state hCpaths).1
      have hCaltPhase : ∀ d, d ≤ cTravel → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        obtain ⟨port, hrun⟩ := C.travel_state_stepN alternate hCalt (by
          simpa [cTravel, ManufacturedReflector.toSupported,
            ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, alternate, hrun, Or.inl rfl⟩
      have hCstatePhase : ∀ d, d ≤ cTravel → ∃ port phase,
          stepN w d (outside, state) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        obtain ⟨port, hrun⟩ := C.travel_state_stepN state hCpaths (by
          simpa [cTravel, ManufacturedReflector.toSupported,
            ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, state, hrun, Or.inr rfl⟩
      have hReverseEnd : stepN w lTravel (mouth, alternate) =
          some (outside, state) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (mouth, alternate) =
          some (outside, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd : stepN w lTravel (mouth, state) =
          some (outside, alternate) := by
        have h := (hLobe state hCandy).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, state) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase hfullGrooved hfullTrace
            hcrossed hmouthLink (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let half := cTravel + lTravel
      have hHalfAlt : stepN w half (outside, alternate) =
          some (outside, state) := by
        dsimp [half]
        rw [stepN_add, hCaltEnd]
        exact hReverseEnd
      have hHalfState : stepN w half (outside, state) =
          some (outside, alternate) := by
        dsimp [half]
        rw [stepN_add, hCstateEnd]
        exact hForwardEnd
      have hHalfAltPhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        exact stayconstant_twoPhase_concat hCaltEnd hCaltPhase
          hReversePhase d (by simpa [half] using hd)
      have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, state) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        exact stayconstant_twoPhase_concat hCstateEnd hCstatePhase
          hForwardPhase d (by simpa [half] using hd)
      let period := half + half
      have hperiod : stepN w period (outside, alternate) =
          some (outside, alternate) := by
        dsimp [period]
        rw [stepN_add, hHalfAlt]
        exact hHalfState
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        exact stayconstant_twoPhase_concat hHalfAlt hHalfAltPhase
          hHalfStatePhase d (by simpa [period] using hd)
      have hpositive : 0 < period := by
        have hcpos := (ManufacturedReflector.stay C).travel_pos
        dsimp [period, half, cTravel, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues hpositive hperiod hwindow
    · simp only [List.mem_singleton] at hcore
      have hentryEq : entry = R.mouth := congrArg Prod.fst hcore
      have hmouthEq : mouth = R.arm := congrArg Prod.snd hcore
      subst entry
      subst mouth
      have houtsideEq : outside = R.arm := by
        rw [R.selfLink] at hmouthLink
        exact (Option.some.inj hmouthLink).symm
      subst outside
      let lTravel := candy.length + 2
      have hReverseEnd : stepN w lTravel (R.arm, alternate) =
          some (R.arm, state) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (R.arm, alternate) =
          some (R.arm, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd : stepN w lTravel (R.arm, state) =
          some (R.arm, alternate) := by
        have h := (hLobe state hCandy).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, state) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase hfullGrooved hfullTrace
            hcrossed hmouthLink (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let period := lTravel + lTravel
      have hperiod : stepN w period (R.arm, alternate) =
          some (R.arm, alternate) := by
        dsimp [period]
        rw [stepN_add, hReverseEnd]
        exact hForwardEnd
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (R.arm, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = state) := by
        intro d hd
        exact stayconstant_twoPhase_concat hReverseEnd hReversePhase
          hForwardPhase d (by simpa [period] using hd)
      have hpositive : 0 < period := by
        dsimp [period, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues hpositive hperiod hwindow
  have hone : stepN w 1 (returnPort, state) =
      some (outside, alternate) := by
    simp [stepN, step, hcrossed, hmouthLink, alternate, k]
  have hall : ∀ d, ∃ port phase,
      stepN w d (returnPort, state) = some (port, phase) ∧
        (phase = flipAt state k ∨ phase = state) := by
    intro d
    cases d with
    | zero =>
        exact ⟨returnPort, state, by simp [stepN], Or.inr rfl⟩
    | succ n =>
        obtain ⟨port, phase, hrun, hphase⟩ := hallAfter n
        refine ⟨port, phase, ?_, ?_⟩
        · rw [show n + 1 = 1 + n by omega, stepN_add, hone]
          simpa using hrun
        · simpa [alternate] using hphase
  exact ⟨approach, returnPort, state, k,
    hActiveApproach, hApproachSimple, hApproachRoute, hRpaths, hall⟩

/-- **Protected changed-forward stay count:** at most three distinct restricted
tongue vectors. -/
theorem ManufacturedReflector.ChangedForwardMerge.stay_distinct_le_three
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedStayReflector w e g}
    (hA : PathGrooves A.toSupported.paths
      (ManufacturedReflector.stay R).baseState)
    (hBstart : PathGrooves (ManufacturedReflector.stay R).toSupported.paths
      (ManufacturedReflector.stay R).activatedState)
    (hmerge : A.ChangedForwardMerge (.stay R))
    (times : List Nat)
    (hlive : ∀ d ∈ times,
      (stepN w d (g, (ManufacturedReflector.stay R).activatedState)).isSome)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.stay R).activatedState))).Nodup) :
    times.length ≤ 3 := by
  obtain ⟨approach, returnPort, state, k,
      hActiveApproach, hApproachSimple, hApproachRoute,
      hRpaths, hall⟩ := hmerge.stay_active_precontact_two_phase
  have hphase := A.repair_prefix_two_phase (.stay R) hA hBstart
    hActiveApproach hApproachSimple hApproachRoute hRpaths
  have htail : ∀ tailTimes : List Nat,
      (∀ d ∈ tailTimes, (stepN w d (returnPort, state)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (returnPort, state))).Nodup →
      tailTimes.length ≤ 2 := by
    intro tailTimes _ htailNodup
    let history := [VectorCount.restrict N state,
      VectorCount.restrict N (flipAt state k)]
    have hcover : NoveltyCoverOn w N (returnPort, state)
        tailTimes [] 2 := by
      refine ⟨history, by simp [history], ?_⟩
      intro d hd
      simp only [List.nil_append]
      obtain ⟨port, phase, hrun, hphaseTail⟩ := hall d
      have hvec : restrictedTonguesAt w N (returnPort, state) d =
          VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hrun]
      rw [hvec]
      rcases hphaseTail with h | h
      · simp [history, h]
      · simp [history, h]
    have hcount := noveltyCoverOn_distinct_count hcover htailNodup
    simpa using hcount
  exact two_phase_prefix_then_direct_tail_distinct_le_succ
    hActiveApproach.sound hphase htail (by omega) times hlive hnd

end GeneralN
