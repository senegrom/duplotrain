import TrackGlobalRepairSimple
import TrackStayContactAllTime

/-!
# Absolute two-phase law for changed-forward stay splices

After the switch-simple lead, a changed-forward splice into a stay reflector
pairs an identity suffix with one explicit lobe.  The identity side changes no
tongue; the explicit lobe toggles one tongue.  Hence the whole infinite tail
has exactly two possible tongue vectors, irrespective of its physical travel.
-/

namespace GeneralN

/-- A changed-forward stay splice has a switch-simple lead of at most `N`,
after which every future tongue vector is one of two phases. -/
theorem ManufacturedReflector.ChangedForwardMerge.stay_two_phase_tail
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedStayReflector w e g}
    (hmerge : A.ChangedForwardMerge (.stay R)) :
    ∃ lead outside state k,
      lead ≤ N ∧
      stepN w lead
        (g, (ManufacturedReflector.stay R).activatedState) =
          some (outside, flipAt state k) ∧
      ∀ d, ∃ port phase,
        stepN w d (outside, flipAt state k) =
          some (port, phase) ∧
        (phase = flipAt state k ∨ phase = state) := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, _oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, _hOldTail, hApproach, hApproachSimple,
      _hApproachGrooved, hApproachForeign, _hCandyEq,
      hentryBranch, _hmouthStem, hmouthLink, _harms,
      hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete, hleadLen, _htailLen, _happroachLe⟩ :=
    hmerge.spliced_lobe_reflector_simple
  let k := mouth / 3
  let alternate := flipAt state k
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
      exact stay_twoPhase_concat hCaltEnd hCaltPhase
        hReversePhase d (by simpa [half] using hd)
    have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
        stepN w d (outside, state) = some (port, phase) ∧
          (phase = alternate ∨ phase = state) := by
      intro d hd
      exact stay_twoPhase_concat hCstateEnd hCstatePhase
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
      exact stay_twoPhase_concat hHalfAlt hHalfAltPhase
        hHalfStatePhase d (by simpa [period] using hd)
    have hpositive : 0 < period := by
      have hcpos := (ManufacturedReflector.stay C).travel_pos
      dsimp [period, half, cTravel, lTravel]
      omega
    refine ⟨leadSteps, outside, state, k, hleadLe, ?_, ?_⟩
    · simpa [alternate, k] using hreach
    · simpa [alternate] using
        (periodic_two_phase_prefix_tongues hpositive hperiod hwindow)
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
      exact stay_twoPhase_concat hReverseEnd hReversePhase
        hForwardPhase d (by simpa [period] using hd)
    have hpositive : 0 < period := by
      dsimp [period, lTravel]
      omega
    refine ⟨leadSteps, R.arm, state, k, hleadLe, ?_, ?_⟩
    · simpa [alternate, k] using hreach
    · simpa [alternate] using
        (periodic_two_phase_prefix_tongues hpositive hperiod hwindow)

/-- A changed-forward stay splice exposes at most `N+2` distinct restricted
tongue vectors: fewer than `N` pre-tail positions and two absolute tail
phases. -/
theorem ManufacturedReflector.ChangedForwardMerge.stay_distinct_le_n_succ_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedStayReflector w e g}
    (hmerge : A.ChangedForwardMerge (.stay R))
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.stay R).activatedState))).Nodup) :
    times.length ≤ N + 2 := by
  obtain ⟨lead, outside, state, k, hleadLe, hreach, htail⟩ :=
    hmerge.stay_two_phase_tail hN
  let start :=
    (g, (ManufacturedReflector.stay R).activatedState)
  let history := (List.range lead).map
    (restrictedTonguesAt w N start)
  let alternate := flipAt state k
  have hcover : NoveltyCoverOn w N start times history 2 := by
    refine ⟨[VectorCount.restrict N alternate,
      VectorCount.restrict N state], by simp, ?_⟩
    intro d hd
    by_cases hbefore : d < lead
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨d, List.mem_range.mpr hbefore, rfl⟩
    · let q := d - lead
      have hdq : d = lead + q := by
        dsimp [q]
        omega
      obtain ⟨port, phase, hrun, hphase⟩ := htail q
      have hglobal : stepN w d start = some (port, phase) := by
        rw [hdq, stepN_add, hreach]
        exact hrun
      have hvector : restrictedTonguesAt w N start d =
          VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hglobal]
      rw [hvector]
      apply List.mem_append_right history
      rcases hphase with rfl | rfl <;> simp [alternate]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistoryLen : history.length = lead := by simp [history]
  omega

end GeneralN
