import TrackThetaPointwiseCore
import TrackNoveltyCover

/-!
# All-time phase covers for theta-intersecting reflector pairs

Composing the pointwise dichotomy around the theta cycles yields absolute
phase covers: a one-sided theta intersection visits at most **four** tongue
vectors at *every* time, a mutual intersection at most **three**.  Together
with `manufactured_pair_all_time_four_phase_tongues` (the avoiding case)
this removes the last time-counted lasso from the flip/flip reflector-pair
analysis: `manufactured_flip_pair_all_time_four_phase` below covers every
flip/flip pair, however its supports intersect, by the same four vectors

    state, state+A, state+B, state+A+B.

All statements carry liveness (`stepN … = some …`), so they compose under
time shifts.  No switch-count hypothesis appears: the covers are blind to
path lengths.
-/

namespace GeneralN

/-- Any lasso whose lead and cycle windows are phase-covered is
phase-covered (and live) at every absolute time. -/
private theorem lasso_all_time_phase
    {w : Wiring} {start settled : Nat × Tongues} {lead period : Nat}
    {phases : List Tongues}
    (hpos : 0 < period)
    (hsettle : stepN w lead start = some settled)
    (hperiod : stepN w period settled = some settled)
    (hleadPhase : ∀ d, d ≤ lead → ∃ port phase,
      stepN w d start = some (port, phase) ∧ phase ∈ phases)
    (hcyclePhase : ∀ r, r ≤ period → ∃ port phase,
      stepN w r settled = some (port, phase) ∧ phase ∈ phases)
    (d : Nat) :
    ∃ port phase, stepN w d start = some (port, phase) ∧
      phase ∈ phases := by
  by_cases hdlead : d ≤ lead
  · exact hleadPhase d hdlead
  · let k := d - lead
    let q := k / period
    let r := k % period
    have hr : r < period := by
      dsimp [r]
      exact Nat.mod_lt _ hpos
    have hkEq : k = q * period + r := by
      dsimp [q, r]
      have hdiv := Nat.div_add_mod k period
      rw [Nat.mul_comm period (k / period)] at hdiv
      omega
    have hdEq : d = lead + (q * period + r) := by
      rw [← hkEq]
      dsimp [k]
      omega
    have hcycle := stepN_mul_period_pair_novelty hperiod q
    obtain ⟨port, phase, hrunR, hphase⟩ :=
      hcyclePhase r (Nat.le_of_lt hr)
    refine ⟨port, phase, ?_, hphase⟩
    rw [hdEq, stepN_add, hsettle]
    simp only [Option.bind_some]
    rw [stepN_add, hcycle]
    simpa using hrunR

/-- **Pointwise theta half.**  One macro-step of the theta walk, with a
three-phase cover at every intermediate time. -/
theorem manufactured_theta_half_pointwise
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch) :
    ∃ travel, 0 < travel ∧
      stepN w travel (g, state) =
        some (g, flipAt state B.actionSwitch) ∧
      ∀ d, d ≤ travel → ∃ port phase,
        stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = flipAt state A.actionSwitch ∨
          phase = flipAt state B.actionSwitch) := by
  have hArun := (A.toSupported.run state hA).1
  change stepN w (2 * A.runway.length + A.candy.length + 2)
    (g, state) = some (e, flipAt state A.actionSwitch) at hArun
  rcases manufactured_support_fault_dichotomy_pointwise
      A B state hA hB hcontact with hcap | hrep
  · obtain ⟨cap, hcapEnd, hcapPhases⟩ := hcap
    have hBrun := (B.toSupported.run state hB).1
    change stepN w (2 * B.runway.length + B.candy.length + 2)
      (e, state) = some (g, flipAt state B.actionSwitch) at hBrun
    refine ⟨(2 * A.runway.length + A.candy.length + 2) + cap +
      (2 * B.runway.length + B.candy.length + 2), by omega, ?_, ?_⟩
    · have hlen : (2 * A.runway.length + A.candy.length + 2) + cap +
          (2 * B.runway.length + B.candy.length + 2) =
          (2 * A.runway.length + A.candy.length + 2) +
            (cap + (2 * B.runway.length + B.candy.length + 2)) := by
        omega
      rw [hlen, stepN_add, hArun]
      simp only [Option.bind_some]
      rw [stepN_add, hcapEnd]
      simpa using hBrun
    · intro d hd
      by_cases hd1 : d ≤ 2 * A.runway.length + A.candy.length + 2
      · obtain ⟨port, phase, hrun, hphase⟩ :=
          A.travel_two_phase_stepN state hA hd1
        refine ⟨port, phase, hrun, ?_⟩
        rcases hphase with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · by_cases hd2 : d ≤
            (2 * A.runway.length + A.candy.length + 2) + cap
        · let rdepth := d - (2 * A.runway.length + A.candy.length + 2)
          have hrle : rdepth ≤ cap := by
            dsimp [rdepth]
            omega
          have hdEq : d =
              (2 * A.runway.length + A.candy.length + 2) + rdepth := by
            dsimp [rdepth]
            omega
          obtain ⟨port, phase, hrunR, hphase⟩ := hcapPhases rdepth hrle
          refine ⟨port, phase, ?_, ?_⟩
          · rw [hdEq, stepN_add, hArun]
            simpa using hrunR
          · rcases hphase with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
        · let rdepth := d -
            ((2 * A.runway.length + A.candy.length + 2) + cap)
          have hrle : rdepth ≤
              2 * B.runway.length + B.candy.length + 2 := by
            dsimp [rdepth]
            omega
          have hdEq : d =
              ((2 * A.runway.length + A.candy.length + 2) + cap) +
                rdepth := by
            dsimp [rdepth]
            omega
          have hmid : stepN w
              ((2 * A.runway.length + A.candy.length + 2) + cap)
              (g, state) = some (e, state) := by
            rw [stepN_add, hArun]
            simpa using hcapEnd
          obtain ⟨port, phase, hrunR, hphase⟩ :=
            B.travel_two_phase_stepN state hB hrle
          refine ⟨port, phase, ?_, ?_⟩
          · rw [hdEq, stepN_add, hmid]
            simpa using hrunR
          · rcases hphase with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
  · obtain ⟨hrepEnd, hrepPhases⟩ := hrep
    refine ⟨(2 * A.runway.length + A.candy.length + 2) +
      (2 * B.runway.length + B.candy.length + 2), by omega, ?_, ?_⟩
    · rw [stepN_add, hArun]
      simpa using hrepEnd
    · intro d hd
      by_cases hd1 : d ≤ 2 * A.runway.length + A.candy.length + 2
      · obtain ⟨port, phase, hrun, hphase⟩ :=
          A.travel_two_phase_stepN state hA hd1
        refine ⟨port, phase, hrun, ?_⟩
        rcases hphase with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · let rdepth := d - (2 * A.runway.length + A.candy.length + 2)
        have hrle : rdepth ≤
            2 * B.runway.length + B.candy.length + 2 := by
          dsimp [rdepth]
          omega
        have hdEq : d =
            (2 * A.runway.length + A.candy.length + 2) + rdepth := by
          dsimp [rdepth]
          omega
        obtain ⟨port, phase, hrunR, hphase⟩ := hrepPhases rdepth hrle
        refine ⟨port, phase, ?_, ?_⟩
        · rw [hdEq, stepN_add, hArun]
          simpa using hrunR
        · rcases hphase with h | h
          · exact Or.inr (Or.inl h)
          · rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)

/-- **One-sided theta intersection: absolute four-phase law.**  If `B`'s
support touches `A`'s switch but `B`'s action avoids `A`'s support, the
walk from `(g, state)` is live forever and visits at most four tongue
vectors, ever. -/
theorem manufactured_one_sided_theta_all_time_four_phase
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : (LocalAction.flip B.actionSwitch).Avoids
      [A.runway, A.candy])
    (d : Nat) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      phase ∈ [state, flipAt state A.actionSwitch,
        flipAt state B.actionSwitch,
        flipAt (flipAt state B.actionSwitch) A.actionSwitch] := by
  obtain ⟨t1, ht1pos, ht1end, ht1phases⟩ :=
    manufactured_theta_half_pointwise A B state hA hB hcontact
  have hA' : PathGrooves [A.runway, A.candy]
      (flipAt state B.actionSwitch) :=
    hA.after_avoiding_action hBA
  have hB' : PathGrooves [B.runway, B.candy]
      (flipAt state B.actionSwitch) :=
    (B.toSupported.run state hB).2
  obtain ⟨t2, ht2pos, ht2end, ht2phases⟩ :=
    manufactured_theta_half_pointwise A B
      (flipAt state B.actionSwitch) hA' hB' hcontact
  have ht2end' : stepN w t2 (g, flipAt state B.actionSwitch) =
      some (g, state) := by
    rw [flipAt_flipAt] at ht2end
    exact ht2end
  have hperiod : stepN w (t1 + t2) (g, state) = some (g, state) := by
    rw [stepN_add, ht1end]
    simpa using ht2end'
  refine lasso_all_time_phase (lead := 0) (settled := (g, state))
    (by omega) (by simp [stepN]) hperiod ?_ ?_ d
  · intro dd hdd
    have hdd0 : dd = 0 := by omega
    subst hdd0
    exact ⟨g, state, by simp [stepN], by simp⟩
  · intro r hr
    by_cases hr1 : r ≤ t1
    · obtain ⟨port, phase, hrun, hphase⟩ := ht1phases r hr1
      refine ⟨port, phase, hrun, ?_⟩
      rcases hphase with h | h
      · simp [h]
      · rcases h with h | h
        · simp [h]
        · simp [h]
    · let rr := r - t1
      have hrrle : rr ≤ t2 := by
        dsimp [rr]
        omega
      have hrEq : r = t1 + rr := by
        dsimp [rr]
        omega
      obtain ⟨port, phase, hrunR, hphase⟩ := ht2phases rr hrrle
      refine ⟨port, phase, ?_, ?_⟩
      · rw [hrEq, stepN_add, ht1end]
        simpa using hrunR
      · rcases hphase with h | h
        · simp [h]
        · rcases h with h | h
          · simp [h]
          · rw [flipAt_flipAt] at h
            simp [h]

/-- **Mutual theta intersection: absolute three-phase law.**  If each
support touches the other's switch, the walk from `(g, state)` is live
forever and visits at most three tongue vectors, ever. -/
theorem manufactured_two_sided_theta_all_time_three_phase
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hAB : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : ∃ path ∈ [A.runway, A.candy],
      ∃ passage ∈ path,
        passageSwitch passage = B.actionSwitch)
    (d : Nat) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      phase ∈ [state, flipAt state A.actionSwitch,
        flipAt state B.actionSwitch] := by
  obtain ⟨lead, hleadPos, hleadEnd, hleadPhases⟩ :=
    manufactured_theta_half_pointwise A B state hA hB hAB
  have hleadPhases' : ∀ dd, dd ≤ lead → ∃ port phase,
      stepN w dd (g, state) = some (port, phase) ∧
      phase ∈ [state, flipAt state A.actionSwitch,
        flipAt state B.actionSwitch] := by
    intro dd hdd
    obtain ⟨port, phase, hrun, hphase⟩ := hleadPhases dd hdd
    refine ⟨port, phase, hrun, ?_⟩
    rcases hphase with h | h
    · simp [h]
    · rcases h with h | h
      · simp [h]
      · simp [h]
  rcases manufactured_support_fault_dichotomy_pointwise
      B A state hB hA hBA with hrevCap | hrevRep
  · obtain ⟨revCap, hrevEnd, hrevPhases⟩ := hrevCap
    have hperiod : stepN w (lead + revCap) (g, state) =
        some (g, state) := by
      rw [stepN_add, hleadEnd]
      simpa using hrevEnd
    refine lasso_all_time_phase (lead := 0) (settled := (g, state))
      (by omega) (by simp [stepN]) hperiod ?_ ?_ d
    · intro dd hdd
      have hdd0 : dd = 0 := by omega
      subst hdd0
      exact ⟨g, state, by simp [stepN], by simp⟩
    · intro r hr
      by_cases hr1 : r ≤ lead
      · exact hleadPhases' r hr1
      · let rr := r - lead
        have hrrle : rr ≤ revCap := by
          dsimp [rr]
          omega
        have hrEq : r = lead + rr := by
          dsimp [rr]
          omega
        obtain ⟨port, phase, hrunR, hphase⟩ := hrevPhases rr hrrle
        refine ⟨port, phase, ?_, ?_⟩
        · rw [hrEq, stepN_add, hleadEnd]
          simpa using hrunR
        · rcases hphase with h | h
          · simp [h]
          · simp [h]
  · obtain ⟨hrevRepEnd, hrevRepPhases⟩ := hrevRep
    have hrevRepPhases' : ∀ r,
        r ≤ 2 * A.runway.length + A.candy.length + 2 →
        ∃ port phase,
          stepN w r (g, flipAt state B.actionSwitch) =
            some (port, phase) ∧
          phase ∈ [state, flipAt state A.actionSwitch,
            flipAt state B.actionSwitch] := by
      intro r hrle
      obtain ⟨port, phase, hrunR, hphase⟩ := hrevRepPhases r hrle
      refine ⟨port, phase, hrunR, ?_⟩
      rcases hphase with h | h
      · simp [h]
      · rcases h with h | h
        · simp [h]
        · simp [h]
    rcases manufactured_support_fault_dichotomy_pointwise
        A B state hA hB hAB with hfwdCap | hfwdRep
    · obtain ⟨fwdCap, hfwdEnd, hfwdPhases⟩ := hfwdCap
      have hBrun := (B.toSupported.run state hB).1
      change stepN w (2 * B.runway.length + B.candy.length + 2)
        (e, state) = some (g, flipAt state B.actionSwitch) at hBrun
      have hperiodS : stepN w
          ((2 * A.runway.length + A.candy.length + 2) + fwdCap +
            (2 * B.runway.length + B.candy.length + 2))
          (g, flipAt state B.actionSwitch) =
            some (g, flipAt state B.actionSwitch) := by
        have hlen : (2 * A.runway.length + A.candy.length + 2) +
            fwdCap + (2 * B.runway.length + B.candy.length + 2) =
            (2 * A.runway.length + A.candy.length + 2) +
              (fwdCap +
                (2 * B.runway.length + B.candy.length + 2)) := by
          omega
        rw [hlen, stepN_add, hrevRepEnd]
        simp only [Option.bind_some]
        rw [stepN_add, hfwdEnd]
        simpa using hBrun
      refine lasso_all_time_phase (lead := lead)
        (settled := (g, flipAt state B.actionSwitch))
        (by omega) hleadEnd hperiodS hleadPhases' ?_ d
      intro r hr
      by_cases hr1 : r ≤ 2 * A.runway.length + A.candy.length + 2
      · exact hrevRepPhases' r hr1
      · by_cases hr2 : r ≤
            (2 * A.runway.length + A.candy.length + 2) + fwdCap
        · let rr := r - (2 * A.runway.length + A.candy.length + 2)
          have hrrle : rr ≤ fwdCap := by
            dsimp [rr]
            omega
          have hrEq : r =
              (2 * A.runway.length + A.candy.length + 2) + rr := by
            dsimp [rr]
            omega
          obtain ⟨port, phase, hrunR, hphase⟩ := hfwdPhases rr hrrle
          refine ⟨port, phase, ?_, ?_⟩
          · rw [hrEq, stepN_add, hrevRepEnd]
            simpa using hrunR
          · rcases hphase with h | h
            · simp [h]
            · simp [h]
        · let rr := r -
            ((2 * A.runway.length + A.candy.length + 2) + fwdCap)
          have hrrle : rr ≤
              2 * B.runway.length + B.candy.length + 2 := by
            dsimp [rr]
            omega
          have hrEq : r =
              ((2 * A.runway.length + A.candy.length + 2) + fwdCap) +
                rr := by
            dsimp [rr]
            omega
          have hmid : stepN w
              ((2 * A.runway.length + A.candy.length + 2) + fwdCap)
              (g, flipAt state B.actionSwitch) = some (e, state) := by
            rw [stepN_add, hrevRepEnd]
            simpa using hfwdEnd
          obtain ⟨port, phase, hrunR, hphase⟩ :=
            B.travel_two_phase_stepN state hB hrrle
          refine ⟨port, phase, ?_, ?_⟩
          · rw [hrEq, stepN_add, hmid]
            simpa using hrunR
          · rcases hphase with h | h
            · simp [h]
            · simp [h]
    · obtain ⟨hfwdRepEnd, hfwdRepPhases⟩ := hfwdRep
      have hperiodS : stepN w
          ((2 * A.runway.length + A.candy.length + 2) +
            (2 * B.runway.length + B.candy.length + 2))
          (g, flipAt state B.actionSwitch) =
            some (g, flipAt state B.actionSwitch) := by
        rw [stepN_add, hrevRepEnd]
        simpa using hfwdRepEnd
      refine lasso_all_time_phase (lead := lead)
        (settled := (g, flipAt state B.actionSwitch))
        (by omega) hleadEnd hperiodS hleadPhases' ?_ d
      intro r hr
      by_cases hr1 : r ≤ 2 * A.runway.length + A.candy.length + 2
      · exact hrevRepPhases' r hr1
      · let rr := r - (2 * A.runway.length + A.candy.length + 2)
        have hrrle : rr ≤
            2 * B.runway.length + B.candy.length + 2 := by
          dsimp [rr]
          omega
        have hrEq : r =
            (2 * A.runway.length + A.candy.length + 2) + rr := by
          dsimp [rr]
          omega
        obtain ⟨port, phase, hrunR, hphase⟩ := hfwdRepPhases rr hrrle
        refine ⟨port, phase, ?_, ?_⟩
        · rw [hrEq, stepN_add, hrevRepEnd]
          simpa using hrunR
        · rcases hphase with h | h
          · simp [h]
          · rcases h with h | h
            · simp [h]
            · simp [h]

/-- Liveness at all times from a closed period. -/
private theorem period_all_time_live
    {w : Wiring} {s : Nat × Tongues} {period : Nat}
    (hpos : 0 < period)
    (hperiod : stepN w period s = some s) (d : Nat) :
    ∃ mid, stepN w d s = some mid := by
  let q := d / period
  let r := d % period
  have hr : r < period := by
    dsimp [r]
    exact Nat.mod_lt _ hpos
  have hdEq : d = q * period + r := by
    dsimp [q, r]
    have hdiv := Nat.div_add_mod d period
    rw [Nat.mul_comm period (d / period)] at hdiv
    omega
  obtain ⟨mid, hmid⟩ := stepN_prefix_some (Nat.le_of_lt hr) hperiod
  refine ⟨mid, ?_⟩
  rw [hdEq, stepN_add, stepN_mul_period_pair_novelty hperiod q]
  simpa using hmid

/-- **Every flip/flip pair has an absolute four-phase law.**  Whatever the
intersection pattern of the two supports — disjoint, one-sided, or mutual —
the walk from `(g, state)` is live forever and visits only the four
commuting-involution corners

    state, state+A, state+B, state+A+B. -/
theorem manufactured_flip_pair_all_time_four_phase
    {w : Wiring} {g e : Nat}
    (FA : ManufacturedFlipReflector w g e)
    (FB : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [FA.runway, FA.candy] state)
    (hB : PathGrooves [FB.runway, FB.candy] state)
    (d : Nat) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      phase ∈ [state, flipAt state FA.actionSwitch,
        flipAt state FB.actionSwitch,
        flipAt (flipAt state FA.actionSwitch) FB.actionSwitch] := by
  classical
  by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
      [FB.runway, FB.candy]
  · by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
        [FA.runway, FA.candy]
    · -- disjoint supports: the compatible-pair four-corner orbit
      have hA' : PathGrooves
          (ManufacturedReflector.flip FA).toSupported.paths state := hA
      have hB' : PathGrooves
          (ManufacturedReflector.flip FB).toSupported.paths state := hB
      have hAB' : (ManufacturedReflector.flip FA).toSupported.action.Avoids
          (ManufacturedReflector.flip FB).toSupported.paths := hAB
      have hBA' : (ManufacturedReflector.flip FB).toSupported.action.Avoids
          (ManufacturedReflector.flip FA).toSupported.paths := hBA
      have hperiod :=
        (ManufacturedReflector.flip FA).toSupported.paired_period
          (ManufacturedReflector.flip FB).toSupported
          hAB' hBA' state hA' hB'
      have hApos : 0 < (ManufacturedReflector.flip FA).toSupported.travel :=
        (ManufacturedReflector.flip FA).travel_pos
      have hpos : 0 <
          2 * ((ManufacturedReflector.flip FA).toSupported.travel +
            (ManufacturedReflector.flip FB).toSupported.travel) := by
        omega
      obtain ⟨mid, hmid⟩ := period_all_time_live hpos hperiod d
      rcases mid with ⟨port, phase⟩
      have hmem := manufactured_pair_all_time_four_phase_tongues
        (ManufacturedReflector.flip FA) (ManufacturedReflector.flip FB)
        state hA' hB' hAB' hBA' d
      have hph : tonguesAt w (g, state) d = phase := by
        simp [tonguesAt, hmid]
      rw [hph] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      refine ⟨port, phase, hmid, ?_⟩
      rcases hmem with h | h | h | h
      · simp [h]
      · have h' : phase = flipAt state FA.actionSwitch := h
        simp [h']
      · have h' : phase =
            flipAt (flipAt state FA.actionSwitch) FB.actionSwitch := h
        simp [h']
      · have h' : phase =
            flipAt (flipAt (flipAt state FA.actionSwitch)
              FB.actionSwitch) FA.actionSwitch := h
        by_cases hsw : FA.actionSwitch = FB.actionSwitch
        · rw [← hsw, flipAt_flipAt] at h'
          simp [h']
        · rw [flipAt_comm hsw, flipAt_flipAt] at h'
          simp [h']
    · -- FA's action avoids FB's support, FB's support meets FA's switch:
      -- one FA-traversal, then the one-sided theta seen from `e`
      have hcontactBA := contact_of_not_avoids_flip hBA
      have hArun := (FA.toSupported.run state hA).1
      change stepN w (2 * FA.runway.length + FA.candy.length + 2)
        (g, state) = some (e, flipAt state FA.actionSwitch) at hArun
      have hA2 : PathGrooves [FA.runway, FA.candy]
          (flipAt state FA.actionSwitch) :=
        (FA.toSupported.run state hA).2
      have hB2 : PathGrooves [FB.runway, FB.candy]
          (flipAt state FA.actionSwitch) :=
        hB.after_avoiding_action hAB
      by_cases hd1 : d ≤ 2 * FA.runway.length + FA.candy.length + 2
      · obtain ⟨port, phase, hrun, hphase⟩ :=
          FA.travel_two_phase_stepN state hA hd1
        refine ⟨port, phase, hrun, ?_⟩
        rcases hphase with h | h
        · simp [h]
        · simp [h]
      · let rr := d - (2 * FA.runway.length + FA.candy.length + 2)
        have hdEq : d =
            (2 * FA.runway.length + FA.candy.length + 2) + rr := by
          dsimp [rr]
          omega
        obtain ⟨port, phase, hrunR, hmem⟩ :=
          manufactured_one_sided_theta_all_time_four_phase FB FA
            (flipAt state FA.actionSwitch) hB2 hA2 hcontactBA hAB rr
        refine ⟨port, phase, ?_, ?_⟩
        · rw [hdEq, stepN_add, hArun]
          simpa using hrunR
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h | h | h
          · simp [h]
          · simp [h]
          · rw [flipAt_flipAt] at h
            simp [h]
          · rw [flipAt_flipAt] at h
            simp [h]
  · have hcontactAB := contact_of_not_avoids_flip hAB
    by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
        [FA.runway, FA.candy]
    · -- FB's support avoided, FA's switch meets FB's support: direct
      -- one-sided theta from `g`
      obtain ⟨port, phase, hrun, hmem⟩ :=
        manufactured_one_sided_theta_all_time_four_phase FA FB
          state hA hB hcontactAB hBA d
      refine ⟨port, phase, hrun, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
      · by_cases hsw : FA.actionSwitch = FB.actionSwitch
        · rw [← hsw, flipAt_flipAt] at h
          simp [h]
        · rw [flipAt_comm (Ne.symm hsw)] at h
          simp [h]
    · -- mutual contact: the three-phase theta
      have hcontactBA := contact_of_not_avoids_flip hBA
      obtain ⟨port, phase, hrun, hmem⟩ :=
        manufactured_two_sided_theta_all_time_three_phase FA FB
          state hA hB hcontactAB hcontactBA d
      refine ⟨port, phase, hrun, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h
      · simp [h]
      · simp [h]
      · simp [h]

/-- **Distinct-vector count for any flip/flip pair: at most four.**  No
liveness hypothesis is needed — the four-phase law itself carries the
liveness of every sampled time. -/
theorem manufactured_flip_pair_distinct_le_four
    {w : Wiring} {N g e : Nat}
    (FA : ManufacturedFlipReflector w g e)
    (FB : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [FA.runway, FA.candy] state)
    (hB : PathGrooves [FB.runway, FB.candy] state)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ 4 := by
  have hcover : NoveltyCoverOn w N (g, state) times [] 4 := by
    refine ⟨[VectorCount.restrict N state,
      VectorCount.restrict N (flipAt state FA.actionSwitch),
      VectorCount.restrict N (flipAt state FB.actionSwitch),
      VectorCount.restrict N
        (flipAt (flipAt state FA.actionSwitch) FB.actionSwitch)],
      by simp, ?_⟩
    intro k hk
    obtain ⟨port, phase, hrun, hmem⟩ :=
      manufactured_flip_pair_all_time_four_phase FA FB state hA hB k
    have hph : restrictedTonguesAt w N (g, state) k =
        VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hrun]
    rw [hph]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
    · simp [h]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

end GeneralN
