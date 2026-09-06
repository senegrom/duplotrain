import TrackThetaPointwiseCore

/-!
# All-time phase covers for theta-intersecting reflector pairs

Closing a boundary invariant under positive-length excursions yields absolute
phase covers: a one-sided theta intersection visits at most **four** tongue
vectors at *every* time, a mutual intersection at most **three**.  Together
with `manufactured_pair_all_time_four_phase_tongues` (the avoiding case)
this removes the last time-counted lasso from the flip/flip reflector-pair
analysis: `manufactured_flip_pair_all_time_four_phase` below covers every
flip/flip pair, however its supports intersect, by the same four vectors

    state, state+A, state+B, state+A+B.

The contact cases use covered positive-length excursions, not explicit periods.
All statements carry liveness (`stepN … = some …`) and compose under time shifts.
No switch-count hypothesis appears: phase covers are independent of path lengths.
-/

namespace GeneralN


section
variable {w : Wiring} {g e : Nat}
  (A : ManufacturedFlipReflector w g e)
  (B : ManufacturedFlipReflector w e g)
  (state : Tongues)
  (hA : PathGrooves [A.runway, A.candy] state)
  (hB : PathGrooves [B.runway, B.candy] state)
include w g e A B state hA hB

/-- **Pointwise theta half.**  One macro-step of the theta walk, with a
three-phase cover at every intermediate time. -/
theorem manufactured_theta_half_pointwise
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
  let safe := fun phase => phase ∈ [state, flipAt state A.actionSwitch,
    flipAt state B.actionSwitch, flipAt (flipAt state B.actionSwitch) A.actionSwitch]
  let boundary := fun c => c = (g, state) ∨ c = (g, flipAt state B.actionSwitch)
  have hprogress : ∀ start, boundary start → ∃ travel finish,
      0 < travel ∧ stepN w travel start = some finish ∧ boundary finish ∧
      ∀ t, t ≤ travel → ∃ port phase,
        stepN w t start = some (port, phase) ∧ safe phase := by
    intro start hs
    rcases hs with rfl | rfl
    · obtain ⟨travel, hpos, hr, hp⟩ :=
        manufactured_theta_half_pointwise A B state hA hB hcontact
      refine ⟨travel, (g, flipAt state B.actionSwitch), hpos, hr, Or.inr rfl, ?_⟩
      intro t ht
      obtain ⟨port, phase, hr, hv⟩ := hp t ht
      exact ⟨port, phase, hr, by rcases hv with rfl | rfl | rfl <;> simp [safe]⟩
    · have hA' := hA.after_avoiding_action hBA
      have hB' := (B.toSupported.run state hB).2
      obtain ⟨travel, hpos, hr, hp⟩ := manufactured_theta_half_pointwise A B
        (flipAt state B.actionSwitch) hA' hB' hcontact
      rw [flipAt_flipAt] at hr
      refine ⟨travel, (g, state), hpos, hr, Or.inl rfl, ?_⟩
      intro t ht
      obtain ⟨port, phase, hr, hv⟩ := hp t ht
      exact ⟨port, phase, hr, by
        rcases hv with rfl | rfl | rfl <;> simp [safe, flipAt_flipAt]⟩
  exact stepN_covered_of_progress boundary safe hprogress (Or.inl rfl) d

/-- **Mutual theta intersection: absolute three-phase law.**  If each
support touches the other's switch, the walk from `(g, state)` is live
forever and visits at most three tongue vectors, ever. -/
theorem manufactured_two_sided_theta_all_time_three_phase
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
  let safe := fun phase => phase ∈
    [state, flipAt state A.actionSwitch, flipAt state B.actionSwitch]
  let boundary := fun c => c = (g, state) ∨ c = (e, flipAt state A.actionSwitch) ∨
    c = (g, flipAt state B.actionSwitch) ∨ c = (e, state)
  have hprogress : ∀ start, boundary start → ∃ travel finish,
      0 < travel ∧ stepN w travel start = some finish ∧ boundary finish ∧
      ∀ t, t ≤ travel → ∃ port phase,
        stepN w t start = some (port, phase) ∧ safe phase := by
    intro start hs
    rcases hs with rfl | rfl | rfl | rfl
    · refine ⟨A.toSupported.travel, (e, flipAt state A.actionSwitch),
        (ManufacturedReflector.flip A).travel_pos, (A.toSupported.run state hA).1,
        Or.inr (Or.inl rfl), ?_⟩
      intro t ht
      obtain ⟨port, phase, hr, hp⟩ := A.travel_two_phase_stepN state hA ht
      exact ⟨port, phase, hr, by rcases hp with rfl | rfl <;> simp [safe]⟩
    · rcases manufactured_support_fault_dichotomy_pointwise A B state hA hB hAB with
        ⟨travel, hr, hp⟩ | ⟨hr, hp⟩
      · refine ⟨travel, (e, state), stepN_flip_restore_pos hr, hr,
          Or.inr (Or.inr (Or.inr rfl)), ?_⟩
        intro t ht
        obtain ⟨port, phase, ht, hv⟩ := hp t ht
        exact ⟨port, phase, ht, by rcases hv with rfl | rfl <;> simp [safe]⟩
      · refine ⟨B.toSupported.travel, (g, flipAt state B.actionSwitch),
          (ManufacturedReflector.flip B).travel_pos, hr,
          Or.inr (Or.inr (Or.inl rfl)), ?_⟩
        intro t ht
        obtain ⟨port, phase, ht, hv⟩ := hp t ht
        exact ⟨port, phase, ht, by rcases hv with rfl | rfl | rfl <;> simp [safe]⟩
    · rcases manufactured_support_fault_dichotomy_pointwise B A state hB hA hBA with
        ⟨travel, hr, hp⟩ | ⟨hr, hp⟩
      · refine ⟨travel, (g, state), stepN_flip_restore_pos hr, hr, Or.inl rfl, ?_⟩
        intro t ht
        obtain ⟨port, phase, ht, hv⟩ := hp t ht
        exact ⟨port, phase, ht, by rcases hv with rfl | rfl <;> simp [safe]⟩
      · refine ⟨A.toSupported.travel, (e, flipAt state A.actionSwitch),
          (ManufacturedReflector.flip A).travel_pos, hr, Or.inr (Or.inl rfl), ?_⟩
        intro t ht
        obtain ⟨port, phase, ht, hv⟩ := hp t ht
        exact ⟨port, phase, ht, by rcases hv with rfl | rfl | rfl <;> simp [safe]⟩
    · refine ⟨B.toSupported.travel, (g, flipAt state B.actionSwitch),
        (ManufacturedReflector.flip B).travel_pos, (B.toSupported.run state hB).1,
        Or.inr (Or.inr (Or.inl rfl)), ?_⟩
      intro t ht
      obtain ⟨port, phase, hr, hp⟩ := B.travel_two_phase_stepN state hB ht
      exact ⟨port, phase, hr, by rcases hp with rfl | rfl <;> simp [safe]⟩
  exact stepN_covered_of_progress boundary safe hprogress (Or.inl rfl) d

end

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

end GeneralN
