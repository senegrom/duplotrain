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
  change stepN w A.toSupported.travel (g, state) =
    some (e, flipAt state A.actionSwitch) at hArun
  have hpos : 0 < A.toSupported.travel := (ManufacturedReflector.flip A).travel_pos
  have hAcover : ∀ d, d ≤ A.toSupported.travel → ∃ port phase,
      stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = flipAt state A.actionSwitch ∨
          phase = flipAt state B.actionSwitch) := by
    intro d hd
    obtain ⟨port, phase, hr, hp⟩ := A.travel_two_phase_stepN state hA hd
    exact ⟨port, phase, hr, by grind⟩
  rcases manufactured_support_fault_dichotomy_pointwise
      A B state hA hB hcontact with ⟨cap, hc, hp⟩ | ⟨hr, hp⟩
  · have hBrun := (B.toSupported.run state hB).1
    change stepN w B.toSupported.travel (e, state) =
      some (g, flipAt state B.actionSwitch) at hBrun
    refine ⟨A.toSupported.travel + (cap + B.toSupported.travel), by omega, ?_, ?_⟩
    · simp only [stepN_add, hArun, hc, Option.bind_some]; exact hBrun
    · apply stepN_cover_append hArun hAcover
      apply stepN_cover_append hc
      · intro d hd
        obtain ⟨port, phase, hr, hv⟩ := hp d hd
        exact ⟨port, phase, hr, by grind⟩
      · intro d hd
        obtain ⟨port, phase, hr, hv⟩ := B.travel_two_phase_stepN state hB hd
        exact ⟨port, phase, hr, by grind⟩
  · refine ⟨A.toSupported.travel + B.toSupported.travel, by omega, ?_, ?_⟩
    · rw [stepN_add, hArun]; exact hr
    · apply stepN_cover_append hArun hAcover
      intro d hd
      obtain ⟨port, phase, hr, hv⟩ := hp d hd
      exact ⟨port, phase, hr, by grind⟩


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
  by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids [FB.runway, FB.candy]
  · by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids [FA.runway, FA.candy]
    · obtain ⟨port, phase, hr, hm⟩ := FA.toSupported.pair_all_time_four_phase FB.toSupported
        (ManufacturedReflector.flip FA).travel_pos (ManufacturedReflector.flip FB).travel_pos
        (fun u hu _ ht => FA.travel_two_phase_stepN u hu ht)
        (fun u hu _ ht => FB.travel_two_phase_stepN u hu ht)
        state hA hB hAB hBA d
      have hcancel : flipAt (flipAt (flipAt state FA.actionSwitch) FB.actionSwitch)
          FA.actionSwitch = flipAt state FB.actionSwitch := by
        simpa only [LocalAction.apply, flipAt_flipAt] using
          (LocalAction.flip FA.actionSwitch).commute (.flip FB.actionSwitch)
            (flipAt state FA.actionSwitch)
      change phase ∈ [state, flipAt state FA.actionSwitch,
        flipAt (flipAt state FA.actionSwitch) FB.actionSwitch,
        flipAt (flipAt (flipAt state FA.actionSwitch) FB.actionSwitch) FA.actionSwitch] at hm
      exact ⟨port, phase, hr, by rw [hcancel] at hm; grind⟩
    · have htail := manufactured_one_sided_theta_all_time_four_phase FB FA
        (flipAt state FA.actionSwitch) (hB.after_avoiding_action hAB)
        (FA.toSupported.run state hA).2 (contact_of_not_avoids_flip hBA) hAB
      apply stepN_cover_append (right := d) (FA.toSupported.run state hA).1 ?_ ?_ d (by omega)
      · intro t ht
        obtain ⟨port, phase, hr, hp⟩ := FA.travel_two_phase_stepN state hA ht
        exact ⟨port, phase, hr, by grind⟩
      · intro t _
        obtain ⟨port, phase, hr, hp⟩ := htail t
        exact ⟨port, phase, hr, by simp only [flipAt_flipAt] at hp; grind⟩
  · have hcontact := contact_of_not_avoids_flip hAB
    by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids [FA.runway, FA.candy]
    · obtain ⟨port, phase, hr, hm⟩ := manufactured_one_sided_theta_all_time_four_phase
        FA FB state hA hB hcontact hBA d
      have hcomm : flipAt (flipAt state FB.actionSwitch) FA.actionSwitch =
          flipAt (flipAt state FA.actionSwitch) FB.actionSwitch :=
        (LocalAction.flip FA.actionSwitch).commute (.flip FB.actionSwitch) state
      exact ⟨port, phase, hr, by rw [hcomm] at hm; grind⟩
    · obtain ⟨port, phase, hr, hm⟩ := manufactured_two_sided_theta_all_time_three_phase
        FA FB state hA hB hcontact (contact_of_not_avoids_flip hBA) d
      exact ⟨port, phase, hr, by grind⟩

end GeneralN
