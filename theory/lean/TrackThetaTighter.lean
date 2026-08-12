import TrackThetaCaptureTighter

/-!
# Tighter theta and reflector-pair accounting

A theta half now costs at most `6*N+1`.  Two halves therefore fit in
`12*N+2`.  The only generic reflector-pair case needing an extra prefix adds
one reflector traversal (`<= 2*N`), yielding `14*N+2`.
-/

namespace GeneralN

/-- One-sided flip/flip theta intersection closes within `12*N+2`. -/
theorem manufactured_one_sided_theta_within_twelve_succ_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedFlipReflector w g e)
    (B : ManufacturedFlipReflector w e g)
    (state : Tongues)
    (hA : PathGrooves [A.runway, A.candy] state)
    (hB : PathGrooves [B.runway, B.candy] state)
    (hcontact : ∃ path ∈ [B.runway, B.candy],
      ∃ passage ∈ path,
        passageSwitch passage = A.actionSwitch)
    (hBA : (LocalAction.flip B.actionSwitch).Avoids
      [A.runway, A.candy]) :
    EventuallyPeriodicWithin w (g, state) (12 * N + 2) := by
  obtain ⟨firstTravel, hfirstPos, hfirstLe, hfirst⟩ :=
    manufactured_theta_half_within_six_succ
      hN A B state hA hB hcontact
  have hA' : PathGrooves [A.runway, A.candy]
      (flipAt state B.actionSwitch) :=
    hA.after_avoiding_action hBA
  have hB' : PathGrooves [B.runway, B.candy]
      (flipAt state B.actionSwitch) :=
    (B.toSupported.run state hB).2
  obtain ⟨secondTravel, hsecondPos, hsecondLe, hsecond⟩ :=
    manufactured_theta_half_within_six_succ hN A B
      (flipAt state B.actionSwitch) hA' hB' hcontact
  have hperiod : stepN w (firstTravel + secondTravel) (g, state) =
      some (g, state) := by
    rw [stepN_add, hfirst]
    simp only [Option.bind_some]
    rw [hsecond, flipAt_flipAt]
  exact eventuallyPeriodicWithin_of_period
    (by omega) (by omega) hperiod

/-- Mutual flip/flip theta intersection closes within `12*N+2`. -/
theorem manufactured_two_sided_theta_within_twelve_succ_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
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
        passageSwitch passage = B.actionSwitch) :
    EventuallyPeriodicWithin w (g, state) (12 * N + 2) := by
  obtain ⟨lead, hleadPos, hleadLe, hlead⟩ :=
    manufactured_theta_half_within_six_succ
      hN A B state hA hB hAB
  have hAt : A.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_le_two_mul_switches hN
  have hBt : B.toSupported.travel ≤ 2 * N := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip B).travel_le_two_mul_switches hN
  have hApos : 0 < A.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip A).travel_pos
  have hBpos : 0 < B.toSupported.travel := by
    simpa [ManufacturedReflector.toSupported] using
      (ManufacturedReflector.flip B).travel_pos
  have hreverseFault :=
    manufactured_support_fault_dichotomy_within_two_succ
      hN B A state hB hA hBA
  have hforwardFault :=
    manufactured_support_fault_dichotomy_within_two_succ
      hN A B state hA hB hAB
  have hBrun := (B.toSupported.run state hB).1
  change stepN w B.toSupported.travel (e, state) =
    some (g, flipAt state B.actionSwitch) at hBrun
  rcases hreverseFault with hreverseCapture | hreverseRepair
  · obtain ⟨reverseTravel, hreverseLe, hreverseCapture⟩ :=
      hreverseCapture
    have hperiod : stepN w (lead + reverseTravel) (g, state) =
        some (g, state) := by
      rw [stepN_add, hlead]
      exact hreverseCapture
    exact eventuallyPeriodicWithin_of_period
      (period := lead + reverseTravel)
      (by omega) (by omega) hperiod
  · rcases hforwardFault with hforwardCapture | hforwardRepair
    · obtain ⟨forwardTravel, hforwardLe, hforwardCapture⟩ :=
        hforwardCapture
      let period := A.toSupported.travel + forwardTravel +
        B.toSupported.travel
      have hperiod : stepN w period
          (g, flipAt state B.actionSwitch) =
            some (g, flipAt state B.actionSwitch) := by
        have hlen : period = A.toSupported.travel +
            (forwardTravel + B.toSupported.travel) := by
          dsimp [period]
          omega
        rw [hlen, stepN_add, hreverseRepair]
        simp only [Option.bind_some]
        rw [stepN_add, hforwardCapture]
        exact hBrun
      exact ⟨lead, period,
        (g, flipAt state B.actionSwitch), by
          dsimp [period]
          omega
        , by
          dsimp [period]
          omega
        , hlead, hperiod⟩
    · let period := A.toSupported.travel + B.toSupported.travel
      have hperiod : stepN w period
          (g, flipAt state B.actionSwitch) =
            some (g, flipAt state B.actionSwitch) := by
        dsimp [period]
        rw [stepN_add, hreverseRepair]
        exact hforwardRepair
      exact ⟨lead, period,
        (g, flipAt state B.actionSwitch), by
          dsimp [period]
          omega
        , by
          dsimp [period]
          omega
        , hlead, hperiod⟩

end GeneralN
