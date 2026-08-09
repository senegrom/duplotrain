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

/-- Any two opposite manufactured reflectors with both supports grooved have
a lasso of size at most `14*N+2`. -/
theorem manufactured_pair_within_fourteen_succ_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state) :
    EventuallyPeriodicWithin w (g, state) (14 * N + 2) := by
  classical
  cases A with
  | stay SA =>
      cases B with
      | stay SB =>
          exact (manufactured_pair_within_eight_mul_switches_of_avoids
            hN (.stay SA) (.stay SB) state hA hB
              (by trivial) (by trivial)).weaken (by omega)
      | flip FB =>
          change PathGrooves
            [SA.runway, [(SA.mouth, SA.arm)]] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
              [SA.runway, [(SA.mouth, SA.arm)]]
          · exact (manufactured_pair_within_eight_mul_switches_of_avoids
              hN (.stay SA) (.flip FB) state hA hB
                (by trivial) hBA).weaken (by omega)
          · have hcontact := contact_of_not_avoids_flip hBA
            have hlead := (SA.toSupported.run state hA).1
            change stepN w SA.toSupported.travel (g, state) =
              some (e, state) at hlead
            have hlocal := manufactured_flip_then_stay_within_eight
              hN FB SA state hB hA hcontact
            have htravel : SA.toSupported.travel ≤ 2 * N := by
              simpa [ManufacturedReflector.toSupported] using
                (ManufacturedReflector.stay SA).travel_le_two_mul_switches hN
            exact (hlocal.prepend hlead).weaken (by omega)
  | flip FA =>
      cases B with
      | stay SB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves
            [SB.runway, [(SB.mouth, SB.arm)]] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [SB.runway, [(SB.mouth, SB.arm)]]
          · exact (manufactured_pair_within_eight_mul_switches_of_avoids
              hN (.flip FA) (.stay SB) state hA hB
                hAB (by trivial)).weaken (by omega)
          · have hcontact := contact_of_not_avoids_flip hAB
            exact (manufactured_flip_then_stay_within_eight
              hN FA SB state hA hB hcontact).weaken (by omega)
      | flip FB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [FB.runway, FB.candy]
          · by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · exact (manufactured_pair_within_eight_mul_switches_of_avoids
                hN (.flip FA) (.flip FB) state hA hB hAB hBA).weaken
                  (by omega)
            · have hcontactBA := contact_of_not_avoids_flip hBA
              have hArun := (FA.toSupported.run state hA)
              have hA' : PathGrooves [FA.runway, FA.candy]
                  (flipAt state FA.actionSwitch) := hArun.2
              have hB' : PathGrooves [FB.runway, FB.candy]
                  (flipAt state FA.actionSwitch) :=
                hB.after_avoiding_action hAB
              have hlocal :=
                manufactured_one_sided_theta_within_twelve_succ_two
                  hN FB FA (flipAt state FA.actionSwitch)
                    hB' hA' hcontactBA hAB
              have hlead := hArun.1
              change stepN w FA.toSupported.travel (g, state) =
                some (e, flipAt state FA.actionSwitch) at hlead
              have htravel : FA.toSupported.travel ≤ 2 * N := by
                simpa [ManufacturedReflector.toSupported] using
                  (ManufacturedReflector.flip FA).travel_le_two_mul_switches hN
              exact (hlocal.prepend hlead).weaken (by omega)
          · have hcontactAB := contact_of_not_avoids_flip hAB
            by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
                [FA.runway, FA.candy]
            · exact (manufactured_one_sided_theta_within_twelve_succ_two
                hN FA FB state hA hB hcontactAB hBA).weaken (by omega)
            · have hcontactBA := contact_of_not_avoids_flip hBA
              exact (manufactured_two_sided_theta_within_twelve_succ_two
                hN FA FB state hA hB hcontactAB hcontactBA).weaken
                  (by omega)

end GeneralN
