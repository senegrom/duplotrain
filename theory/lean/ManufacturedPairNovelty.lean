import TrackNoveltyCover

/-!
# Pointwise novelty of manufactured reflector pairs

This file strengthens the endpoint-only reflector API for the concrete
reflectors manufactured by a first repeated switch.  A complete traversal
has exactly two tongue phases: the incoming state on the selected outward
route, and the local-action state after the far-arm contact and throughout
the reverse runway.

The two local actions close a four-vector invariant for an avoiding opposite
pair. Positive-length traversals then give the all-time cover directly.
-/

namespace GeneralN

/-- Reaching a configuration shifts `tonguesAt` by the travel time whenever
the queried suffix is live (so the two `getD` defaults are irrelevant). -/
theorem tonguesAt_add_of_reaches
    {w : Wiring} {start middle : Nat × Tongues} {K d : Nat}
    (hreach : stepN w K start = some middle)
    (hlive : ∃ finish, stepN w d middle = some finish) :
    tonguesAt w start (K + d) = tonguesAt w middle d := by
  obtain ⟨finish, hfinish⟩ := hlive
  simp [tonguesAt, stepN_add, hreach, hfinish]

/-- A manufactured reflector's local action avoids every switch in its own
retained groove support. -/
theorem ManufacturedReflector.action_avoids_own_support
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.toSupported.action.Avoids A.toSupported.paths := by
  cases A with
  | stay R => trivial
  | flip R => exact R.support_foreign

/-- Rebase the retained runway to any state which grooves the support. -/
theorem ManufacturedReflector.runway_trace_at
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state) :
    PhysicalTrace w (g, state) A.runway (A.mouthConfig.1, state) := by
  cases A with
  | stay R =>
      exact R.runway_trace state
        (pathGrooves_pair.mp hpaths).1
  | flip R =>
      exact R.runway_trace state
        (pathGrooves_pair.mp hpaths).1

/-- The selected far arm enters the reflector mouth and performs precisely
the advertised local action. -/
theorem ManufacturedReflector.orientedFinish_arrive
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state) :
    arrive state (A.orientedFinish state) =
      (A.mouthConfig.1, A.toSupported.action.apply state) := by
  cases A with
  | stay R =>
      change arrive state R.arm = (R.mouth, state)
      exact passagesGrooved_singleton.mp
        (pathGrooves_pair.mp hpaths).2
  | flip R => exact R.oriented_finish_arrive state

/-- Concrete travel splits into the selected no-change route, one contact,
and the reverse runway. -/
theorem ManufacturedReflector.travel_eq_oriented_add
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues) :
    A.toSupported.travel =
      (A.orientedRoute state).length + (A.runway.length + 1) := by
  cases A with
  | stay R =>
      simp [ManufacturedReflector.toSupported,
        ManufacturedStayReflector.toSupported,
        ManufacturedReflector.orientedRoute,
        ManufacturedReflector.runway]
      omega
  | flip R =>
      by_cases hselected :
          state R.actionSwitch = bval R.firstArm
      · simp [ManufacturedReflector.toSupported,
          ManufacturedFlipReflector.toSupported,
          ManufacturedReflector.orientedRoute,
          ManufacturedReflector.runway, hselected]
        omega
      · simp [ManufacturedReflector.toSupported,
          ManufacturedFlipReflector.toSupported,
          ManufacturedReflector.orientedRoute,
          ManufacturedReflector.runway, hselected,
          reversePassages_length]
        omega

/-- **Exact two-phase law for a concrete manufactured reflector.**

At every time through a complete traversal, the full tongue vector is either
the incoming vector or the vector obtained by the reflector's one local
action.  The length of the runway and candy is irrelevant. -/
theorem ManufacturedReflector.travel_two_phase_tongues
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    {d : Nat} (hd : d ≤ A.toSupported.travel) :
    tonguesAt w (g, state) d = state ∨
      tonguesAt w (g, state) d = A.toSupported.action.apply state := by
  by_cases hroute : d ≤ (A.orientedRoute state).length
  · have htrace := A.orientedRoute_trace state hpaths
    have hgrooved :
        PassagesGrooved state (A.orientedRoute state) :=
      htrace.grooved_of_switchSimple (A.orientedRoute_simple state)
    obtain ⟨port, hrun⟩ :=
      htrace.grooved_prefix_tongues state hgrooved hroute
    left
    simp [tonguesAt, hrun]
  · let tailDepth := d - (A.orientedRoute state).length
    have htailPos : 1 ≤ tailDepth := by
      dsimp [tailDepth]
      omega
    have hsplit :
        d = (A.orientedRoute state).length + tailDepth := by
      dsimp [tailDepth]
      omega
    have htailBound : tailDepth ≤ A.runway.length + 1 := by
      have htravel := A.travel_eq_oriented_add state
      dsimp [tailDepth]
      omega
    have hpathsAfter :
        PathGrooves A.toSupported.paths
          (A.toSupported.action.apply state) :=
      hpaths.after_avoiding_action A.action_avoids_own_support
    have hrunwayAfter :
        PassagesGrooved (A.toSupported.action.apply state) A.runway :=
      hpathsAfter A.runway A.runway_mem_support
    have hrecorded := A.runway_trace_at state hpaths
    have hcontact := A.orientedFinish_arrive state hpaths
    obtain ⟨port, htail⟩ :=
      physicalTrace_contact_retraces_prefix_positive
        hrecorded hrunwayAfter A.entryEdge hcontact
        htailPos htailBound
    have hlead := (A.orientedRoute_trace state hpaths).sound
    have hrun : stepN w d (g, state) =
        some (port, A.toSupported.action.apply state) := by
      rw [hsplit, stepN_add, hlead]
      exact htail
    right
    simp [tonguesAt, hrun]

/-- A manufactured traversal has only its incoming and outgoing vectors. -/
theorem ManufacturedReflector.travel_two_phase_stepN
    {w : Wiring} {g e : Nat} (B : ManufacturedReflector w g e)
    (state : Tongues) (hB : PathGrooves B.toSupported.paths state)
    {d : Nat} (hd : d ≤ B.toSupported.travel) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      (phase = state ∨ phase = B.toSupported.action.apply state) := by
  obtain ⟨⟨port, phase⟩, hrun⟩ := stepN_prefix_some hd (B.toSupported.run state hB).1
  have hphase := B.travel_two_phase_tongues state hB hd
  exact ⟨port, phase, hrun, by simpa [tonguesAt, hrun] using hphase⟩

/-- Entering a manufactured flip reflector at its mouth with the action
tongue already flipped exposes only the flipped vector and the restored base
vector.  This is the pointwise strengthening of `capture_from_mouth`. -/
theorem ManufacturedFlipReflector.capture_from_mouth_two_phase
    {w : Wiring} {g e : Nat}
    (C : ManufacturedFlipReflector w g e)
    (state : Tongues)
    (hrunway : PassagesGrooved state C.runway)
    (hcandy : PassagesGrooved state C.candy)
    {d : Nat}
    (hd : d <= C.candy.length + 2 + C.runway.length) :
    exists port phase,
      stepN w d (C.mouth, flipAt state C.actionSwitch) =
          some (port, phase) /\
        (phase = flipAt state C.actionSwitch \/ phase = state) := by
  let A := ManufacturedReflector.flip C
  have hpaths : PathGrooves A.toSupported.paths state :=
    pathGrooves_pair.mpr ⟨hrunway, hcandy⟩
  have hflipped := hpaths.after_avoiding_action A.action_avoids_own_support
  have hrunwayFlip : PassagesGrooved (flipAt state C.actionSwitch) C.runway :=
    (pathGrooves_pair.mp hflipped).1
  have hle : C.runway.length + d ≤ A.toSupported.travel := by
    change C.runway.length + d ≤ 2 * C.runway.length + C.candy.length + 2
    omega
  obtain ⟨⟨port, phase⟩, hr⟩ := stepN_prefix_some hle (A.toSupported.run _ hflipped).1
  change stepN w (C.runway.length + d) (g, flipAt state C.actionSwitch) =
    some (port, phase) at hr
  have hp := A.travel_two_phase_tongues _ hflipped hle
  have hphase : phase = flipAt state C.actionSwitch ∨ phase = state := by
    change tonguesAt w (g, flipAt state C.actionSwitch) (C.runway.length + d) =
      flipAt state C.actionSwitch ∨
      tonguesAt w (g, flipAt state C.actionSwitch) (C.runway.length + d) =
        flipAt (flipAt state C.actionSwitch) C.actionSwitch at hp
    simpa [tonguesAt, hr, flipAt_flipAt] using hp
  have hreach : stepN w C.runway.length (g, flipAt state C.actionSwitch) =
      some (C.mouth, flipAt state C.actionSwitch) := (C.runway_trace _ hrunwayFlip).sound
  rw [stepN_add, hreach] at hr
  exact ⟨port, phase, hr, hphase⟩


/-- Repeat a closed raw-track period any number of times. -/
theorem stepN_mul_period_pair_novelty
    {w : Wiring} {start : Nat × Tongues} {period : Nat}
    (hperiod : stepN w period start = some start) :
    ∀ q, stepN w (q * period) start = some start := by
  intro q
  induction q with
  | zero => simp [stepN]
  | succ q ih =>
      have hlen : (q + 1) * period = q * period + period := by
        simp [Nat.add_mul]
      rw [hlen, stepN_add, ih]
      exact hperiod

/-- The two local actions preserve their four-corner orbit and both groove
supports. Alternate positive-length traversals inside that invariant; there
is no need to calculate a four-leg time window or reduce time modulo a period. -/
theorem SupportedReflector.pair_all_time_four_phase
    {w : Wiring} {g e : Nat}
    (A : SupportedReflector w g e)
    (B : SupportedReflector w e g)
    (hApos : 0 < A.travel) (hBpos : 0 < B.travel)
    (hAtwo : ∀ state, PathGrooves A.paths state → ∀ d, d ≤ A.travel →
      ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
        (phase = state ∨ phase = A.action.apply state))
    (hBtwo : ∀ state, PathGrooves B.paths state → ∀ d, d ≤ B.travel →
      ∃ port phase, stepN w d (e, state) = some (port, phase) ∧
        (phase = state ∨ phase = B.action.apply state))
    (state : Tongues)
    (hA : PathGrooves A.paths state)
    (hB : PathGrooves B.paths state)
    (hAB : A.action.Avoids B.paths)
    (hBA : B.action.Avoids A.paths)
    (d : Nat) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
    phase ∈
      [state,
       A.action.apply state,
       B.action.apply (A.action.apply state),
       A.action.apply
         (B.action.apply (A.action.apply state))] := by
  let a := A.action
  let b := B.action
  let safe := fun u => u ∈ [state, a.apply state, b.apply (a.apply state), b.apply state]
  have hfour : a.apply (b.apply (a.apply state)) = b.apply state := by
    rw [a.commute b, a.involutive]
  have hsafeA : ∀ u, safe u → safe (a.apply u) := by
    intro u hu
    simp only [safe, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;>
      simp [safe, a.involutive, hfour, a.commute b]
  have hsafeB : ∀ u, safe u → safe (b.apply u) := by
    intro u hu
    simp only [safe, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> simp [safe, b.involutive]
  let boundary := fun c : Nat × Tongues =>
    (c.1 = g ∨ c.1 = e) ∧ safe c.2 ∧
      PathGrooves A.paths c.2 ∧ PathGrooves B.paths c.2
  have hprogress : ∀ start, boundary start → ∃ travel finish,
      0 < travel ∧ stepN w travel start = some finish ∧ boundary finish ∧
      ∀ t, t ≤ travel → ∃ port phase,
        stepN w t start = some (port, phase) ∧ safe phase := by
    intro ⟨p, u⟩ ⟨hp, hu, huA, huB⟩
    dsimp only at hp hu huA huB
    rcases hp with hp | hp
    · subst p
      refine ⟨A.travel, (e, a.apply u), hApos,
        (A.run u huA).1,
        ⟨Or.inr rfl, hsafeA u hu,
          (A.run u huA).2,
          huB.after_avoiding_action hAB⟩, ?_⟩
      intro t ht
      obtain ⟨port, phase, hr, hv⟩ := hAtwo u huA t ht
      exact ⟨port, phase, hr, hv.elim (fun h => h.symm ▸ hu) (fun h => h.symm ▸ hsafeA u hu)⟩
    · subst p
      refine ⟨B.travel, (g, b.apply u), hBpos,
        (B.run u huB).1,
        ⟨Or.inl rfl, hsafeB u hu, huA.after_avoiding_action hBA,
          (B.run u huB).2⟩, ?_⟩
      intro t ht
      obtain ⟨port, phase, hr, hv⟩ := hBtwo u huB t ht
      exact ⟨port, phase, hr, hv.elim (fun h => h.symm ▸ hu) (fun h => h.symm ▸ hsafeB u hu)⟩
  obtain ⟨port, phase, hr, hs⟩ := stepN_covered_of_progress boundary safe hprogress
    (start := (g, state)) ⟨Or.inl rfl, by simp [safe], hA, hB⟩ d
  refine ⟨port, phase, hr, ?_⟩
  change phase ∈ [state, a.apply state, b.apply (a.apply state),
    a.apply (b.apply (a.apply state))]
  simpa only [hfour] using hs

/-- Manufactured reflectors supply the abstract pair law with their two-phase traversals. -/
theorem manufactured_pair_all_time_four_phase_tongues
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (d : Nat) :
    tonguesAt w (g, state) d ∈
      [state,
       A.toSupported.action.apply state,
       B.toSupported.action.apply (A.toSupported.action.apply state),
       A.toSupported.action.apply
         (B.toSupported.action.apply (A.toSupported.action.apply state))] := by
  obtain ⟨port, phase, hr, hs⟩ := A.toSupported.pair_all_time_four_phase B.toSupported
    A.travel_pos B.travel_pos
    (fun u hu _ ht => A.travel_two_phase_stepN u hu ht)
    (fun u hu _ ht => B.travel_two_phase_stepN u hu ht)
    state hA hB hAB hBA d
  simpa [tonguesAt, hr] using hs

end GeneralN
