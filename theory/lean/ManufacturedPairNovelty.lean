import TrackNoveltyCover

/-!
# Pointwise novelty of manufactured reflector pairs

This file strengthens the endpoint-only reflector API for the concrete
reflectors manufactured by a first repeated switch.  A complete traversal
has exactly two tongue phases: the incoming state on the selected outward
route, and the local-action state after the far-arm contact and throughout
the reverse runway.

The eventual goal is a four-vector cover for a compatible opposite pair.
Nothing in this file asserts the still-open global `StateLaw`.
-/

namespace GeneralN

/-- Every prefix of a live finite run is itself live. -/
theorem stepN_prefix_some
    {w : Wiring} {start finish : Nat × Tongues} {d K : Nat}
    (hd : d ≤ K) (hfinish : stepN w K start = some finish) :
    ∃ middle, stepN w d start = some middle := by
  let rest := K - d
  have hsplit : K = d + rest := by
    dsimp [rest]
    omega
  rw [hsplit, stepN_add] at hfinish
  cases hprefix : stepN w d start with
  | none => simp [hprefix] at hfinish
  | some middle => exact ⟨middle, rfl⟩

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
  | flip R =>
      change PathGrooves [R.runway, R.candy] state at hpaths
      by_cases hselected :
          state R.actionSwitch = bval R.firstArm
      · have hsecondValue :
            bval R.secondArm = !(state R.actionSwitch) := by
          rw [hselected]
          exact branch_values_opposite R.firstArm_branch
            R.secondArm_branch
            (R.firstArm_switch.trans R.secondArm_switch.symm)
            R.arms_ne
        have hpin :
            pin state R.secondArm = flipAt state R.actionSwitch :=
          pin_eq_flipAt R.secondArm_switch hsecondValue
        have hstem : 3 * (R.secondArm / 3) = R.mouth := by
          have hm := R.mouth_is_stem
          have hs := R.secondArm_switch
          unfold ManufacturedFlipReflector.actionSwitch at hs
          omega
        simp [ManufacturedReflector.orientedFinish, hselected,
          ManufacturedReflector.mouthConfig,
          ManufacturedReflector.toSupported,
          ManufacturedFlipReflector.toSupported,
          LocalAction.apply, arrive, R.secondArm_branch, hstem, hpin]
      · have hsecondSelected :
            state R.actionSwitch = bval R.secondArm := by
          rcases R.selected_arm state with hfirst | hsecond
          · exact absurd hfirst hselected
          · exact hsecond
        have hfirstValue :
            bval R.firstArm = !(state R.actionSwitch) := by
          rw [hsecondSelected]
          have hopp := branch_values_opposite R.firstArm_branch
            R.secondArm_branch
            (R.firstArm_switch.trans R.secondArm_switch.symm)
            R.arms_ne
          cases hb : bval R.firstArm <;>
            cases hq : bval R.secondArm <;> simp_all
        have hpin :
            pin state R.firstArm = flipAt state R.actionSwitch :=
          pin_eq_flipAt R.firstArm_switch hfirstValue
        have hstem : 3 * (R.firstArm / 3) = R.mouth := by
          have hm := R.mouth_is_stem
          have hs := R.firstArm_switch
          unfold ManufacturedFlipReflector.actionSwitch at hs
          omega
        simp [ManufacturedReflector.orientedFinish, hselected,
          ManufacturedReflector.mouthConfig,
          ManufacturedReflector.toSupported,
          ManufacturedFlipReflector.toSupported,
          LocalAction.apply, arrive, R.firstArm_branch, hstem, hpin]

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

/-- **Four-phase law for a compatible opposite pair.**

During two complete round trips, every tongue vector is one of the four
commuting-involution corners generated by the two local reflector actions.
This is pointwise and uses the raw `stepN` dynamics, not merely the endpoint
period theorem. -/
theorem manufactured_pair_four_phase_tongues
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {d : Nat}
    (hd : d ≤ 2 * (A.toSupported.travel + B.toSupported.travel)) :
    tonguesAt w (g, state) d ∈
      [state,
       A.toSupported.action.apply state,
       B.toSupported.action.apply (A.toSupported.action.apply state),
       A.toSupported.action.apply
         (B.toSupported.action.apply
           (A.toSupported.action.apply state))] := by
  let aState := A.toSupported.action.apply state
  let baState := B.toSupported.action.apply aState
  let abaState := A.toSupported.action.apply baState
  have hA1 : stepN w A.toSupported.travel (g, state) =
      some (e, aState) := by
    exact (A.toSupported.run state hA).1
  have hBAtA : PathGrooves B.toSupported.paths aState := by
    exact hB.after_avoiding_action hAB
  have hB1 : stepN w B.toSupported.travel (e, aState) =
      some (g, baState) := by
    exact (B.toSupported.run aState hBAtA).1
  have hABrun :
      stepN w (A.toSupported.travel + B.toSupported.travel)
        (g, state) = some (g, baState) := by
    rw [stepN_add, hA1]
    exact hB1
  have hAAtBA : PathGrooves A.toSupported.paths baState := by
    have hAfterA : PathGrooves A.toSupported.paths aState :=
      hA.after_avoiding_action A.action_avoids_own_support
    exact hAfterA.after_avoiding_action hBA
  have hA2 : stepN w A.toSupported.travel (g, baState) =
      some (e, abaState) := by
    exact (A.toSupported.run baState hAAtBA).1
  have hABArun :
      stepN w
        ((A.toSupported.travel + B.toSupported.travel) +
          A.toSupported.travel) (g, state) = some (e, abaState) := by
    rw [stepN_add, hABrun]
    exact hA2
  have hBAtABA : PathGrooves B.toSupported.paths abaState := by
    have hAfterA : PathGrooves B.toSupported.paths aState :=
      hB.after_avoiding_action hAB
    have hAfterAB : PathGrooves B.toSupported.paths baState :=
      hAfterA.after_avoiding_action B.action_avoids_own_support
    exact hAfterAB.after_avoiding_action hAB
  have hrestore : B.toSupported.action.apply abaState = state := by
    dsimp [aState, baState, abaState]
    rw [A.toSupported.action.commute B.toSupported.action
      (A.toSupported.action.apply state)]
    rw [A.toSupported.action.involutive]
    exact B.toSupported.action.involutive state
  by_cases hFirstA : d ≤ A.toSupported.travel
  · rcases A.travel_two_phase_tongues state hA hFirstA with hu | hAu
    · simp [hu]
    · simp [hAu]
  · by_cases hFirstB :
        d ≤ A.toSupported.travel + B.toSupported.travel
    · let q := d - A.toSupported.travel
      have hq : q ≤ B.toSupported.travel := by
        dsimp [q]
        omega
      have hdq : d = A.toSupported.travel + q := by
        dsimp [q]
        omega
      rcases B.travel_two_phase_tongues aState hBAtA hq with
          hAState | hBAState
      · have hlive := stepN_prefix_some hq hB1
        have hshift := tonguesAt_add_of_reaches (d := q) hA1 hlive
        rw [← hdq] at hshift
        simp [hshift, hAState, aState]
      · have hlive := stepN_prefix_some hq hB1
        have hshift := tonguesAt_add_of_reaches (d := q) hA1 hlive
        rw [← hdq] at hshift
        simp [hshift, hBAState, aState]
    · by_cases hSecondA :
          d ≤ (A.toSupported.travel + B.toSupported.travel) +
            A.toSupported.travel
      · let q := d -
          (A.toSupported.travel + B.toSupported.travel)
        have hq : q ≤ A.toSupported.travel := by
          dsimp [q]
          omega
        have hdq : d =
            (A.toSupported.travel + B.toSupported.travel) + q := by
          dsimp [q]
          omega
        rcases A.travel_two_phase_tongues baState hAAtBA hq with
            hBAState | hABAState
        · have hlive := stepN_prefix_some hq hA2
          have hshift := tonguesAt_add_of_reaches (d := q) hABrun hlive
          rw [← hdq] at hshift
          simp [hshift, hBAState, aState, baState]
        · have hlive := stepN_prefix_some hq hA2
          have hshift := tonguesAt_add_of_reaches (d := q) hABrun hlive
          rw [← hdq] at hshift
          simp [hshift, hABAState, aState, baState]
      · let q := d -
          ((A.toSupported.travel + B.toSupported.travel) +
            A.toSupported.travel)
        have hq : q ≤ B.toSupported.travel := by
          dsimp [q]
          omega
        have hdq : d =
            ((A.toSupported.travel + B.toSupported.travel) +
              A.toSupported.travel) + q := by
          dsimp [q]
          omega
        rcases B.travel_two_phase_tongues abaState hBAtABA hq with
            hABAState | hFinal
        · have hB2 : stepN w B.toSupported.travel (e, abaState) =
              some (g, state) := by
            have hrun := (B.toSupported.run abaState hBAtABA).1
            rw [hrestore] at hrun
            exact hrun
          have hlive := stepN_prefix_some hq hB2
          have hshift := tonguesAt_add_of_reaches (d := q) hABArun hlive
          rw [← hdq] at hshift
          simp [hshift, hABAState, aState, baState, abaState]
        · have hB2 : stepN w B.toSupported.travel (e, abaState) =
              some (g, state) := by
            have hrun := (B.toSupported.run abaState hBAtABA).1
            rw [hrestore] at hrun
            exact hrun
          have hlive := stepN_prefix_some hq hB2
          have hshift := tonguesAt_add_of_reaches (d := q) hABArun hlive
          rw [← hdq] at hshift
          have hfinalState : tonguesAt w (g, state) d = state := by
            rw [hshift, hFinal, hrestore]
          simp [hfinalState]

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

/-- The four-phase law holds at every future time, not only in the first
period window. -/
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
         (B.toSupported.action.apply
           (A.toSupported.action.apply state))] := by
  let period := 2 * (A.toSupported.travel + B.toSupported.travel)
  have hpos : 0 < period := by
    have hAp := A.travel_pos
    have hBp := B.travel_pos
    dsimp [period]
    omega
  have hperiod : stepN w period (g, state) = some (g, state) := by
    dsimp [period]
    exact A.toSupported.paired_period B.toSupported
      hAB hBA state hA hB
  let q := d / period
  let r := d % period
  have hr : r < period := by
    dsimp [r]
    exact Nat.mod_lt d hpos
  have hdEq : d = q * period + r := by
    dsimp [q, r]
    have hdiv := Nat.div_add_mod d period
    rw [Nat.mul_comm period (d / period)] at hdiv
    omega
  have hsame : tonguesAt w (g, state) d =
      tonguesAt w (g, state) r := by
    have hrun : stepN w d (g, state) =
        stepN w r (g, state) := by
      rw [hdEq, stepN_add,
        stepN_mul_period_pair_novelty hperiod q]
      simp
    simp [tonguesAt, hrun]
  rw [hsame]
  exact manufactured_pair_four_phase_tongues
    A B state hA hB hAB hBA (Nat.le_of_lt hr)

end GeneralN
