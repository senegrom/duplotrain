import TrackNoveltyCover

/-!
# Pointwise novelty of manufactured reflector pairs

This file strengthens the endpoint-only reflector API for the concrete
reflectors manufactured by a first repeated switch.  A complete traversal
has exactly two tongue phases: the incoming state on the selected outward
route, and the local-action state after the far-arm contact and throughout
the reverse runway.

These pointwise traversal laws also support changed-contact capture and
all-time boundary invariants.
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

/-- The restricted-vector form of `tonguesAt_add_of_reaches`. -/
theorem restrictedTonguesAt_add_of_reaches
    {w : Wiring} {N : Nat} {start middle : Nat × Tongues} {K d : Nat}
    (hreach : stepN w K start = some middle)
    (hlive : ∃ finish, stepN w d middle = some finish) :
    restrictedTonguesAt w N start (K + d) = restrictedTonguesAt w N middle d :=
  congrArg (VectorCount.restrict N) (tonguesAt_add_of_reaches hreach hlive)

/-- A live sample past a reached configuration is a live sample of the
suffix run. -/
theorem stepN_suffix_some_of_reaches
    {w : Wiring} {start middle : Nat × Tongues} {K d : Nat}
    (hreach : stepN w K start = some middle)
    (hlive : (stepN w (K + d) start).isSome) :
    ∃ finish, stepN w d middle = some finish := by
  simpa [stepN_add, hreach, Option.isSome_iff_exists] using hlive

/-- Shift a live phase orbit into an ambient run after a historical prefix. -/
theorem cover_of_live_phase_orbit
    {w : Wiring} {N K : Nat} {start middle : Nat × Tongues}
    {phases : List Tongues} {times : List Nat} {history fresh : List (List Bool)}
    (hreach : stepN w K start = some middle)
    (horbit : ∀ d, ∃ port phase, stepN w d middle = some (port, phase) ∧ phase ∈ phases)
    (hcover : ∀ phase ∈ phases, VectorCount.restrict N phase ∈ history ++ fresh)
    (hlead : ∀ j ∈ times, j < K → restrictedTonguesAt w N start j ∈ history) :
    ∀ j ∈ times, restrictedTonguesAt w N start j ∈ history ++ fresh := by
  intro j hj
  by_cases hjK : j < K
  · exact List.mem_append_left _ (hlead j hj hjK)
  · obtain ⟨d, rfl⟩ : ∃ d, j = K + d := ⟨j - K, by omega⟩
    obtain ⟨port, phase, hr, hs⟩ := horbit d
    simpa [restrictedTonguesAt, tonguesAt, stepN_add, hreach, hr] using hcover _ hs

/-- The recorded exploration followed by its return retrace reaches activation. -/
theorem ManufacturedReflector.manufacturing_journey_reaches_activated
    {w : Wiring} {g e : Nat} (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState) :
    stepN w (A.exploration.length + A.runway.length + 1)
      (g, A.baseState) = some (e, A.activatedState) := by
  have hreturn := physicalTrace_contact_retraces_prefix A.runway_trace
    (hpaths A.runway A.runway_mem_support) A.entryEdge A.return_arrive_mouth
  simpa [reversePassages_length, Nat.add_assoc] using (A.exploration_trace.append hreturn).sound

def ManufacturedReflector.sharpConstructionHistory
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : List (List Bool) :=
  ((List.range (A.exploration.length + 1)).map
      (restrictedTonguesAt w N (g, A.baseState))) ++
    [VectorCount.restrict N A.activatedState]

/-- Every exploration sample is recorded; every later return sample is activated. -/
theorem ManufacturedReflector.manufacturing_journey_mem_sharpHistory
    {w : Wiring} {g e N : Nat} (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    {j : Nat} (hj : j ≤ A.exploration.length + A.runway.length + 1) :
    restrictedTonguesAt w N (g, A.baseState) j ∈ A.sharpConstructionHistory N := by
  by_cases hearly : j ≤ A.exploration.length
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)
  · obtain ⟨port, hr⟩ := physicalTrace_contact_retraces_prefix_pointwise A.runway_trace
      (hpaths A.runway A.runway_mem_support) A.entryEdge A.return_arrive_mouth
      (j - A.exploration.length) (by omega)
    have hpos : j - A.exploration.length ≠ 0 := by omega
    have hrun : stepN w j (g, A.baseState) = some (port, A.activatedState) := by
      rw [show j = A.exploration.length + (j - A.exploration.length) by omega,
        stepN_add, A.exploration_trace.sound]
      simpa [hpos] using hr
    apply List.mem_append_right
    simp [restrictedTonguesAt, tonguesAt, hrun]

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
      simp [ManufacturedReflector.toSupported, ManufacturedStayReflector.toSupported,
        ManufacturedReflector.orientedRoute, ManufacturedReflector.runway]
      omega
  | flip R =>
      simp only [ManufacturedReflector.toSupported, ManufacturedFlipReflector.toSupported,
        ManufacturedReflector.orientedRoute, ManufacturedReflector.runway]
      split <;> simp [reversePassages_length] <;> omega

/-- **Exact two-phase law for a concrete manufactured reflector.**

At every time through a complete traversal, the full tongue vector is either
the incoming vector or the vector obtained by the reflector's one local
action.  The length of the runway and candy is irrelevant. -/
theorem ManufacturedReflector.travel_two_phase_stepN
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    {d : Nat} (hd : d ≤ A.toSupported.travel) :
    ∃ port phase, stepN w d (g, state) = some (port, phase) ∧
      (phase = state ∨ phase = A.toSupported.action.apply state) := by
  have htrace := A.orientedRoute_trace state hpaths
  have hg := htrace.grooved_of_switchSimple (A.orientedRoute_simple state)
  have hpathsAfter := hpaths.after_avoiding_action A.action_avoids_own_support
  have hreturn := (physicalTrace_contact_retraces_prefix_pointwise
    (A.runway_trace_at state hpaths) (hpathsAfter A.runway A.runway_mem_support)
    A.entryEdge (A.orientedFinish_arrive state hpaths))
  apply stepN_cover_append htrace.sound ?_ ?_ d
    (by rwa [← A.travel_eq_oriented_add state])
  · intro t ht
    obtain ⟨port, hr⟩ := htrace.grooved_prefix_tongues state hg ht
    exact ⟨port, state, hr, Or.inl rfl⟩
  · intro t ht
    obtain ⟨port, hr⟩ := hreturn t ht
    exact ⟨port, _, hr, by split <;> simp⟩

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
  obtain ⟨port, phase, hr, hp⟩ := A.travel_two_phase_stepN _ hflipped hle
  change stepN w (C.runway.length + d) (g, flipAt state C.actionSwitch) =
    some (port, phase) at hr
  rw [stepN_add, (C.runway_trace _ hrunwayFlip).sound] at hr
  exact ⟨port, phase, hr, by
    simpa [A, ManufacturedReflector.toSupported, ManufacturedFlipReflector.toSupported,
      LocalAction.apply, flipAt_flipAt] using hp⟩


end GeneralN
