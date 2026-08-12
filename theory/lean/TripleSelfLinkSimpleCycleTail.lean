import TripleSelfLinkSimpleCycleClosure

/-!
# Quantitative closure of the self-link simple-cycle branch

A stable switch-simple lap is grooved, hence carries one complete tongue
vector at every intermediate time. Periodic extension gives an all-time
one-vector tail. The raw cycle rotates that tail back to the selected close.
-/

namespace GeneralN

/-- A stable switch-simple physical cycle is an exact all-time one-vector
tail, represented through the existing two-vector interface. -/
theorem rawTwoVectorTail_of_stable_simple_cycle_exact
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {shift p : Nat} {settled : Tongues} {cycle : List Passage}
    (hreach : stepN w shift start = some (p, settled))
    (hnonempty : cycle ≠ [])
    (hstable : PhysicalTrace w (p, settled) cycle (p, settled))
    (hsimple : SwitchSimple cycle) :
    exists P : RawTwoVectorTail w N start,
      P.shift = shift /\ P.localStart = (p, settled) := by
  have hpositive : 0 < cycle.length := by
    cases cycle with
    | nil => exact (hnonempty rfl).elim
    | cons passage rest => simp
  have hperiod : stepN w cycle.length (p, settled) =
      some (p, settled) := hstable.sound
  have hgrooved : PassagesGrooved settled cycle :=
    hstable.grooved_of_switchSimple hsimple
  have hwindow : forall d, d <= cycle.length ->
      exists port phase,
        stepN w d (p, settled) = some (port, phase) /\
        (phase = settled \/ phase = settled) := by
    intro d hd
    obtain ⟨port, hrun⟩ :=
      hstable.grooved_prefix_tongues settled hgrooved hd
    exact ⟨port, settled, hrun, Or.inl rfl⟩
  have hall : forall d, exists port phase,
      stepN w d (p, settled) = some (port, phase) /\
      (phase = settled \/ phase = settled) :=
    periodic_two_phase_prefix_tongues hpositive hperiod hwindow
  let phase := VectorCount.restrict N settled
  let P : RawTwoVectorTail w N start := {
    shift := shift
    localStart := (p, settled)
    phase₀ := phase
    phase₁ := phase
    reached := hreach
    live := by
      intro d
      obtain ⟨port, state, hrun, _hstate⟩ := hall d
      exact ⟨(port, state), hrun⟩
    two_vectors := by
      intro d
      obtain ⟨port, state, hrun, hstate⟩ := hall d
      rcases hstate with rfl | rfl <;>
        simp [restrictedTonguesAt, tonguesAt, hrun, phase]
  }
  exact ⟨P, rfl, rfl⟩

/-- Rotate the stable simple-cycle tail back to the selected raw-cycle base,
retaining the exact shift. -/
theorem RawCycleThroughSelfLink.close_tail_of_simple_cycle_trace_exact
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close)
    {outside : Nat} {atRepeat : Prod Nat Tongues} {visited : Nat}
    {cycle : List Passage} {settled : Tongues}
    (hmouth : w.link (3 * (R.branch / 3)) = some outside)
    (hvisited : stepN w visited (outside, R.state) = some atRepeat)
    (hnonempty : cycle ≠ [])
    (htransient : PhysicalTrace w atRepeat cycle
      (atRepeat.1, settled))
    (hstable : PhysicalTrace w (atRepeat.1, settled) cycle
      (atRepeat.1, settled))
    (hsimple : SwitchSimple cycle) :
    exists P : RawTwoVectorTail w N start, P.shift = close := by
  obtain ⟨outside', hmouth', houtside'⟩ := R.branch_step
  have houtsideEq : outside = outside' :=
    Option.some.inj (hmouth.symm.trans hmouth')
  subst outside'
  let outsideOffset := R.offset + 1
  have htoOutside : stepN w outsideOffset R.closeConfig =
      some (outside, R.state) := by
    dsimp [outsideOffset]
    rw [stepN_add, R.self_at]
    exact houtside'
  let repeatOffset := outsideOffset + visited
  have htoRepeat : stepN w repeatOffset R.closeConfig =
      some atRepeat := by
    dsimp [repeatOffset]
    rw [stepN_add, htoOutside]
    exact hvisited
  let stableOffset := repeatOffset + cycle.length
  have htoStable : stepN w stableOffset R.closeConfig =
      some (atRepeat.1, settled) := by
    dsimp [stableOffset]
    rw [stepN_add, htoRepeat]
    exact htransient.sound
  let shift := close + stableOffset
  have hreach : stepN w shift start =
      some (atRepeat.1, settled) := by
    dsimp [shift]
    rw [stepN_add, R.close_at]
    exact htoStable
  obtain ⟨P, _hshift, hlocal⟩ :=
    rawTwoVectorTail_of_stable_simple_cycle_exact
      (N := N) hreach hnonempty hstable hsimple
  have htoStable' : stepN w stableOffset R.closeConfig =
      some P.localStart := by
    rw [hlocal]
    exact htoStable
  exact P.rotate_back_to_period_base_exact R.close_at R.period_positive
    R.cycle htoStable'

/-- The trace-valued simple-cycle outcome yields the same forbidden literal
five-close four-cover as the opposite-reflector outcome. -/
theorem RawSixEventReduction.tail_simple_cycle_false
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (htriple : FiveFrameTripleOutcome
      R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4 R.a5 R.z5)
    (S : SelectedFiveFrameABCABC (R.tailTripleCase htriple))
    (Cyc : RawCycleThroughSelfLink w start
      ((R.tailTripleCase htriple).frames.closingAt S.i0))
    {outside : Nat} {atRepeat : Prod Nat Tongues} {visited : Nat}
    {cycle : List Passage} {settled : Tongues}
    (hmouth : w.link (3 * (Cyc.branch / 3)) = some outside)
    (hvisited : stepN w visited (outside, Cyc.state) = some atRepeat)
    (hnonempty : cycle ≠ [])
    (htransient : PhysicalTrace w atRepeat cycle
      (atRepeat.1, settled))
    (hstable : PhysicalTrace w (atRepeat.1, settled) cycle
      (atRepeat.1, settled))
    (hsimple : SwitchSimple cycle) : False := by
  obtain ⟨P, hshift⟩ :=
    Cyc.close_tail_of_simple_cycle_trace_exact
      (N := N) hmouth hvisited hnonempty htransient hstable hsimple
  apply R.no_tail_fixed_four_cover hN
  apply five_close_noveltyCoverOn_four_of_two_vector_tail
    (R.tailFixedFrames hN) (R.tailTripleCase htriple) S P
  exact Nat.le_trans (Nat.le_of_eq hshift) (Nat.le_succ _)

/-- Both first-revisit outcomes of a raw cycle through the selected self-link
are impossible: simple-cycle by the preceding tail rotation, and opposite
reflector by the previous module's exact selected-state closure. -/
theorem RawSixEventReduction.tail_cycle_self_link_false
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (htriple : FiveFrameTripleOutcome
      R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4 R.a5 R.z5)
    (S : SelectedFiveFrameABCABC (R.tailTripleCase htriple))
    (Cyc : RawCycleThroughSelfLink w start
      ((R.tailTripleCase htriple).frames.closingAt S.i0)) : False := by
  obtain ⟨outside, atRepeat, visited, hmouth, hvisited, houtcome⟩ :=
    Cyc.outside_first_revisit_trace_or_reflector
  rcases houtcome with hcycle | hreflector
  · obtain ⟨cycle, settled, hnonempty, htransient, hstable,
        hsimple⟩ := hcycle
    exact R.tail_simple_cycle_false hN htriple S Cyc
      hmouth hvisited hnonempty htransient hstable hsimple
  · obtain ⟨A, state, backSteps, hA, hbase, hstate, hback,
        _hpreserves⟩ := hreflector
    exact R.tail_opposite_reflector_false hN htriple S Cyc
      A state backSteps hmouth hvisited hA hbase hstate hback

end GeneralN
