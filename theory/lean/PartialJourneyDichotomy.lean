import PartialSecondRunSharp
import TraceRetainingFirstRevisit
import TraceRetainingBABASecondRepeat
import PointwiseSimpleCycleTail

/-!
# Structural dichotomy for an unfinished second journey

This file separates the dynamic statement "the second probe does not
manufacture an opposite reflector" from the coefficient-one accounting
problem.  The dynamic conclusion is exact: the `N+1` probe either dies, or
reaches a stable switch-simple cycle.  The latter has one settled restricted
tongue vector at every absolute time after its transient lap.

The statements are over raw `Wiring`, `PhysicalTrace`, and `stepN`; there is
no finite-`N` evaluation and no hidden completion selector.
-/

namespace GeneralN

/-- The literal reflector payload returned by the second `N+1` probe. -/
structure PartialSecondReflectorCompletion
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : Type where
  reflector : ManufacturedReflector w e g
  state : Tongues
  length_le :
    reflector.exploration.length + reflector.runway.length + 1 <=
      2 * N + 1
  paths : PathGrooves reflector.toSupported.paths state
  base : reflector.baseState = A.activatedState
  activated : state = reflector.activatedState
  reaches :
    stepN w
      (reflector.exploration.length + reflector.runway.length + 1)
      (e, A.activatedState) = some (g, state)
  preserves : forall j,
    j ∉ reflector.exploration.map passageSwitch ->
      state j = A.activatedState j

/-- A retained first-activation cycle is already a reached stable simple
cycle, with the exact shift equal to the switch-simple lead length. -/
def PartialSecondCycleOutcome.toReachedStableSimpleCycle
    {w : Wiring} {start : Nat × Tongues} {N : Nat}
    (C : PartialSecondCycleOutcome w start N) :
    ReachedStableSimpleCycle w start := {
  shift := C.lead.length
  atRepeat := C.atRepeat
  cycle := C.cycle
  settled := C.settled
  reached := C.lead_trace.sound
  nonempty := C.cycle_nonempty
  transient := C.transient
  stable := C.stable
  simple := C.cycle_simple
}

/-- The raw second probe after a completed first reflector has exactly three
structural outcomes: death at the probe horizon, a reached stable simple
cycle, or a literal opposite manufactured reflector. -/
theorem ManufacturedReflector.partial_second_probe_outcome
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N) :
    stepN w (N + 1) (e, A.activatedState) = none ∨
      Nonempty (ReachedStableSimpleCycle w (e, A.activatedState)) ∨
      Nonempty (PartialSecondReflectorCompletion A N) := by
  cases hprobe : stepN w (N + 1) (e, A.activatedState) with
  | none =>
      exact Or.inl rfl
  | some finish =>
      have hentry : w.link g = some e :=
        w.symm _ _ A.entryEdge
      rcases first_activated_trace_outcome_sharp_partial
          hN hprobe hentry with hcycle | hreflector
      · exact Or.inr (Or.inl
          ⟨Classical.choice hcycle |>.toReachedStableSimpleCycle⟩)
      · obtain ⟨B, state, hlength, hpaths, hbase,
          hactivated, hreach, hpreserves⟩ := hreflector
        exact Or.inr (Or.inr ⟨{
          reflector := B
          state := state
          length_le := hlength
          paths := hpaths
          base := hbase
          activated := hactivated
          reaches := hreach
          preserves := hpreserves
        }⟩)

/-- If the literal opposite-reflector payload is impossible, only death or
a reached stable simple cycle remains. -/
theorem ManufacturedReflector.partial_second_probe_dead_or_cycle
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hnoSecond : Not (Nonempty
      (PartialSecondReflectorCompletion A N))) :
    stepN w (N + 1) (e, A.activatedState) = none ∨
      Nonempty (ReachedStableSimpleCycle w (e, A.activatedState)) := by
  rcases A.partial_second_probe_outcome hN with
      hdead | hcycle | hreflector
  · exact Or.inl hdead
  · exact Or.inr hcycle
  · exact (hnoSecond hreflector).elim

/-- Independent trace-level form of the same structural fact.  Any
nonsimple continuation from a known entry edge either exposes a manufactured
reflector or reaches a stable switch-simple cycle.  Excluding the former
therefore gives the latter without mentioning a probe horizon. -/
theorem PhysicalTrace.nonsimple_no_reflector_reaches_stable_cycle
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {entryEdge : Nat}
    (htrace : PhysicalTrace w start passages finish)
    (hnonsimple : Not (SwitchSimple passages))
    (hentry : w.link entryEdge = some start.1)
    (hnoReflector : forall
      (B : ManufacturedReflector w start.1 entryEdge)
      (state : Tongues) (backSteps : Nat),
      PathGrooves B.toSupported.paths state ->
      B.baseState = start.2 ->
      state = B.activatedState ->
      (exists atRepeat visited,
        stepN w visited start = some atRepeat ∧
        stepN w backSteps atRepeat = some (entryEdge, state)) ->
      False) :
    Nonempty (ReachedStableSimpleCycle w start) := by
  obtain ⟨atRepeat, visited, hvisited, houtcome⟩ :=
    htrace.first_revisit_trace_or_activated_reflector
      hnonsimple hentry
  rcases houtcome with hcycle | hreflector
  · obtain ⟨cycle, settled, hnonempty, htransient,
        hstable, hsimple⟩ := hcycle
    exact reachedStableSimpleCycle_of_prefix
      (baseShift := 0) (visited := visited)
      (by simp [stepN]) hvisited hnonempty
      htransient hstable hsimple
  · obtain ⟨B, state, backSteps, hpaths, hbase,
        hactivated, hback, _hpreserves⟩ := hreflector
    exact (hnoReflector B state backSteps hpaths hbase hactivated
      ⟨atRepeat, visited, hvisited, hback⟩).elim

/-- Exact absolute one-vector tail of a reached stable simple cycle. -/
theorem ReachedStableSimpleCycle.absolute_settled_vector
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : ReachedStableSimpleCycle w start) :
    forall t, C.shift + C.cycle.length <= t ->
      restrictedTonguesAt w N start t =
        VectorCount.restrict N C.settled := by
  have hstableReach :
      stepN w (C.shift + C.cycle.length) start =
        some (C.atRepeat.1, C.settled) := by
    rw [stepN_add, C.reached]
    exact C.transient.sound
  have hall :=
    C.stable.stable_simple_cycle_all_time
      C.nonempty C.simple
  intro t ht
  let d := t - (C.shift + C.cycle.length)
  have htEq : t = C.shift + C.cycle.length + d := by
    dsimp [d]
    omega
  obtain ⟨port, hlocal⟩ := hall d
  have hglobal : stepN w t start = some (port, C.settled) := by
    rw [htEq, stepN_add, hstableReach]
    exact hlocal
  simp [restrictedTonguesAt, tonguesAt, hglobal]

/-- Consequently any duplicate-free sample lying wholly in that stable tail
contains at most one restricted tongue vector. -/
theorem ReachedStableSimpleCycle.stable_tail_distinct_le_one
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : ReachedStableSimpleCycle w start)
    (times : List Nat)
    (htail : forall t, t ∈ times ->
      C.shift + C.cycle.length <= t)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= 1 := by
  cases times with
  | nil => simp
  | cons t rest =>
      cases rest with
      | nil => simp
      | cons s tail =>
          have hnotmem := (List.nodup_cons.mp hnd).1
          exfalso
          apply hnotmem
          apply List.mem_map.mpr
          refine ⟨s, List.mem_cons_self, ?_⟩
          exact (C.absolute_settled_vector s
              (htail s (by simp))).trans
            (C.absolute_settled_vector t
              (htail t (by simp))).symm

end GeneralN
