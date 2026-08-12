import TraceRetainingFirstRevisit
import MinimalBABASecondRepeat
import TripleSelfLinkSimpleCycleTail

/-!
# Trace-retaining Mellit second repeat

The existing exact-lobe second-repeat theorem deliberately returned
`SettlesOnSimpleCycle`, which forgets every intermediate passage of the
stable lap.  This file reruns the same physical fork through the generic
trace-retaining first-revisit API.  The opposite-reflector branch is
unchanged; the cycle branch now carries the transient and stable
switch-simple traces required by pointwise novelty accounting.
-/

namespace GeneralN

/-- Mellit's second repeat with a physical stable-cycle witness. -/
theorem rawExactLobeWrite_second_repeat_cycle_traces_or_pair
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start next finish : Nat × Tongues} {k : Nat}
    {passages : List Passage}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k)
    (hnext : stepN w (k + 1) start = some next)
    (htrace : PhysicalTrace w next passages finish)
    (hnonsimple : ¬ SwitchSimple passages) :
    (∃ atRepeat visited cycle settled,
        stepN w visited next = some atRepeat ∧
        cycle ≠ [] ∧
        PhysicalTrace w atRepeat cycle (atRepeat.1, settled) ∧
        PhysicalTrace w (atRepeat.1, settled) cycle
          (atRepeat.1, settled) ∧
        SwitchSimple cycle) ∨
      (∃ (A : ManufacturedFlipReflector w
            (3 * rawWriterAt w start k) next.1)
          (B : ManufacturedReflector w next.1
            (3 * rawWriterAt w start k))
          (atRepeat : Nat × Tongues) (visited backSteps : Nat),
        next.2 = (ManufacturedReflector.flip A).activatedState ∧
        A.runway = [] ∧ A.candy = [] ∧
        A.actionSwitch = rawWriterAt w start k ∧
        stepN w visited next = some atRepeat ∧
        stepN w (visited + backSteps) next =
          some (3 * rawWriterAt w start k, B.activatedState) ∧
        PathGrooves (ManufacturedReflector.flip A).toSupported.paths
          B.baseState ∧
        PathGrooves B.toSupported.paths B.activatedState ∧
        EventuallyPeriodic w
          (3 * rawWriterAt w start k, B.activatedState)) := by
  obtain ⟨witness, hwitness, hstemWitness⟩ :=
    rawProductiveAt_fixed_stem_successor hN hprod
  have hwitnessEq : witness = next := by
    exact Option.some.inj (hwitness.symm.trans hnext)
  subst witness
  have hbranch := rawExactLobeWrite_selected_to_unmatched hN hprod hlobe
  let A : ManufacturedFlipReflector w
      (3 * rawWriterAt w start k) next.1 :=
    manufacturedFlipReflectorOfSelectedLobe
      (rawWriterAt w start k) next.1 (tonguesAt w start k)
      hbranch hstemWitness
  have hactivated :
      next.2 = (ManufacturedReflector.flip A).activatedState := by
    have hpost := rawExactLobeWrite_post_is_activated hN hprod hnext
    simpa [A, manufacturedFlipReflectorOfSelectedLobe,
      ManufacturedReflector.activatedState] using hpost
  obtain ⟨atRepeat, visited, hvisited, houtcome⟩ :=
    htrace.first_revisit_trace_or_activated_reflector
      hnonsimple hstemWitness
  rcases houtcome with hcycle | hreflector
  · obtain ⟨cycle, settled, hnonempty, htransient,
        hstable, hsimple⟩ := hcycle
    exact Or.inl ⟨atRepeat, visited, cycle, settled,
      hvisited, hnonempty, htransient, hstable, hsimple⟩
  · obtain ⟨B, state, backSteps, hBpaths, hBbase,
        hstate, hback, _hpreserves⟩ := hreflector
    have hreach : stepN w (visited + backSteps) next =
        some (3 * rawWriterAt w start k, B.activatedState) := by
      rw [stepN_add, hvisited]
      simpa [hstate] using hback
    have hAatBase :
        PathGrooves (ManufacturedReflector.flip A).toSupported.paths
          B.baseState := by
      simp [A, manufacturedFlipReflectorOfSelectedLobe,
        ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported, PathGrooves,
        PassagesGrooved]
    have hAatActivated :
        PathGrooves (ManufacturedReflector.flip A).toSupported.paths
          B.activatedState := by
      simp [A, manufacturedFlipReflectorOfSelectedLobe,
        ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported, PathGrooves,
        PassagesGrooved]
    have hBatActivated :
        PathGrooves B.toSupported.paths B.activatedState := by
      simpa [hstate] using hBpaths
    have hperiodic : EventuallyPeriodic w
        (3 * rawWriterAt w start k, B.activatedState) :=
      manufactured_pair_eventually_periodic
        (.flip A) B B.activatedState hAatActivated hBatActivated
    exact Or.inr ⟨A, B, atRepeat, visited, backSteps,
      hactivated, rfl, rfl, (by
        simp [A, manufacturedFlipReflectorOfSelectedLobe,
          ManufacturedFlipReflector.actionSwitch]), hvisited, hreach,
      hAatBase, hBatActivated, hperiodic⟩

/-- The trace-valued cycle branch also retains its exact absolute raw reach
from the original run. -/
structure ReachedStableSimpleCycle
    (w : Wiring) (start : Nat × Tongues) : Type where
  shift : Nat
  atRepeat : Nat × Tongues
  cycle : List Passage
  settled : Tongues
  reached : stepN w shift start = some atRepeat
  nonempty : cycle ≠ []
  transient : PhysicalTrace w atRepeat cycle (atRepeat.1, settled)
  stable : PhysicalTrace w (atRepeat.1, settled) cycle
    (atRepeat.1, settled)
  simple : SwitchSimple cycle

/-- Transport a locally reached stable cycle into absolute raw time. -/
theorem reachedStableSimpleCycle_of_prefix
    {w : Wiring} {start next : Nat × Tongues}
    {baseShift visited : Nat}
    (hbaseShift : stepN w baseShift start = some next)
    {atRepeat : Nat × Tongues} {cycle : List Passage}
    {settled : Tongues}
    (hvisited : stepN w visited next = some atRepeat)
    (hnonempty : cycle ≠ [])
    (htransient : PhysicalTrace w atRepeat cycle
      (atRepeat.1, settled))
    (hstable : PhysicalTrace w (atRepeat.1, settled) cycle
      (atRepeat.1, settled))
    (hsimple : SwitchSimple cycle) :
    Nonempty (ReachedStableSimpleCycle w start) := by
  refine ⟨{
    shift := baseShift + visited
    atRepeat := atRepeat
    cycle := cycle
    settled := settled
    reached := by
      rw [stepN_add, hbaseShift]
      exact hvisited
    nonempty := hnonempty
    transient := htransient
    stable := hstable
    simple := hsimple
  }⟩

/-- Every reached stable simple cycle produces an exact one-vector tail after
one transient lap. -/
theorem ReachedStableSimpleCycle.one_vector_tail
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : ReachedStableSimpleCycle w start) :
    ∃ P : RawTwoVectorTail w N start,
      P.shift = C.shift + C.cycle.length := by
  have hstableReach : stepN w (C.shift + C.cycle.length) start =
      some (C.atRepeat.1, C.settled) := by
    rw [stepN_add, C.reached]
    exact C.transient.sound
  obtain ⟨P, hshift, _hlocal⟩ :=
    rawTwoVectorTail_of_stable_simple_cycle_exact
      (N := N) hstableReach C.nonempty C.stable C.simple
  exact ⟨P, hshift⟩

end GeneralN
