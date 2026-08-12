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
