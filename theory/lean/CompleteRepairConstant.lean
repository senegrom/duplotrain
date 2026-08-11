import PairTongueCountAbsoluteFour
import RepairLeadTwoPhase
import TwoPhasePrefixTailCount

/-!
# Complete protected repair costs at most five tongue vectors

A completed protected repair route is itself a protected repair prefix, hence
has only its activated and final tongue phases.  From the endpoint onward the
restored opposite reflector pair has the already-proved flat four-vector
bound.  The shared endpoint is counted once, giving at most five vectors.
-/

namespace GeneralN

/-- A complete protected repair followed by the restored reflector pair
exposes at most five distinct restricted tongue vectors. -/
theorem ManufacturedReflector.completed_protected_route_with_pair_distinct_le_five
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 5 := by
  let L := (A.orientedRoute B.activatedState).length
  let endpoint : Nat × Tongues :=
    (A.orientedFinish B.activatedState, finalState)
  have hrepairReach :
      stepN w L (g, B.activatedState) = some endpoint := by
    simpa [L, endpoint] using hrepair.sound
  have hrouteMembership : ∀ passage ∈ A.orientedRoute B.activatedState,
      passage ∈ A.orientedRoute B.activatedState := by
    intro passage hp
    exact hp
  have hphase := A.repair_prefix_two_phase B hA hBstart
    hrepair (A.orientedRoute_simple B.activatedState)
    hrouteMembership hBfinal

  obtain ⟨reference, _hreferencePaths, hroute, hfinish,
      hreferenceGrooved, _hguard⟩ :=
    A.current_route_reference B.baseState B.activatedState hA
  have hfinalGrooved :
      PassagesGrooved finalState (A.orientedRoute B.activatedState) :=
    hrepair.grooved_of_switchSimple
      (A.orientedRoute_simple B.activatedState)
  have hfinalReferenceGrooved :
      PassagesGrooved finalState (A.orientedRoute reference) := by
    rw [hroute]
    exact hfinalGrooved
  have hreferenceGrooved' :
      PassagesGrooved reference (A.orientedRoute reference) := by
    rw [hroute]
    exact hreferenceGrooved
  have horiented := A.oriented_data_eq_of_route_grooved
    reference finalState hreferenceGrooved' hfinalReferenceGrooved
  have hrouteFinal := A.orientedRoute_trace finalState hAfinal
  have hrouteFinal' : PhysicalTrace w (g, finalState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState) := by
    rw [horiented.1, horiented.2, hroute, hfinish] at hrouteFinal
    exact hrouteFinal
  have hpairReach : stepN w L (g, finalState) = some endpoint := by
    simpa [L, endpoint] using hrouteFinal'.sound
  have htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes, (stepN w k endpoint).isSome) →
      (tailTimes.map (restrictedTonguesAt w N endpoint)).Nodup →
      tailTimes.length ≤ 4 := by
    intro tailTimes htailLive htailNodup
    exact manufactured_pair_reached_tongue_vector_count_four_all
      A B finalState hAfinal hBfinal hpairReach
      tailTimes htailLive htailNodup
  exact two_phase_prefix_then_direct_tail_distinct_le_succ
    hrepairReach hphase htail (by omega) times hlive hnd

end GeneralN
