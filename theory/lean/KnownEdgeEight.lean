import KnownEdgeEleven
import PairTongueCountAbsoluteFour
import TrackStaySpliceAllTime

/-!
# Known-edge coefficient-8 linear bound

The protected-repair branches now have the following direct tongue counts:

* early retrace/capture: `6*N+3`;
* facing-forward splice: `4*N+2`;
* changed stay splice: `N+2`;
* changed flip splice: `2*N+5`;
* complete repair: `N+4`.

A manufactured reflector forces `N>0`, so all branches fit in `6*N+3`.
Adding the two construction histories gives `8*N+6` known-edge.
-/

namespace GeneralN

/-- Protected repair exposes at most `6*N+3` distinct restricted tongue
vectors. -/
theorem manufactured_pair_protected_repair_distinct_le_six_succ_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 6 * N + 3 := by
  have hNpos : 0 < N := by
    have hp := hN _ _ A.entryEdge
    omega
  have hnd' : (times.map (fun k =>
      VectorCount.restrict N
        (tonguesAt w (g, B.activatedState) k))).Nodup := by
    exact hnd
  rcases manufactured_pair_protected_repair_quantitative_outcomes_six_succ_three
      hN A B hA hB with hperiodic | hrest
  · have hc := hperiodic.tongue_vector_count times hlive hnd'
    omega
  · rcases hrest with hfacing | hrest
    · have hc := hfacing.distinct_le_four_mul_add_two hN times hnd
      omega
    · rcases hrest with hchanged | hcomplete
      · cases B with
        | stay R =>
            have hc := hchanged.stay_distinct_le_n_succ_two hN times hnd
            omega
        | flip R =>
            have hc := hchanged.flip_distinct_le_two_mul_add_five hN times hnd
            omega
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        have hc := A.completed_route_with_pair_support_distinct_le_n_succ_four
          hN B B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal times hlive hnd
        omega

/-- Known-edge long-run coefficient-8 bound. -/
theorem known_edge_long_run_distinct_le_eight
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlong : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 8 * N + 6 := by
  rcases two_component_quantitative_outcome_exact hN hlong hentry with
    hperiodic | hpair
  · have hsmall := hperiodic.tongue_vector_count times hlive (by
      exact hnd)
    omega
  · obtain ⟨A, B, stateA, stateB,
      _hfirstLe, _hsecondLe, hbaseA, hactivatedA,
      hreachA, hgroovesA, hbaseB, hactivatedB,
      hreachB, hgroovesB, _hpreservesB⟩ := hpair
    have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
      simpa [hbaseB] using hgroovesA
    have hBatActivated :
        PathGrooves B.toSupported.paths B.activatedState := by
      simpa [← hactivatedB] using hgroovesB
    have htail : ∀ (tailTimes : List Nat),
        (∀ k ∈ tailTimes,
          (stepN w k (start.1, stateB)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (start.1, stateB))).Nodup →
        tailTimes.length ≤ 6 * N + 3 := by
      intro tailTimes htailLive htailNodup
      have htailLive' : ∀ k ∈ tailTimes,
          (stepN w k (start.1, B.activatedState)).isSome := by
        simpa [← hactivatedB] using htailLive
      have htailNodup' :
          (tailTimes.map
            (restrictedTonguesAt w N
              (start.1, B.activatedState))).Nodup := by
        simpa [← hactivatedB] using htailNodup
      exact manufactured_pair_protected_repair_distinct_le_six_succ_three
        hN A B hAatBase hBatActivated tailTimes
          htailLive' htailNodup'
    have hassembled :=
      two_manufacturing_journeys_then_direct_tail_distinct_le
        (tailCap := 6 * N + 3)
        hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
        hbaseB hactivatedB hreachB hgroovesB htail times hlive hnd
    omega

end GeneralN
