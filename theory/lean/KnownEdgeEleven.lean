import KnownEdgeFourteen
import TrackEarlyRepairSharp
import FacingForwardNovelty

/-!
# Known-edge coefficient-11 linear bound

The remaining `12*N` repair branches were physical-length artefacts.
Switch-simple early retraces close within `6*N+3`, while a facing-forward
splice has a bounded lead of at most four reflector travels and then only one
new tongue phase.  Thus every protected-repair tail exposes at most `9*N+5`
restricted tongue vectors.  Adding the two construction histories gives the
known-edge bound `11*N+8`.
-/

namespace GeneralN

/-- A facing-forward splice exposes at most `4*N+2` distinct restricted
tongue vectors: its concrete lead window has length at most `4*N+1`, and the
infinite two-phase tail contributes at most one further vector. -/
theorem ManufacturedReflector.FacingForwardMerge.distinct_le_four_mul_add_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.FacingForwardMerge B)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 4 * N + 2 := by
  obtain ⟨S⟩ := hmerge.has_pointwiseTail
  let history := (List.range (S.leadSteps + 1)).map
    (restrictedTonguesAt w N (g, B.activatedState))
  have hleadHistorical : ∀ j, j ≤ S.leadSteps →
      restrictedTonguesAt w N (g, B.activatedState) j ∈ history := by
    intro j hj
    exact List.mem_map.mpr
      ⟨j, List.mem_range.mpr (by omega), rfl⟩
  have hcount := S.distinct_samples_le_history_add_one
    history hleadHistorical times hnd
  have hhistoryLen : history.length = S.leadSteps + 1 := by
    simp [history]
  have hAtravel : A.toSupported.travel ≤ 2 * N :=
    A.travel_le_two_mul_switches hN
  have hBtravel : B.toSupported.travel ≤ 2 * N :=
    B.travel_le_two_mul_switches hN
  have hlead := S.lead_le
  omega

/-- Protected repair exposes at most `9*N+5` distinct restricted tongue
vectors.  Early exits cost `6*N+3`, facing-forward splices `4*N+2`, changed
splices `9*N+5`, and complete repair `9*N+4`. -/
theorem manufactured_pair_protected_repair_distinct_le_nine_succ_five
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
    times.length ≤ 9 * N + 5 := by
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
      · have hc := hchanged.distinct_le_nine_succ_five hN times
          hlive hnd
        omega
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        have hc := A.completed_route_with_pair_support_distinct_le_nine_succ_four
          hN B B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal times hlive hnd
        omega

/-- Known-edge long-run coefficient-11 bound. -/
theorem known_edge_long_run_distinct_le_eleven
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlong : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 11 * N + 8 := by
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
        tailTimes.length ≤ 9 * N + 5 := by
      intro tailTimes htailLive htailNodup
      have htailLive' : ∀ k ∈ tailTimes,
          (stepN w k (start.1, B.activatedState)).isSome := by
        simpa [← hactivatedB] using htailLive
      have htailNodup' :
          (tailTimes.map
            (restrictedTonguesAt w N
              (start.1, B.activatedState))).Nodup := by
        simpa [← hactivatedB] using htailNodup
      exact manufactured_pair_protected_repair_distinct_le_nine_succ_five
        hN A B hAatBase hBatActivated tailTimes
          htailLive' htailNodup'
    have hassembled :=
      two_manufacturing_journeys_then_direct_tail_distinct_le
        (tailCap := 9 * N + 5)
        hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
        hbaseB hactivatedB hreachB hgroovesB htail times hlive hnd
    omega

end GeneralN
