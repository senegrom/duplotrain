import PairTongueCountFour
import TrackStaySpliceSharp
import TrackThetaTighter
import TrackQuantitativeRouteSharp
import TrackGlobalRepairSimple
import TwoJourneyTailCountSharp

/-!
# Known-edge coefficient-14 linear bound

The changed-forward flip splice already has a pointwise four-novelty cover
(`runway_or_candy_absolute_four_novelty`); discharging its lead hypothesis
by position-counting the bounded lead window costs `2*N+1` vectors, so the
branch counts `2*N+5`.  With the stay splice at `9*N` and the sharpened
complete repair at `9*N+4`, every protected-repair branch fits inside
`12*N+5`, which the two-journey assembly turns into `14*N+8` known-edge.
-/

namespace GeneralN

/-- Changed-forward flip splice: at most `2*N+5` distinct restricted
tongue vectors — the lead window by position, the tail by the pointwise
four-novelty cover. -/
theorem ManufacturedReflector.ChangedForwardMerge.flip_distinct_le_two_mul_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R))
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).activatedState))).Nodup) :
    times.length ≤ 2 * N + 5 := by
  let window := (List.range (A.toSupported.travel + 1)).map
    (restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).activatedState))
  have hleadHistorical : ∀ j, j ≤ A.toSupported.travel →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈
          window := by
    intro j hj
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩
  have hcover := hmerge.runway_or_candy_absolute_four_novelty
    N window hleadHistorical times
  have hcover' : NoveltyCoverOn w N
      (g, (ManufacturedReflector.flip R).activatedState)
      times window 4 := hcover
  have hcount := noveltyCoverOn_distinct_count hcover' hnd
  have hwin : window.length = A.toSupported.travel + 1 := by
    simp [window]
  have htravel : A.toSupported.travel ≤ 2 * N :=
    A.travel_le_two_mul_switches hN
  omega

/-- Every changed-forward merge exposes at most `9*N+5` distinct restricted
tongue vectors: `9*N` for the stay splice, `2*N+5` for the flip splice. -/
theorem ManufacturedReflector.ChangedForwardMerge.distinct_le_nine_succ_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hmerge : A.ChangedForwardMerge B)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, B.activatedState))).Nodup) :
    times.length ≤ 9 * N + 5 := by
  cases B with
  | stay R =>
      have hnd' : (times.map (fun k =>
          VectorCount.restrict N (tonguesAt w
            (g, (ManufacturedReflector.stay R).activatedState) k))).Nodup := by
        exact hnd
      have hlocal := hmerge.stay_within_nine hN
      have hc := hlocal.tongue_vector_count times hlive hnd'
      omega
  | flip R =>
      have hc := hmerge.flip_distinct_le_two_mul_add_five hN times hnd
      omega

/-- Protected repair exposes at most `12*N+5` distinct restricted tongue
vectors: the periodic and facing outcomes by their `12*N` lassos, the
changed splice by `9*N+5`, the complete repair by `9*N+4`. -/
theorem manufactured_pair_protected_repair_distinct_le_twelve_succ_five
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
    times.length ≤ 12 * N + 5 := by
  have hnd' : (times.map (fun k =>
      VectorCount.restrict N
        (tonguesAt w (g, B.activatedState) k))).Nodup := by
    exact hnd
  rcases manufactured_pair_protected_repair_quantitative_outcomes
      hN A B hA hB with hperiodic | hrest
  · have hc := hperiodic.tongue_vector_count times hlive hnd'
    omega
  · rcases hrest with hfacing | hrest
    · have hlocal := hfacing.within_twelve hN
      have hc := hlocal.tongue_vector_count times hlive hnd'
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

/-- Known-edge long-run coefficient-14 bound. -/
theorem known_edge_long_run_distinct_le_fourteen
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlong : stepN w (3 * N + 2) start = some finish)
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 14 * N + 8 := by
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
        tailTimes.length ≤ 12 * N + 5 := by
      intro tailTimes htailLive htailNodup
      have htailLive' : ∀ k ∈ tailTimes,
          (stepN w k (start.1, B.activatedState)).isSome := by
        simpa [← hactivatedB] using htailLive
      have htailNodup' :
          (tailTimes.map
            (restrictedTonguesAt w N
              (start.1, B.activatedState))).Nodup := by
        simpa [← hactivatedB] using htailNodup
      exact manufactured_pair_protected_repair_distinct_le_twelve_succ_five
        hN A B hAatBase hBatActivated tailTimes
          htailLive' htailNodup'
    have hassembled :=
      two_manufacturing_journeys_then_direct_tail_distinct_le
        (tailCap := 12 * N + 5)
        hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
        hbaseB hactivatedB hreachB hgroovesB htail times hlive hnd
    omega

end GeneralN
