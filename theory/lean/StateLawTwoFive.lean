import MellitFiveNoveltyAssembly
import StateLawTwoSharp

/-!
# Unconditional raw `2*N+5` state bound

The older coefficient-two assembly charged a completed pair of manufactured
reflectors as two independent `N+2` histories followed by four Gray states.
`ManufacturedReflector.two_journeys_all_run_distinct_le_N_add_six` now charges
that branch at coefficient one.  The other two branches of the same known-edge
decomposition were already bounded by `2*N+2` (dead suffix) and `2*N+4`
(simple-cycle suffix).  Taking the maximum gives `2*N+4` after a known incoming
edge when `2 <= N`; the elementary `2^N` theorem handles `N = 0, 1`.

Splitting off an arbitrary initial configuration then gives the raw
arbitrary-start bound `2*N+5`.  This does not prove the open coefficient-one
`GeneralN.StateLaw`.
-/

namespace GeneralN

private theorem twofive_nodup_of_map_nodup
    {alpha beta : Type}
    [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) :
    forall {xs : List alpha}, (xs.map f).Nodup -> xs.Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

private theorem twofive_live_distinct_le_of_stepN_none
    {w : Wiring} {N L : Nat}
    {start : Nat × Tongues} {times : List Nat}
    (hnone : stepN w L start = none)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= L := by
  have htimesNodup : times.Nodup :=
    twofive_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  apply nodup_nat_lt_length htimesNodup
  intro k hk
  by_cases hlt : k < L
  · exact hlt
  · have hkEq : k = L + (k - L) := by omega
    have hnoneK : stepN w k start = none := by
      rw [hkEq, stepN_add, hnone]
      simp
    have hkLive := hlive k hk
    rw [hnoneK] at hkLive
    simp at hkLive

/-- After entering through a known physical edge, every duplicate-free family
of live restricted tongue vectors has length at most `2*N+4`. -/
theorem known_edge_all_run_distinct_le_two_mul_add_four
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length <= 2 * N + 4 := by
  by_cases htwo : 2 <= N
  · cases hfirst : stepN w (N + 1) start with
    | none =>
        have hc := twofive_live_distinct_le_of_stepN_none
          (N := N) hfirst hlive hnd
        omega
    | some firstFinish =>
        rcases first_activated_count_outcome_sharp
            hN hfirst hentry with hcycleA | hreflectorA
        · have hc := hcycleA times hnd
          omega
        · obtain ⟨A, stateA, _hfirstLe, hgroovesA,
            hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
          have hentryB : w.link start.1 = some e :=
            w.symm _ _ A.entryEdge
          cases hsecond : stepN w (N + 1) (e, stateA) with
          | none =>
              have htail : forall tailTimes : List Nat,
                    (forall k, k ∈ tailTimes ->
                      (stepN w k (e, stateA)).isSome) ->
                    (tailTimes.map
                      (restrictedTonguesAt w N (e, stateA))).Nodup ->
                    tailTimes.length <= N + 1 := by
                intro tailTimes htailLive htailNodup
                exact twofive_live_distinct_le_of_stepN_none
                  hsecond htailLive htailNodup
              have hc :=
                one_manufacturing_journey_then_direct_tail_distinct_le
                  (tailCap := N + 1)
                  hN A stateA hbaseA hactivatedA hreachA hgroovesA
                  htail times hlive hnd
              omega
          | some secondFinish =>
              rcases first_activated_count_outcome_sharp
                  (w := w) (N := N) (e := start.1)
                  hN hsecond hentryB with hcycleB | hreflectorB
              · have htail : forall tailTimes : List Nat,
                    (forall k, k ∈ tailTimes ->
                      (stepN w k (e, stateA)).isSome) ->
                    (tailTimes.map
                      (restrictedTonguesAt w N (e, stateA))).Nodup ->
                    tailTimes.length <= N + 2 := by
                  intro tailTimes _htailLive htailNodup
                  exact hcycleB tailTimes htailNodup
                have hc :=
                  one_manufacturing_journey_then_direct_tail_distinct_le
                    (tailCap := N + 2)
                    hN A stateA hbaseA hactivatedA hreachA hgroovesA
                    htail times hlive hnd
                omega
              · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                    hbaseB, hactivatedB, _hreachB,
                    _hpreservesB⟩ := hreflectorB
                have hbaseAB : B.baseState = A.activatedState :=
                  hbaseB.trans hactivatedA
                have hAactivated :
                    PathGrooves A.toSupported.paths A.activatedState := by
                  rw [← hactivatedA]
                  exact hgroovesA
                have hBactivated :
                    PathGrooves B.toSupported.paths B.activatedState := by
                  rw [← hactivatedB]
                  exact hgroovesB
                have hliveA : forall k, k ∈ times ->
                    (stepN w k (start.1, A.baseState)).isSome := by
                  simpa [hbaseA] using hlive
                have hndA :
                    (times.map
                      (restrictedTonguesAt w N
                        (start.1, A.baseState))).Nodup := by
                  simpa [hbaseA] using hnd
                have hc :=
                  A.two_journeys_all_run_distinct_le_N_add_six
                    hN B hbaseAB hAactivated hBactivated
                    times hliveA hndA
                omega
  · have hsmall : N = 0 ∨ N = 1 := by omega
    rcases hsmall with rfl | rfl
    · change (times.map (fun k =>
        VectorCount.restrict 0 (tonguesAt w start k))).Nodup at hnd
      have hc := state_law_two_pow w 0 hN start times hlive hnd
      have hc' : times.length <= 1 := by simpa using hc
      omega
    · change (times.map (fun k =>
        VectorCount.restrict 1 (tonguesAt w start k))).Nodup at hnd
      have hc := state_law_two_pow w 1 hN start times hlive hnd
      have hc' : times.length <= 2 := by simpa using hc
      omega

/-- **Unconditional raw `2*N+5` theorem.**  A single train on an arbitrary
`N`-switch lazy-point wiring visits at most `2*N+5` pairwise-distinct
restricted tongue vectors. -/
theorem state_law_linear_two_add_five
    (w : Wiring) (N : Nat)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (start : Nat × Tongues)
    (times : List Nat)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length <= 2 * N + 5 := by
  apply arbitrary_start_distinct_le_succ_of_all_known_edge
    (cap := 2 * N + 4)
  · intro e localStart hentry localTimes hlocalLive hlocalNodup
    exact known_edge_all_run_distinct_le_two_mul_add_four
      hN hentry localTimes hlocalLive hlocalNodup
  · exact hlive
  · exact hnd

end GeneralN
