import KnownEdgeNAddFiveAlt

/-!
# Known-edge coefficient-one bound at `N + 5`

This file re-runs the raw known-edge structural dichotomy without retaining
the old opaque `N + 6` branch.  The only branch which formerly needed that
sixth additive state was a completed opposite reflector pair; the second
historical overlap proved in `KnownEdgeNAddFiveAlt` closes that branch at
`N + 5`.

Everything below is uniform in `N` and stated directly over `Wiring`,
`stepN`, and pairwise-distinct restricted tongue vectors.
-/

namespace GeneralN

private theorem ultraFive_nodup_of_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

/-- A run already dead at time `L` has fewer than `L` live sample times.
This local copy is needed because the corresponding implementation helper in
`StateLawCoefficientOneTop` is deliberately private. -/
private theorem ultraFive_live_distinct_le_of_stepN_none
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    {times : List Nat}
    (hnone : stepN w L start = none)
    (hlive : ∀ k, k ∈ times → (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ L := by
  have htimesNodup : times.Nodup :=
    ultraFive_nodup_of_map_nodup
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

/-- The known-edge first/second-repeat decomposition with the completed-pair
branch sharpened to `N+5`.  The two residual structures are retained exactly,
so no `N+6` estimate is smuggled through an opaque disjunct. -/
theorem known_edge_N_add_five_or_one_reflector_early_outcome_ultra
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k, k ∈ times → (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 5 ∨
      Nonempty (OneReflectorSecondDead w N e start) ∨
      Nonempty (OneReflectorDamagedCycle w N e start) := by
  cases hfirst : stepN w (N + 1) start with
  | none =>
      left
      have hc := ultraFive_live_distinct_le_of_stepN_none
        (N := N) hfirst hlive hnd
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycleA | hreflectorA
      · left
        have hc := hcycleA times hnd
        omega
      · obtain ⟨A, stateA, _hfirstLe, hgroovesA,
          hbaseA, hactivatedA, hreachA, _hpreservesA⟩ := hreflectorA
        subst stateA
        have hentryB : w.link start.1 = some e :=
          w.symm _ _ hentry
        have hliveA : ∀ k, k ∈ times →
            (stepN w k (start.1, A.baseState)).isSome := by
          simpa [hbaseA] using hlive
        have hndA : (times.map
            (restrictedTonguesAt w N
              (start.1, A.baseState))).Nodup := by
          simpa [hbaseA] using hnd
        have closePair : ∀
            (B : ManufacturedReflector w e start.1),
            B.baseState = A.activatedState →
            PathGrooves B.toSupported.paths B.activatedState →
            times.length ≤ N + 5 := by
          intro B hbaseB hgroovesB
          exact A.two_journeys_all_run_distinct_le_N_add_five_alt
            hN B hbaseB hgroovesA hgroovesB
            times hliveA hndA
        cases hsecond : stepN w (N + 1)
            (e, A.activatedState) with
        | none =>
            right
            left
            exact ⟨{
              A := A
              grooves := hgroovesA
              base := hbaseA
              reached := hreachA
              dead := hsecond
            }⟩
        | some secondFinish =>
            rcases first_activated_count_outcome_sharp
                (w := w) (N := N) (e := start.1)
                hN hsecond hentryB with
              _hcycleB | hreflectorB
            · rcases first_activated_trace_outcome_sharp
                  (w := w) (N := N) (e := start.1)
                  hN hsecond hentryB with htraceCycle | hreflectorB'
              · obtain ⟨C⟩ := htraceCycle
                by_cases hrepeat :
                    PathGrooves A.toSupported.paths C.atRepeat.2
                · left
                  have hc := C.preserved_all_run_distinct_le_N_add_three
                    hN A hgroovesA hrepeat times hliveA hndA
                  omega
                · right
                  right
                  exact ⟨{
                    A := A
                    grooves := hgroovesA
                    base := hbaseA
                    reached := hreachA
                    cycle := C
                    damaged := hrepeat
                  }⟩
              · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                    hbaseB, hactivatedB, _hreachB,
                    _hpreservesB⟩ := hreflectorB'
                subst stateB
                left
                exact closePair B hbaseB hgroovesB
            · obtain ⟨B, stateB, _hsecondLe, hgroovesB,
                  hbaseB, hactivatedB, _hreachB,
                  _hpreservesB⟩ := hreflectorB
              subst stateB
              left
              exact closePair B hbaseB hgroovesB

/-- **General known-edge coefficient-one theorem at `N+5`.**

For every finite `N`-switch raw track whose starting port has a known incoming
edge, every duplicate-free list of live restricted tongue vectors has length
at most `N+5`.  This is the stronger known-edge theorem needed to lift an
arbitrary start to `N+6`.
-/
theorem known_edge_all_run_distinct_le_N_add_five_ultra
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 5 := by
  rcases known_edge_N_add_five_or_one_reflector_early_outcome_ultra
      hN hentry times hlive hnd with hclosed | hdead | hdamaged
  · exact hclosed
  · obtain ⟨D⟩ := hdead
    rcases D.N_add_three_or_forward hN times hlive hnd with
      hsmall | hforward
    · omega
    · obtain ⟨F⟩ := hforward
      exact F.all_run_distinct_le_N_add_five
        hN times hlive hnd
  · obtain ⟨D⟩ := hdamaged
    rcases D.N_add_three_or_forward hN times hlive hnd with
      hsmall | hforward
    · omega
    · obtain ⟨F⟩ := hforward
      exact F.toForwardContact.all_run_distinct_le_N_add_five
        hN times hlive hnd

/-- **Unconditional arbitrary-start coefficient-one bound at `N+6`.**
The first successful physical step exposes a known incoming edge.  Applying
the theorem above to the shifted run costs at most the original time-zero
vector and nothing else. -/
theorem state_law_linear_N_add_six_ultra
    (w : Wiring) (N : Nat)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  have hbound := arbitrary_start_distinct_le_succ_of_all_known_edge
    (w := w) (N := N) (cap := N + 5)
    (fun hentry localTimes hlocalLive hlocalNodup =>
      known_edge_all_run_distinct_le_N_add_five_ultra
        hN hentry localTimes hlocalLive hlocalNodup)
    start times hlive hnd
  omega

/-- **The exact raw track theorem.**  This closes `GeneralN.StateLaw` as it
is stated in `StateLaw.lean`: arbitrary finite wiring, arbitrary start and
arbitrary duplicate-free family of live sample times, uniformly in `N`. -/
theorem stateLaw_ultra : StateLaw := by
  intro w N hN start times hlive hnd
  apply state_law_linear_N_add_six_ultra
    w N hN start times hlive
  change (times.map
    (fun k => VectorCount.restrict N (tonguesAt w start k))).Nodup
  exact hnd

end GeneralN
