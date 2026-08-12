import TrackFiniteAlternation

/-!
# The sharp `N+4` state-law target

This file states the sharp target directly over raw `Wiring` and `stepN`.
It also records the coefficient-one amortized novelty statement which is
exactly sufficient for that target.  Neither proposition is asserted here;
the proved theorem is the reduction from the amortized statement to the raw
track statement.
-/

namespace GeneralN

/-- **THE SHARP STATE-LAW TARGET.**  A single train on any raw lazy-point
wiring with `N` switches visits at most `N+4` pairwise-distinct restricted
tongue vectors. -/
def StateLawNAddFour : Prop :=
  forall (w : Wiring) (N : Nat),
    (forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) ->
    forall (start : Nat × Tongues) (times : List Nat),
      (forall k, k ∈ times -> (stepN w k start).isSome) ->
      (times.map (fun k => VectorCount.restrict N
        ((stepN w k start).getD start).2)).Nodup ->
      times.length <= N + 4

/-- The amortized novelty formulation of the sharp target.  First productive
writers and globally novel repeated writers share one budget: every repeated
novelty beyond the first three must be paid for by an ambient switch which
has not occurred as a first writer. -/
def AmortizedNoveltyNAddThree : Prop :=
  forall (w : Wiring) (N : Nat),
    (forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) ->
    forall (start : Nat × Tongues) (K : Nat),
      (rawFirstWriterTimes w N start K).length +
          (rawRepeatedWriterNovelTimes w N start K).length <= N + 3

/-- Exact finite bookkeeping for the amortized budget.  Unlike the older
`N + B + 1` theorem, this keeps the actual number of first writers instead
of replacing it by the coarse upper bound `N`. -/
theorem distinct_samples_le_of_amortized_novelty
    (w : Wiring) (N : Nat)
    (_hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hbudget :
      (rawFirstWriterTimes w N start K).length +
          (rawRepeatedWriterNovelTimes w N start K).length <= N + 3)
    (times : List Nat)
    (htimes : forall k, k ∈ times -> k <= K)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= N + 4 := by
  let history := rawFirstWriterHistory w N start K
  let fresh := rawRepeatedWriterFresh w N start K
  have hhistory : history.length =
      (rawFirstWriterTimes w N start K).length + 1 := by
    simp [history, rawFirstWriterHistory]
  have hfresh : fresh.length =
      (rawRepeatedWriterNovelTimes w N start K).length := by
    simp [fresh, rawRepeatedWriterFresh]
  have hcover : NoveltyCoverOn w N start times history fresh.length := by
    refine ⟨fresh, Nat.le_refl _, ?_⟩
    intro k hk
    exact restrictedTonguesAt_mem_finite_writer_cover
      w N start K k (htimes k hk)
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  omega

/-- The amortized novelty law proves the exact raw `N+4` statement, for
arbitrary starts and without a known-incoming-edge assumption. -/
theorem stateLawNAddFour_of_amortizedNovelty
    (hamortized : AmortizedNoveltyNAddThree) : StateLawNAddFour := by
  intro w N hN start times _hlive hnd
  let K := maxRawTime times
  have htimes : forall k, k ∈ times -> k <= K := by
    intro k hk
    exact le_maxRawTime_of_mem hk
  have hnd' : (times.map
      (restrictedTonguesAt w N start)).Nodup := by
    change (times.map (fun k => VectorCount.restrict N
      ((stepN w k start).getD start).2)).Nodup
    exact hnd
  exact distinct_samples_le_of_amortized_novelty
    w N hN start K (hamortized w N hN start K)
      times htimes hnd'

/-- The sharp target strictly strengthens the already proved `N+6`
`StateLaw`. -/
theorem stateLaw_of_stateLawNAddFour
    (hsharp : StateLawNAddFour) : StateLaw := by
  intro w N hN start times hlive hnd
  have hnd' : (times.map (fun k => VectorCount.restrict N
      ((stepN w k start).getD start).2)).Nodup := by
    change (times.map (restrictedTonguesAt w N start)).Nodup
    exact hnd
  have hbound := hsharp w N hN start times hlive hnd'
  omega

end GeneralN
