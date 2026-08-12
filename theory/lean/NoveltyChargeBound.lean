import MellitGlobalIncompatibleClosure

/-!
# Novelty charging by first writes and Gray phases

This file develops an alternative quantitative invariant directly in the
raw `Wiring` / `stepN` language.  First productive writes are charged to
their switches.  Once a compatible manufactured-reflector pair has been
reached, its four Gray corners do **not** cost four further vectors: the
initial corner is already the exceptional contact vector of the first
turnaround.  Hence the pair costs only three additional vectors.

The hypotheses below have the following raw-track provenance.

* `hN` is the literal finite-`N` port bound on `Wiring.link`.
* `PathGrooves` and `Avoids` are finite certificates about the passages and
  switch actions manufactured by the physical first/second-repeat argument.
* `hreach` is a literal `stepN` equality.  The canonical endpoint equality
  used below is derived from `PhysicalTrace.sound` and the forced retrace.

No echo-machine assumption occurs here.  In particular, the token calculus
and `EdgeReversal.nextCell_update` require `Echo.IsRun`; the sparse raw
overwrite trace used for arbitrary `Wiring` runs does not currently provide
that recurrence.  Importing either invariant into this argument without a
compiler theorem would therefore add an underived hypothesis.

The theorems in this file improve the compatible-pair branch to `N + 5`.
They do not prove `GeneralN.StateLaw`; the incompatible/protected-repair
branch of the global argument remains separate.
-/

namespace GeneralN

/-- The complete canonical manufacturing journey really ends at the
reflector's activated state.  This packages only raw `stepN` facts and is
useful for identifying the first-turnaround contact vector with the initial
corner of the following reflector pair. -/
theorem ManufacturedReflector.manufacturing_journey_reaches_activated
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState) :
    stepN w (A.exploration.length + A.runway.length + 1)
      (g, A.baseState) = some (e, A.activatedState) := by
  have hback :
      stepN w (A.runway.length + 1) A.preReturn =
        some (e, A.activatedState) := by
    have htrace := physicalTrace_contact_retraces_prefix
      A.runway_trace (A.runway_grooved hpaths)
      A.entryEdge A.return_arrive_mouth
    simpa [reversePassages_length] using htrace.sound
  have hlen :
      A.exploration.length + A.runway.length + 1 =
        A.exploration.length + (A.runway.length + 1) := by
    omega
  rw [hlen, stepN_add, A.exploration_trace.sound]
  exact hback

/-- **The historical Gray-corner overlap.**

Suppose an arbitrary raw run reaches a compatible manufactured-reflector
pair at time `K`.  If all selected pre-`K` vectors and the reached pair's
starting vector are historical, then the entire selected trajectory needs
only three fresh vectors: the other three corners of the Gray square.

This is the injective charge missing from the four-corner tail estimate: the
starting corner is charged once, to the first turnaround, and is never
charged again to the tail. -/
theorem manufactured_pair_history_and_tail_three_novelty_cover_of_start_mem
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    {start : Nat × Tongues} {K : Nat}
    (hreach : stepN w K start = some (g, state))
    (times : List Nat) (history : List (List Bool))
    (hhistory : forall j, j ∈ times -> j < K ->
      restrictedTonguesAt w N start j ∈ history)
    (hstart : VectorCount.restrict N state ∈ history) :
    NoveltyCoverOn w N start times history 3 := by
  let aState := A.toSupported.action.apply state
  let baState := B.toSupported.action.apply aState
  let abaState := A.toSupported.action.apply baState
  refine ⟨[VectorCount.restrict N aState,
      VectorCount.restrict N baState,
      VectorCount.restrict N abaState], by simp, ?_⟩
  intro j hj
  by_cases hjK : j < K
  · exact List.mem_append_left _ (hhistory j hj hjK)
  · have htail : K ≤ j := by omega
    have hphase := manufactured_pair_absolute_four_phase_tongues
      A B state hA hB hAB hBA hreach htail
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hphase
    rcases hphase with hstate | ha | hba | haba
    · apply List.mem_append_left
      simpa [restrictedTonguesAt, hstate] using hstart
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, aState, ha]
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, aState, baState, hba]
    · apply List.mem_append_right history
      simp [restrictedTonguesAt, aState, baState, abaState, haba]

/-- **First turnaround plus compatible pair: four, not five, repeated-writer
novelties.**

The first simple exploration is charged to first writers.  Its forced return
has at most one exceptional vector, the activated state of `P`.  Determinism
identifies that vector with the reached pair's initial corner, so the pair
adds only its other three Gray corners. -/
theorem first_turnaround_then_compatible_pair_repeatedWriterNovelty_le_four
    {w : Wiring} {h g e N : Nat}
    (P : ManufacturedReflector w h g)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hPpaths : PathGrooves P.toSupported.paths P.activatedState)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (hreach : stepN w
      (P.exploration.length + P.runway.length + 1)
      (h, P.baseState) = some (g, state)) :
    forall H,
      (rawRepeatedWriterNovelTimes w N (h, P.baseState) H).length ≤ 4 := by
  have hcanonical := P.manufacturing_journey_reaches_activated hPpaths
  have hstate : state = P.activatedState := by
    have hpairs : (g, state) = (g, P.activatedState) :=
      Option.some.inj (hreach.symm.trans hcanonical)
    exact congrArg Prod.snd hpairs
  intro H
  let J := P.exploration.length + P.runway.length + 1
  let start : Nat × Tongues := (h, P.baseState)
  by_cases hHJ : H ≤ J
  · have hmono := rawRepeatedWriterNovelTimes_length_mono
      (w := w) (N := N) (start := start) hHJ
    have hone := P.manufacturing_repeatedWriterNovelty_le_one hN hPpaths
    dsimp [J, start] at hmono
    omega
  · have hJH : J ≤ H := by omega
    let times := rawRepeatedWriterPostTimes w N start H
    let history := rawFirstWriterHistory w N start H
    have hexplorationH : P.exploration.length ≤ H := by
      dsimp [J] at hJH
      omega
    have hpair : NoveltyCoverOn w N start times
        (history ++ [VectorCount.restrict N P.activatedState]) 3 := by
      apply manufactured_pair_history_and_tail_three_novelty_cover_of_start_mem
        A B state hA hB hAB hBA
          (start := start) (K := J)
      · simpa [J, start] using hreach
      · intro j hj hjJ
        have hjJourney :
            j ≤ P.exploration.length + P.runway.length + 1 := by
          dsimp [J] at hjJ
          omega
        have hm := P.manufacturing_journey_mem_rawHistory_one_extra
          (N := N) (K := H) hPpaths hexplorationH j hjJourney
        simpa [start, history] using hm
      · simp [hstate]
    obtain ⟨pairFresh, hpairFresh, hpairMem⟩ := hpair
    have hcover : NoveltyCoverOn w N start times history 4 := by
      refine ⟨VectorCount.restrict N P.activatedState :: pairFresh,
        ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro j hj
        have hm := hpairMem j hj
        simpa [List.append_assoc] using hm
    have hnew : forall j, j ∈ times ->
        restrictedTonguesAt w N start j ∉ history := by
      simpa [times, history] using
        (repeatedWriterPostTimes_avoid_firstHistory hN start H)
    have hnd :
        (times.map (restrictedTonguesAt w N start)).Nodup := by
      dsimp [times]
      rw [map_repeatedWriterPostTimes_eq_fresh]
      exact rawRepeatedWriterFresh_nodup w N start H
    have hcount := noveltyCoverOn_fresh_distinct_count hcover hnew hnd
    simpa [times, rawRepeatedWriterPostTimes, start] using hcount

end GeneralN
