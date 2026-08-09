import SelfEpochFour
import TrackCurveShrinkGlobal
import KoizumiFramePersistence

/-!
# Extracting the two endpoints of a self-pivot epoch

`TrackCurveShrinkGlobal` proves the geometric facts needed here directly in
the raw track language:

* the represented unmatched-branch writers on one selected train curve form
  a list of length at most two; and
* through a live interval containing only quiet moves and productive
  self-pivots, that endpoint-writer list can only shrink.

This file performs the final extraction.  It chooses the two writers from
the endpoint carrier at the start of the interval, proves that every
productive event writes one of them, and discharges the certificate exposed
by `SelfEpochFour`.  Consequently every such epoch contains at most four
distinct visible tongue vectors.

No recurrence, planarity, small-`N` enumeration, or additional track axiom is
used.
-/

namespace GeneralN

/-- Any list of length at most two is covered by two named values.  Empty and
singleton lists are padded by repetition. -/
private theorem list_length_le_two_cover
    {xs : List Nat} (hlen : xs.length ≤ 2) :
    ∃ A B, ∀ C, C ∈ xs → C = A ∨ C = B := by
  cases xs with
  | nil =>
      exact ⟨0, 0, by simp⟩
  | cons A rest =>
      cases rest with
      | nil =>
          exact ⟨A, A, by simp⟩
      | cons B tail =>
          cases tail with
          | nil =>
              exact ⟨A, B, by simp⟩
          | cons D tail =>
              simp only [List.length_cons] at hlen
              omega

/-- **Endpoint extraction.**  Every live raw prefix containing no productive
non-self pivot admits the exact fixed two-writer certificate consumed by
`SelfEpochFour`.

The two writers are selected from the unmatched-branch endpoint carrier of
the train curve at raw time zero.  Current writers belong to the current
carrier, and carrier monotonicity puts them back in that fixed initial list.
-/
theorem rawSelfEpoch_extract_two_endpoints
    {w : Wiring} {N K : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hself : ∀ k, k < K → RawProductiveAt w N start k →
      RawCurveSelfAt w start k) :
    ∃ A B, RawSelfTwoEndpointEpoch w N start K A B := by
  have hcapacity :=
    rawFiniteCurveEndpointWritersAt_length_le_two w N start 0
  obtain ⟨A, B, hcover⟩ := list_length_le_two_cover hcapacity
  refine ⟨A, B, ?_⟩
  intro k hk hprod
  have htrainSelf : RawTrainCurveSelfAt w start k := by
    simpa [RawTrainCurveSelfAt, RawCurveSelfAt, rawWriterAt,
      rawEntryAt, tonguesAt] using hself k hk hprod
  refine ⟨htrainSelf, hcover (rawWriterAt w start k) ?_⟩
  have hcurrent := rawProductiveAt_writer_mem_endpointWritersAt hN hprod
  exact rawSelfOnlyEpoch_endpointWriters_subset
    hN start K hlive hself k (by omega)
      (rawWriterAt w start k) hcurrent

/-- The geometric endpoint extraction discharges the certificate in
`SelfEpochFour`: a self-only epoch has at most four distinct visible tongue
vectors. -/
theorem rawSelfEpoch_distinct_le_four
    {w : Wiring} {N K : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hself : ∀ k, k < K → RawProductiveAt w N start k →
      RawCurveSelfAt w start k)
    {times : List Nat}
    (htimes : ∀ k ∈ times, k ≤ K)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 4 := by
  obtain ⟨A, B, hepoch⟩ :=
    rawSelfEpoch_extract_two_endpoints hN start hlive hself
  exact raw_self_two_endpoint_epoch_distinct_le_four
    hepoch htimes hnd

end GeneralN
