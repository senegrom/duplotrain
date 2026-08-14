import TrackCurveShrinkGlobal

/-!
# Four states in a two-endpoint self epoch

The curve-growth argument separates productive pivots into non-self merges
and self-pivots.  A self-pivot only proves that the next train curve is a
subcurve of the old one; by itself it does **not** prove that a whole epoch
has one fixed pair of endpoint switches.  This file therefore exposes that
remaining geometric obligation explicitly.

`RawSelfTwoEndpointEpoch` says that every productive event in the prefix is
a self-pivot and that its writer is one of two certified endpoint switches.
Under precisely that certificate, `raw_self_two_endpoint_epoch_four_cover`
proves that every restricted tongue vector in the prefix is one of the four
Gray corners obtained by flipping those two endpoint tongues.  The counting
corollary `raw_self_two_endpoint_epoch_distinct_le_four` is fully raw: it is
stated over `Wiring`, `stepN`, and arbitrary sampled times.

No recurrence, planarity, small-`N` enumeration, or unproved endpoint
extraction is used.  Consequently this file is a safe assembly interface:
a future curve argument may discharge the endpoint certificate, but the
certificate is not silently assumed to follow from self-pivotality alone.
-/

namespace GeneralN

/-- The four possible visible vectors obtained by changing only endpoint
switches `A` and `B` from the epoch's initial tongue state.  Repetitions are
harmless when `A = B` or an endpoint lies outside the visible range. -/
def twoWriterCorners (N : Nat) (base : Tongues) (A B : Nat) :
    List (List Bool) :=
  [VectorCount.restrict N base,
   VectorCount.restrict N (flipAt base A),
   VectorCount.restrict N (flipAt base B),
   VectorCount.restrict N (flipAt (flipAt base A) B)]

@[simp] theorem twoWriterCorners_length
    (N : Nat) (base : Tongues) (A B : Nat) :
    (twoWriterCorners N base A B).length = 4 := by
  simp [twoWriterCorners]

/-- A raw self-only prefix equipped with the exact fixed-endpoint carrier
needed by the four-state argument. -/
def RawSelfTwoEndpointEpoch
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (K A B : Nat) : Prop :=
  ∀ k, k < K → RawProductiveAt w N start k →
    RawCurveSelfAt w start k ∧
      (rawWriterAt w start k = A ∨ rawWriterAt w start k = B)

private theorem bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) :
    a = !b := by
  cases a <;> cases b <;> simp_all

/-- If a visible tongue assignment agrees with `base` outside `A` and `B`,
its restriction is one of the four explicit endpoint corners. -/
theorem restrict_mem_twoWriterCorners_of_agrees_outside
    {N A B : Nat} {base u : Tongues}
    (houtside : ∀ C, C < N → C ≠ A → C ≠ B → u C = base C) :
    VectorCount.restrict N u ∈ twoWriterCorners N base A B := by
  have restrict_eq_of_pointwise
      (v : Tongues) (hpoint : ∀ C, C < N → u C = v C) :
      VectorCount.restrict N u = VectorCount.restrict N v := by
    unfold VectorCount.restrict
    apply List.map_congr_left
    intro C hC
    exact hpoint C (List.mem_range.mp hC)
  by_cases hAB : A = B
  · subst B
    by_cases hA : u A = base A
    · have heq : VectorCount.restrict N u =
          VectorCount.restrict N base := by
        apply restrict_eq_of_pointwise
        intro C hC
        by_cases hCA : C = A
        · simpa [hCA] using hA
        · exact houtside C hC hCA hCA
      simp [twoWriterCorners, heq]
    · have hAflip : u A = !(base A) := bool_eq_not_of_ne hA
      have heq : VectorCount.restrict N u =
          VectorCount.restrict N (flipAt base A) := by
        apply restrict_eq_of_pointwise
        intro C hC
        by_cases hCA : C = A
        · subst C
          simpa [flipAt] using hAflip
        · simp [flipAt, hCA, houtside C hC hCA hCA]
      simp [twoWriterCorners, heq]
  · by_cases hA : u A = base A
    · by_cases hB : u B = base B
      · have heq : VectorCount.restrict N u =
            VectorCount.restrict N base := by
          apply restrict_eq_of_pointwise
          intro C hC
          by_cases hCA : C = A
          · simpa [hCA] using hA
          · by_cases hCB : C = B
            · simpa [hCB] using hB
            · exact houtside C hC hCA hCB
        simp [twoWriterCorners, heq]
      · have hBflip : u B = !(base B) := bool_eq_not_of_ne hB
        have heq : VectorCount.restrict N u =
            VectorCount.restrict N (flipAt base B) := by
          apply restrict_eq_of_pointwise
          intro C hC
          by_cases hCB : C = B
          · subst C
            simpa [flipAt] using hBflip
          · by_cases hCA : C = A
            · subst C
              simp [flipAt, hAB, hA]
            · simp [flipAt, hCB, houtside C hC hCA hCB]
        simp [twoWriterCorners, heq]
    · have hAflip : u A = !(base A) := bool_eq_not_of_ne hA
      by_cases hB : u B = base B
      · have heq : VectorCount.restrict N u =
            VectorCount.restrict N (flipAt base A) := by
          apply restrict_eq_of_pointwise
          intro C hC
          by_cases hCA : C = A
          · subst C
            simpa [flipAt] using hAflip
          · by_cases hCB : C = B
            · subst C
              simp [flipAt, Ne.symm hAB, hB]
            · simp [flipAt, hCA, houtside C hC hCA hCB]
        simp [twoWriterCorners, heq]
      · have hBflip : u B = !(base B) := bool_eq_not_of_ne hB
        have heq : VectorCount.restrict N u =
            VectorCount.restrict N (flipAt (flipAt base A) B) := by
          apply restrict_eq_of_pointwise
          intro C hC
          by_cases hCA : C = A
          · subst C
            simp [flipAt, hAB, hAflip]
          · by_cases hCB : C = B
            · subst C
              simp [flipAt, Ne.symm hAB, hBflip]
            · simp [flipAt, hCA, hCB, houtside C hC hCA hCB]
        simp [twoWriterCorners, heq]

/-- Every tongue outside the two certified endpoint writers remains at its
epoch-start value.  This is the raw one-coordinate-update statement. -/
theorem raw_two_endpoint_epoch_agrees_outside
    {w : Wiring} {N K A B : Nat} {start : Nat × Tongues}
    (hepoch : RawSelfTwoEndpointEpoch w N start K A B) :
    ∀ k, k ≤ K → ∀ C, C < N → C ≠ A → C ≠ B →
      (tonguesAt w start k) C = start.2 C := by
  intro k hk C hC hCA hCB
  apply raw_tongue_stable_before_writer hC start k
  intro j hj hprod
  have hjK : j < K := by omega
  rcases (hepoch j hjK hprod).2 with hwriter | hwriter
  · rw [hwriter]
    exact Ne.symm hCA
  · rw [hwriter]
    exact Ne.symm hCB

/-- **Raw self-epoch four-corner cover.**  Every time through the certified
self-only epoch lies in the explicit Gray square of its two endpoint
writers. -/
theorem raw_self_two_endpoint_epoch_four_cover
    {w : Wiring} {N K A B : Nat} {start : Nat × Tongues}
    (hepoch : RawSelfTwoEndpointEpoch w N start K A B) :
    ∀ k, k ≤ K →
      restrictedTonguesAt w N start k ∈
        twoWriterCorners N start.2 A B := by
  intro k hk
  apply restrict_mem_twoWriterCorners_of_agrees_outside
  intro C hC hCA hCB
  exact raw_two_endpoint_epoch_agrees_outside hepoch k hk C hC hCA hCB

/-- Any duplicate-free sample of visible vectors from a certified two-endpoint
self epoch has length at most four. -/
theorem raw_self_two_endpoint_epoch_distinct_le_four
    {w : Wiring} {N K A B : Nat} {start : Nat × Tongues}
    (hepoch : RawSelfTwoEndpointEpoch w N start K A B)
    {times : List Nat}
    (htimes : ∀ k ∈ times, k ≤ K)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 4 := by
  have hcover : NoveltyCoverOn w N start times [] 4 := by
    refine ⟨twoWriterCorners N start.2 A B, ?_, ?_⟩
    · simp
    · intro k hk
      simp only [List.nil_append]
      exact raw_self_two_endpoint_epoch_four_cover hepoch k (htimes k hk)
  simpa using noveltyCoverOn_distinct_count hcover hnd

end GeneralN
