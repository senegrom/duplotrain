import StateLawTwoSixUltra
import TwoHistoryUnionCharge

/-!
# Two independent repetitions at the productive boundary

For a flip reflector, the facing mouth gives the canonical repeated
construction vector.  If the initially written switch is encountered at a
different unchanged passage, that passage gives a second repetition.  This
file removes one post-time from each repetition and inserts the arbitrary
pre-passage vector.  The resulting history still covers the whole first
manufacture but has exactly the same size as the ordinary one-duplicate
`sharpHistoryCore`.

This is a general-`N` list theorem over the raw trace; it does not assume the
state law or any finite-instance calculation.
-/

namespace GeneralN

private theorem boundary_flip_runway_repeated
    {w : Wiring} {g e N : Nat}
    (R : ManufacturedFlipReflector w g e) :
    restrictedTonguesAt w N (g, R.base) R.runway.length =
      restrictedTonguesAt w N (g, R.base) (R.runway.length + 1) := by
  have hAtRunway :
      tonguesAt w (g, R.base) R.runway.length = R.mouthState := by
    simp [tonguesAt, R.runwayTrace.sound]
  have hstepOne :
      ∃ q, stepN w 1 (R.mouth, R.mouthState) =
        some (q, R.mouthState) := by
    have htrace := R.candyTrace
    cases htrace with
    | @cons p x q u v passages finish harrive hlink tail =>
        have hv : v = R.mouthState := by
          unfold arrive at harrive
          rw [if_pos R.mouth_is_stem] at harrive
          exact (Prod.mk.inj harrive).2.symm
        refine ⟨q, ?_⟩
        simp [stepN, step, harrive, hlink, hv]
  have hAtNext :
      tonguesAt w (g, R.base) (R.runway.length + 1) =
        R.mouthState := by
    have hlive :
        ∃ finish, stepN w 1 (R.mouth, R.mouthState) = some finish := by
      obtain ⟨q, hq⟩ := hstepOne
      exact ⟨(q, R.mouthState), hq⟩
    have hshift := tonguesAt_add_of_reaches
      (K := R.runway.length) (d := 1) R.runwayTrace.sound hlive
    obtain ⟨q, hq⟩ := hstepOne
    rw [hshift]
    simp [tonguesAt, hq]
  simp only [restrictedTonguesAt]
  rw [hAtRunway, hAtNext]

/-- The time indices left after deleting the post-time of the canonical
mouth repetition and the post-time of a distinct unchanged occurrence. -/
def InitialEntryWriterOccurrence.doubleReducedTimes
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R)) : List Nat :=
  ((List.range
      ((ManufacturedReflector.flip R).exploration.length + 1)).erase
        (R.runway.length + 1)).erase (O.before.length + 1)

/-- Replace the two deleted repeated occurrences by the arbitrary boundary
vector. -/
def InitialEntryWriterOccurrence.doubleReducedBoundaryHistory
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (N : Nat) (original : Tongues) : List (List Bool) :=
  VectorCount.restrict N original ::
    (O.doubleReducedTimes.map
      (restrictedTonguesAt w N (g, (ManufacturedReflector.flip R).baseState)) ++
      [VectorCount.restrict N
        (ManufacturedReflector.flip R).activatedState])

private theorem mem_doubleReducedTimes_of_ne
    {w : Wiring} {g e k0 t : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (ht : t < (ManufacturedReflector.flip R).exploration.length + 1)
    (hcanonical : t ≠ R.runway.length + 1)
    (hoccurrence : t ≠ O.before.length + 1) :
    t ∈ O.doubleReducedTimes := by
  unfold InitialEntryWriterOccurrence.doubleReducedTimes
  apply (List.mem_erase_of_ne hoccurrence).mpr
  apply (List.mem_erase_of_ne hcanonical).mpr
  exact List.mem_range.mpr ht

private theorem canonical_pre_mem_doubleReducedTimes
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (hdifferent : O.before.length ≠ R.runway.length)
    (hnotOccurrencePost : R.runway.length ≠ O.before.length + 1) :
    R.runway.length ∈ O.doubleReducedTimes := by
  apply mem_doubleReducedTimes_of_ne O
  · simp [ManufacturedReflector.exploration]
    omega
  · omega
  · exact hnotOccurrencePost

private theorem occurrence_pre_mem_doubleReducedTimes
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (hdifferent : O.before.length ≠ R.runway.length)
    (hnotCanonicalPost : O.before.length ≠ R.runway.length + 1) :
    O.before.length ∈ O.doubleReducedTimes := by
  apply mem_doubleReducedTimes_of_ne O
  · rw [O.split]
    simp
    omega
  · exact hnotCanonicalPost
  · omega

/-- Both erasures are genuine and distinct, so the remaining time list has
exactly `exploration.length - 1` entries. -/
theorem InitialEntryWriterOccurrence.doubleReducedTimes_length
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (hdifferent : O.before.length ≠ R.runway.length) :
    O.doubleReducedTimes.length =
      (ManufacturedReflector.flip R).exploration.length - 1 := by
  have hcanonical : R.runway.length + 1 ∈
      List.range ((ManufacturedReflector.flip R).exploration.length + 1) := by
    apply List.mem_range.mpr
    simp [ManufacturedReflector.exploration]
  have hoccurrenceRange : O.before.length + 1 ∈
      List.range ((ManufacturedReflector.flip R).exploration.length + 1) := by
    apply List.mem_range.mpr
    rw [O.split]
    simp
  have hoccurrenceAfter : O.before.length + 1 ∈
      (List.range
        ((ManufacturedReflector.flip R).exploration.length + 1)).erase
          (R.runway.length + 1) := by
    apply (List.mem_erase_of_ne (by omega)).mpr
    exact hoccurrenceRange
  unfold InitialEntryWriterOccurrence.doubleReducedTimes
  rw [List.length_erase_of_mem hoccurrenceAfter,
    List.length_erase_of_mem hcanonical, List.length_range]
  omega

/-- Every vector in the first sharp construction remains represented after
the two post-times are deleted. -/
theorem InitialEntryWriterOccurrence.sharp_mem_doubleReducedBoundaryHistory
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (original : Tongues)
    (hstay : O.next = O.middle)
    (hdifferent : O.before.length ≠ R.runway.length) :
    ∀ v,
      v ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N →
      v ∈ O.doubleReducedBoundaryHistory N original := by
  intro v hv
  unfold ManufacturedReflector.sharpConstructionHistory at hv
  rcases List.mem_append.mp hv with hv | hv
  · obtain ⟨t, ht, htv⟩ := List.mem_map.mp hv
    have htBound :
        t < (ManufacturedReflector.flip R).exploration.length + 1 :=
      List.mem_range.mp ht
    let f := restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).baseState)
    have hcanonical : f R.runway.length = f (R.runway.length + 1) := by
      exact boundary_flip_runway_repeated R
    have hoccurrence : f O.before.length = f (O.before.length + 1) := by
      exact entry_writer_unchanged_gives_consecutive_duplicate
        (N := N) (ManufacturedReflector.flip R) O hstay
    have put (s : Nat) (hs : s ∈ O.doubleReducedTimes)
        (heq : f s = v) :
        v ∈ O.doubleReducedBoundaryHistory N original := by
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨s, hs, heq⟩
    by_cases htCanonical : t = R.runway.length + 1
    · subst t
      by_cases hoverlap : R.runway.length = O.before.length + 1
      · apply put O.before.length
          (occurrence_pre_mem_doubleReducedTimes O hdifferent (by omega))
        calc
          f O.before.length = f (O.before.length + 1) := hoccurrence
          _ = f R.runway.length := by rw [hoverlap]
          _ = f (R.runway.length + 1) := hcanonical
          _ = v := htv
      · apply put R.runway.length
          (canonical_pre_mem_doubleReducedTimes O hdifferent hoverlap)
        exact hcanonical.trans htv
    · by_cases htOccurrence : t = O.before.length + 1
      · subst t
        by_cases hoverlap : O.before.length = R.runway.length + 1
        · apply put R.runway.length
            (canonical_pre_mem_doubleReducedTimes O hdifferent (by omega))
          calc
            f R.runway.length = f (R.runway.length + 1) := hcanonical
            _ = f O.before.length := by rw [hoverlap]
            _ = f (O.before.length + 1) := hoccurrence
            _ = v := htv
        · apply put O.before.length
            (occurrence_pre_mem_doubleReducedTimes O hdifferent hoverlap)
          exact hoccurrence.trans htv
      · apply put t
          (mem_doubleReducedTimes_of_ne O htBound
            htCanonical htOccurrence)
        exact htv
  · apply List.mem_cons_of_mem
    apply List.mem_append_right
    simpa using hv

/-- The arbitrary boundary vector plus the complete first manufacture costs
only `exploration.length + 1` entries when the two repetitions are distinct.
This is exactly the size of the ordinary one-duplicate sharp core. -/
theorem InitialEntryWriterOccurrence.doubleReducedBoundaryHistory_length
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (original : Tongues)
    (hdifferent : O.before.length ≠ R.runway.length) :
    (O.doubleReducedBoundaryHistory N original).length =
      (ManufacturedReflector.flip R).exploration.length + 1 := by
  unfold InitialEntryWriterOccurrence.doubleReducedBoundaryHistory
  rw [List.length_cons, List.length_append, List.length_map,
    O.doubleReducedTimes_length hdifferent]
  simp
  have hpositive :
      0 < (ManufacturedReflector.flip R).exploration.length := by
    simp [ManufacturedReflector.exploration]
    omega
  omega

/-- Add the second reflector's first-writer history, erasing the shared
activation boundary once. -/
noncomputable def InitialEntryWriterOccurrence.doubleReducedTwoHistory
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (B : ManufacturedReflector w e g)
    (N : Nat) (original : Tongues) : List (List Bool) :=
  O.doubleReducedBoundaryHistory N original ++
    (B.writerConstructionHistory N).erase
      (VectorCount.restrict N
        (ManufacturedReflector.flip R).activatedState)

/-- The doubly-reduced union represents the arbitrary boundary vector and
both complete manufacturing journeys. -/
theorem InitialEntryWriterOccurrence.mem_doubleReducedTwoHistory
    {w : Wiring} {N g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hstay : O.next = O.middle)
    (hdifferent : O.before.length ≠ R.runway.length)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState) :
    VectorCount.restrict N original ∈
        O.doubleReducedTwoHistory B N original ∧
      (∀ x,
        x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N ∨
          x ∈ B.sharpConstructionHistory N →
        x ∈ O.doubleReducedTwoHistory B N original) := by
  have hAactivated :
      VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState ∈
        O.doubleReducedBoundaryHistory N original := by
    apply O.sharp_mem_doubleReducedBoundaryHistory original
      hstay hdifferent
    simp [ManufacturedReflector.sharpConstructionHistory]
  constructor
  · apply List.mem_append_left
    exact List.mem_cons_self
  · intro x hx
    rcases hx with hA | hB
    · apply List.mem_append_left
      exact O.sharp_mem_doubleReducedBoundaryHistory
        original hstay hdifferent x hA
    · have hwriter := B.mem_writerConstructionHistory_of_mem_sharp hB
      by_cases hboundary :
          x = VectorCount.restrict N
            (ManufacturedReflector.flip R).activatedState
      · subst x
        exact List.mem_append_left _ hAactivated
      · apply List.mem_append_right
        exact (List.mem_erase_of_ne hboundary).mpr hwriter

/-- Exact coefficient-one size of the doubly-reduced two-journey history.
The reusable support of a flip reflector omits precisely its facing mouth,
so its exploration has one more passage than `reusableSwitches`; the usual
disjoint-coordinate charge then gives `N+3`. -/
theorem InitialEntryWriterOccurrence.doubleReducedTwoHistory_length_le_N_add_three
    {w : Wiring} {N g e k0 : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hdifferent : O.before.length ≠ R.runway.length)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2) :
    (O.doubleReducedTwoHistory B N original).length ≤ N + 3 := by
  have hboundary : VectorCount.restrict N
      (ManufacturedReflector.flip R).activatedState ∈
      B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    (ManufacturedReflector.flip R).reusable_add_second_first_writers_le
    hN B hbaseGrooves hpreGrooves
  have hexploration :
      (ManufacturedReflector.flip R).exploration.length =
        (ManufacturedReflector.flip R).reusableSwitches.length + 1 := by
    simp [ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
    omega
  unfold InitialEntryWriterOccurrence.doubleReducedTwoHistory
  rw [List.length_append, List.length_erase_of_mem hboundary,
    O.doubleReducedBoundaryHistory_length original hdifferent,
    B.writerConstructionHistory_length]
  omega

end GeneralN
