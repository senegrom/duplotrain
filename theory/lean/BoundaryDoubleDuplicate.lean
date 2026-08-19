import BoundaryAbsentSecondWriter

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
    (hstay : O.next = O.middle) :
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
      exact R.runway_boundary_repeated
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
          (occurrence_pre_mem_doubleReducedTimes O (by omega))
        calc
          f O.before.length = f (O.before.length + 1) := hoccurrence
          _ = f R.runway.length := by rw [hoverlap]
          _ = f (R.runway.length + 1) := hcanonical
          _ = v := htv
      · apply put R.runway.length
          (canonical_pre_mem_doubleReducedTimes O hoverlap)
        exact hcanonical.trans htv
    · by_cases htOccurrence : t = O.before.length + 1
      · subst t
        by_cases hoverlap : O.before.length = R.runway.length + 1
        · apply put R.runway.length
            (canonical_pre_mem_doubleReducedTimes O (by omega))
          calc
            f R.runway.length = f (R.runway.length + 1) := hcanonical
            _ = f O.before.length := by rw [hoverlap]
            _ = f (O.before.length + 1) := hoccurrence
            _ = v := htv
        · apply put O.before.length
            (occurrence_pre_mem_doubleReducedTimes O hoverlap)
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
def InitialEntryWriterOccurrence.doubleReducedTwoHistory
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
    (hstay : O.next = O.middle) :
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
      hstay
    simp [ManufacturedReflector.sharpConstructionHistory]
  constructor
  · apply List.mem_append_left
    exact List.mem_cons_self
  · intro x hx
    rcases hx with hA | hB
    · apply List.mem_append_left
      exact O.sharp_mem_doubleReducedBoundaryHistory
        original hstay x hA
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

/-- If the flip reflector's omitted action mouth is not a productive first
writer of the second construction, that unused coordinate removes the final
surcharge.  Thus the history containing the arbitrary boundary vector and
both complete constructions has size at most `N + 2`. -/
theorem InitialEntryWriterOccurrence.doubleReducedTwoHistory_length_le_N_add_two_of_action_absent
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
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
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (haction : R.actionSwitch ∉ B.constructionFirstWriterSwitches N) :
    (O.doubleReducedTwoHistory B N original).length ≤ N + 2 := by
  have hboundary : VectorCount.restrict N
      (ManufacturedReflector.flip R).activatedState ∈
      B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hactionLt : R.actionSwitch < N := by
    have hlt :=
      (ManufacturedReflector.flip R).exploration_trace.switch_lt
        hN (R.mouth, R.firstArm) (by
          simp [ManufacturedReflector.exploration])
    simpa [passageSwitch,
      ManufacturedFlipReflector.actionSwitch] using hlt
  have hactionNot : R.actionSwitch ∉
      (ManufacturedReflector.flip R).reusableSwitches := by
    intro hmem
    change R.actionSwitch ∈
      ((R.runway ++ R.candy).map passageSwitch) at hmem
    obtain ⟨passage, hpassage, hswitch⟩ := List.mem_map.mp hmem
    rcases List.mem_append.mp hpassage with hrunway | hcandy
    · exact (R.support_foreign R.runway (by simp)
        passage hrunway) hswitch
    · exact (R.support_foreign R.candy (by simp)
        passage hcandy) hswitch
  have hcharge :=
    (ManufacturedReflector.flip R).reusable_add_second_first_writers_add_reserved_le
      hN B hbaseGrooves hpreGrooves
        hactionLt hactionNot haction
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

/-- If the unchanged occurrence is at the canonical duplicate position,
then it is literally the flip reflector's facing mouth.  Hence its switch is
the omitted action switch. -/
theorem InitialEntryWriterOccurrence.switch_eq_action_of_before_length_eq_runway
    {w : Wiring} {g e k0 : Nat}
    {R : ManufacturedFlipReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0
      (ManufacturedReflector.flip R))
    (hsame : O.before.length = R.runway.length) :
    k0 = R.actionSwitch := by
  have hsplit := O.split
  change R.runway ++ (R.mouth, R.firstArm) :: R.candy =
      O.before ++ (O.p, O.x) :: O.after at hsplit
  have hdrop := congrArg (List.drop R.runway.length) hsplit
  have hhead : (R.mouth, R.firstArm) = (O.p, O.x) := by
    simpa [hsame] using congrArg List.head? hdrop
  have hp : O.p = R.mouth := (Prod.mk.inj hhead).1.symm
  calc
    k0 = passageSwitch (O.p, O.x) := O.switch_eq.symm
    _ = O.p / 3 := rfl
    _ = R.mouth / 3 := by rw [hp]
    _ = R.actionSwitch := by
      rfl

/-- The facing action mouth of a flip reflector is not part of its reusable
support. -/
theorem ManufacturedFlipReflector.action_not_mem_reusable
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e) :
    R.actionSwitch ∉
      (ManufacturedReflector.flip R).reusableSwitches := by
  intro hmem
  change R.actionSwitch ∈
    ((R.runway ++ R.candy).map passageSwitch) at hmem
  obtain ⟨passage, hpassage, hswitch⟩ := List.mem_map.mp hmem
  rcases List.mem_append.mp hpassage with hrunway | hcandy
  · exact (R.support_foreign R.runway (by simp)
      passage hrunway) hswitch
  · exact (R.support_foreign R.candy (by simp)
      passage hcandy) hswitch

/-- The omitted action mouth is one of the counted finite switches. -/
theorem ManufacturedFlipReflector.action_lt
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e) :
    R.actionSwitch < N := by
  have hlt :=
    (ManufacturedReflector.flip R).exploration_trace.switch_lt
      hN (R.mouth, R.firstArm) (by
        simp [ManufacturedReflector.exploration])
  simpa [passageSwitch,
    ManufacturedFlipReflector.actionSwitch] using hlt

end GeneralN
