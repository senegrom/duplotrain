import TwoHistoryUnionCharge

/-!
# Reserving coordinates in a shared construction history

These counting facts concern the two constructions themselves. They do not
require an arbitrary initial vector or any boundary-saturation theorem.
-/

namespace GeneralN

/-- Any duplicate-free list of unoccupied coordinates can be charged at
once. The one- and two-coordinate savings are instances of this lemma. -/
theorem ManufacturedReflector.reusable_add_second_first_writers_add_reserved_list_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e) (B : ManufacturedReflector w e g)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves A.toSupported.paths B.preReturn.2)
    (reserved : List Nat) (hreserved : reserved.Nodup)
    (hbound : ∀ j ∈ reserved, j < N)
    (hfree : ∀ j ∈ reserved,
      j ∉ A.reusableSwitches ∧ j ∉ B.constructionFirstWriterSwitches N) :
    A.reusableSwitches.length +
      (rawFirstWriterTimes w N (e, B.baseState) B.exploration.length).length +
        reserved.length ≤ N := by
  obtain ⟨hused, husedLt⟩ := A.sharedConstructionCoordinates hN B hbaseGrooves hpreGrooves
  have hdisjoint : ∀ r ∈ reserved,
      ∀ j ∈ A.reusableSwitches ++ B.constructionFirstWriterSwitches N, r ≠ j := by
    intro r hr j hj heq
    subst j
    rcases List.mem_append.mp hj with h | h
    · exact (hfree r hr).1 h
    · exact (hfree r hr).2 h
  have hnd := List.nodup_append.mpr ⟨hreserved, hused, hdisjoint⟩
  have hlt : ∀ j ∈ reserved ++
      (A.reusableSwitches ++ B.constructionFirstWriterSwitches N), j < N := by
    intro j hj
    rcases List.mem_append.mp hj with h | h
    · exact hbound j h
    · exact husedLt j h
  have hcount := nodup_nat_lt_length hnd hlt
  simpa [ManufacturedReflector.constructionFirstWriterSwitches,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcount

/-- Reserving `k0` outside both the old reusable support and the second
construction's productive first writers strengthens the coefficient-one
coordinate charge by exactly one. -/
theorem ManufacturedReflector.reusable_add_second_first_writers_add_reserved_le
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentA : Not (List.Mem k0 A.reusableSwitches))
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N))) :
    A.reusableSwitches.length +
        (rawFirstWriterTimes w N (e, B.baseState)
          B.exploration.length).length + 1 <= N := by
  simpa using A.reusable_add_second_first_writers_add_reserved_list_le
    hN B hbaseGrooves hpreGrooves [k0] (by simp)
    (by simpa using hk0) (by
      intro j hj
      have heq : j = k0 := List.mem_singleton.mp hj
      subst j
      exact ⟨habsentA, habsentB⟩)

/-- Two distinct switches outside both the old reusable support and the
second construction's productive first writers buy two units in the same
coordinate charge. -/
theorem ManufacturedReflector.reusable_add_second_first_writers_add_two_reserved_le
    {w : Wiring} {N g e r1 r2 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves A.toSupported.paths B.preReturn.2)
    (hr1 : r1 < N) (hr2 : r2 < N) (hne : r1 ≠ r2)
    (habsentA1 : r1 ∉ A.reusableSwitches)
    (habsentB1 : r1 ∉ B.constructionFirstWriterSwitches N)
    (habsentA2 : r2 ∉ A.reusableSwitches)
    (habsentB2 : r2 ∉ B.constructionFirstWriterSwitches N) :
    A.reusableSwitches.length +
        (rawFirstWriterTimes w N (e, B.baseState)
          B.exploration.length).length + 2 ≤ N := by
  have hcount := A.reusable_add_second_first_writers_add_reserved_list_le
    hN B hbaseGrooves hpreGrooves [r1, r2] (by simp [hne])
    (by simpa using And.intro hr1 hr2)
    (by simpa using And.intro (And.intro habsentA1 habsentB1) (And.intro habsentA2 habsentB2))
  simpa using hcount

/-- One unused coordinate lowers the canonical two-construction history
from `N+3` to `N+2`, leaving room for two fresh repair-tail vectors. -/
theorem ManufacturedReflector.preservedTwoHistoryCore_length_le_N_add_two_of_reserved
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentA : Not (List.Mem k0 A.reusableSwitches))
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N))) :
    (A.preservedTwoHistoryCore B N).length <= N + 2 := by
  have hboundary :
      VectorCount.restrict N A.activatedState ∈
        B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    A.reusable_add_second_first_writers_add_reserved_le
      hN B hbaseGrooves hpreGrooves hk0 habsentA habsentB
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

/-- Two unused coordinates lower the canonical two-construction history
to `N+1`. Kept as a specialization for the historical boundary proof. -/
theorem ManufacturedReflector.preservedTwoHistoryCore_length_le_N_add_one_of_two_reserved
    {w : Wiring} {N g e r1 r2 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves A.toSupported.paths B.preReturn.2)
    (hr1 : r1 < N) (hr2 : r2 < N) (hne : r1 ≠ r2)
    (habsentA1 : r1 ∉ A.reusableSwitches)
    (habsentB1 : r1 ∉ B.constructionFirstWriterSwitches N)
    (habsentA2 : r2 ∉ A.reusableSwitches)
    (habsentB2 : r2 ∉ B.constructionFirstWriterSwitches N) :
    (A.preservedTwoHistoryCore B N).length ≤ N + 1 := by
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    A.reusable_add_second_first_writers_add_two_reserved_le
      hN B hbaseGrooves hpreGrooves hr1 hr2 hne
        habsentA1 habsentB1 habsentA2 habsentB2
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

end GeneralN
