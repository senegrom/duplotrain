import StateLawTwoSixUltra
import TwoHistoryUnionCharge

/-!
# The productive initial coordinate is absent from the second writer history

This file isolates one coefficient-one accounting step.  The first
reflector `A` has a list of reusable support coordinates; the second
reflector `B` has a list of coordinates at which its switch-simple
construction performs a productive first write.  If the productive initial
coordinate `k0` belongs to neither list, then it is a genuinely reserved
coordinate.  Adjoining it to the existing disjoint-coordinate certificate
saves one state in the combined construction history.

The final theorem packages the form needed by the arbitrary-start boundary
argument: once the first-reflector analysis says that the original vector is
already represented or `k0` is absent from the reusable support, absence
from the second writer list gives exactly the desired absorbed-or-one-saved
dichotomy.
-/

namespace GeneralN

private theorem boundaryAbsent_nodup_filter_nat (p : Nat -> Bool) :
    forall {xs : List Nat}, xs.Nodup -> (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hm => hnd.1 (List.mem_filter.mp hm).1,
            ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem boundaryAbsent_nodup_map_nat_of_injective_on
    {f : Nat -> Nat} {xs : List Nat}
    (hinj : forall x, x ∈ xs ->
      forall y, y ∈ xs -> f x = f y -> x = y)
    (hnd : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
        have hxy := hinj x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih
          (fun a ha b hb => hinj a
            (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb))
          hnd.2

/-- Switch coordinates of the productive first writers in a manufactured
reflector's switch-simple construction. -/
noncomputable def ManufacturedReflector.constructionFirstWriterSwitches
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w g e) (N : Nat) : List Nat :=
  (rawFirstWriterTimes w N (g, B.baseState)
      B.exploration.length).map
    (rawWriterAt w (g, B.baseState))

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
  classical
  let times :=
    rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact boundaryAbsent_nodup_filter_nat _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply boundaryAbsent_nodup_map_nat_of_injective_on
    · intro i hi j hj hEq
      have hiData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hi)
      have hjData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hj)
      exact rawFirstWriterAt_injective hiData.2 hjData.2 hEq
    · exact htimesNodup
  have hdisjoint :
      forall oldSwitch, List.Mem oldSwitch A.reusableSwitches ->
        forall freshSwitch, List.Mem freshSwitch writers ->
          Ne oldSwitch freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside :=
      A.second_exploration_productive_writer_not_reusable
        hN B hbaseGrooves hpreGrooves
          hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let occupied := A.reusableSwitches ++ writers
  have hoccupiedNodup : occupied.Nodup := by
    dsimp [occupied]
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  have hk0NotOccupied : Not (List.Mem k0 occupied) := by
    intro hk
    rcases List.mem_append.mp hk with hOld | hFresh
    · exact habsentA hOld
    · apply habsentB
      dsimp [ManufacturedReflector.constructionFirstWriterSwitches,
        writers, times]
      exact hFresh
  have hallNodup : (k0 :: occupied).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hk0NotOccupied, hoccupiedNodup⟩
  have hallLt : forall C, List.Mem C (k0 :: occupied) -> C < N := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · exact hk0
    · rcases List.mem_append.mp hC with hOld | hFresh
      · exact A.reusableSwitch_lt hN hOld
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
        have hkData := mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using hk)
        exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hallNodup hallLt
  have hlength :
      (k0 :: occupied).length =
        A.reusableSwitches.length + times.length + 1 := by
    simp [occupied, writers]
  rw [hlength] at hbound
  simpa [times] using hbound

/-- The reserved coordinate lowers the two-construction core from `N+3` to
`N+2`.  This is the one-state saving needed to adjoin the original boundary
vector without exceeding the old `N+3` construction budget. -/
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

/-- Reusable absorbed-or-saved interface for the boundary proof.

The only first-reflector input is the local dichotomy that the original
restricted vector is already represented by `A` or the productive initial
coordinate is absent from `A`'s reusable support.  If `k0` is also absent
from `B`'s productive first-writer switch list, then either the original
vector is in the combined core, or that core has the improved `N+2` size.
-/
theorem ManufacturedReflector.boundary_absorbed_or_combined_history_saves_one_of_second_writer_absent
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N)))
    (hfirst :
      List.Mem (VectorCount.restrict N original)
          (A.sharpHistoryCore N) \/
        Not (List.Mem k0 A.reusableSwitches)) :
    List.Mem (VectorCount.restrict N original)
        (A.preservedTwoHistoryCore B N) \/
      (A.preservedTwoHistoryCore B N).length <= N + 2 := by
  rcases hfirst with habsorbed | habsentA
  · apply Or.inl
    apply List.mem_append_left
    exact habsorbed
  · apply Or.inr
    exact A.preservedTwoHistoryCore_length_le_N_add_two_of_reserved
      hN B hbase hbaseGrooves hpreGrooves
        hk0 habsentA habsentB

end GeneralN
