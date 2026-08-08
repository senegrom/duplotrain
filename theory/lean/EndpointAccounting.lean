import SparseEpochCertificateCore

/-!
# Endpoint accounting: cells = occupied edges + full edges

For a duplicate-free list of projected support-edge representatives, expand
each edge to its two slot endpoints and retain the confirmed endpoints.  Under
the natural coverage hypotheses this filtered list is exactly the list of one
selected register slot per projected cell.

Every occupied edge contributes one confirmed endpoint, and contributes a
second endpoint exactly when it is full.  Therefore

    projected cells = represented support edges + full edges.

This discharges the numerical `E+F=M` field of the component-free sparse
certificate from elementary local conditions.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Both endpoints of every represented jump edge. -/
def edgeEnds : List Nat → List Nat
  | [] => []
  | s :: rest => s :: m.bar s :: edgeEnds rest

/-- One selected register slot for each listed cell. -/
def selectedSlots (cells : List Nat) (k : Nat) : List Nat :=
  cells.map (fun c => reg m e r0 k c)

/-- Confirmed endpoints among the represented edges. -/
open Classical in
noncomputable def confirmedEnds (edges : List Nat) (k : Nat) : List Nat :=
  (edgeEnds m edges).filter (fun s => Confirmed m e r0 k s)

/-- Selected-slot list length. -/
theorem selectedSlots_length (cells : List Nat) (k : Nat) :
    (selectedSlots m e r0 cells k).length = cells.length := by
  simp [selectedSlots]

/-- Distinct cells select distinct slots. -/
theorem selectedSlots_nodup
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) (k : Nat)
    (hnd : cells.Nodup) :
    (selectedSlots m e r0 cells k).Nodup := by
  induction cells with
  | nil => simp [selectedSlots]
  | cons c rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [selectedSlots, List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨d, hd, heq⟩ := List.mem_map.mp hm
        have hc := reg_cell m e r0 hr0 k c
        have hdcell := reg_cell m e r0 hr0 k d
        have hcells := congrArg m.cellOf heq
        rw [hc, hdcell] at hcells
        exact hnd.1 (hcells ▸ hd)
      · exact ih hnd.2

/-- Filtering a duplicate-free endpoint list preserves duplicate-freeness. -/
theorem confirmedEnds_nodup
    (edges : List Nat) (k : Nat)
    (hnd : (edgeEnds m edges).Nodup) :
    (confirmedEnds m e r0 edges k).Nodup := by
  classical
  exact List.Nodup.filter _ hnd

/-- Membership in the confirmed endpoint list. -/
theorem mem_confirmedEnds_iff
    (edges : List Nat) (k x : Nat) :
    x ∈ confirmedEnds m e r0 edges k ↔
      x ∈ edgeEnds m edges ∧ Confirmed m e r0 k x := by
  classical
  simp [confirmedEnds]

/-- Every selected slot is confirmed. -/
theorem selected_slot_confirmed
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {cells : List Nat} {k x : Nat}
    (hx : x ∈ selectedSlots m e r0 cells k) :
    Confirmed m e r0 k x := by
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  exact old_register_confirmed m e r0 hr0 k c

/-- A confirmed endpoint whose cell is listed occurs in the selected-slot
list. -/
theorem confirmed_mem_selectedSlots
    {cells : List Nat} {k x : Nat}
    (hcell : m.cellOf x ∈ cells)
    (hx : Confirmed m e r0 k x) :
    x ∈ selectedSlots m e r0 cells k := by
  unfold selectedSlots
  apply List.mem_map.mpr
  refine ⟨m.cellOf x, hcell, ?_⟩
  unfold Confirmed at hx
  exact hx

/-- Each represented occupied edge contributes one endpoint, plus a second
endpoint iff it is full. -/
theorem confirmedEnds_length_eq
    (edges : List Nat) (k : Nat)
    (hocc : ∀ s ∈ edges, Occupied m e r0 k s) :
    (confirmedEnds m e r0 edges k).length =
      edges.length + trueCount (fullBits m e r0 edges k) := by
  classical
  induction edges with
  | nil => simp [confirmedEnds, edgeEnds, fullBits, trueCount]
  | cons s rest ih =>
      have hsocc := hocc s List.mem_cons_self
      have hrest : ∀ t ∈ rest, Occupied m e r0 k t := by
        intro t ht
        exact hocc t (List.mem_cons_of_mem _ ht)
      have hi := ih hrest
      by_cases hs : Confirmed m e r0 k s
      · by_cases hb : Confirmed m e r0 k (m.bar s)
        · simp [confirmedEnds, edgeEnds, fullBits, trueCount,
            Full, hs, hb, hi]
        · simp [confirmedEnds, edgeEnds, fullBits, trueCount,
            Full, hs, hb, hi]
      · by_cases hb : Confirmed m e r0 k (m.bar s)
        · simp [confirmedEnds, edgeEnds, fullBits, trueCount,
            Full, hs, hb, hi]
        · exact absurd hsocc (by
            intro h
            rcases h with h | h
            · exact hs h
            · exact hb h)

private theorem nodup_same_members_length
    {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hmem : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs.length = ys.length := by
  have hxy : xs.length ≤ ys.length := by
    induction xs generalizing ys with
    | nil => exact Nat.zero_le _
    | cons x rest ih =>
        rw [List.nodup_cons] at hx
        have hxin : x ∈ ys := (hmem x).mp List.mem_cons_self
        have hyerase : (ys.erase x).Nodup := hy.erase _
        have hrest : ∀ z, z ∈ rest ↔ z ∈ ys.erase x := by
          intro z
          constructor
          · intro hz
            have hzy := (hmem z).mp (List.mem_cons_of_mem _ hz)
            have hzx : z ≠ x := fun h => hx.1 (h ▸ hz)
            exact (List.mem_erase_of_ne hzx).mpr hzy
          · intro hz
            have hzy := List.mem_of_mem_erase hz
            have hzxs := (hmem z).mpr hzy
            rcases hzxs with rfl | hzrest
            · exact absurd (List.mem_erase_self x ys) hz
            · exact hzrest
        have hle := ih hx.2 hyerase hrest
        rw [List.length_erase_of_mem hxin] at hle
        have hpos : 0 < ys.length := by
          cases ys with
          | nil => cases hxin
          | cons _ _ => simp
        simp only [List.length_cons]
        omega
  have hyx : ys.length ≤ xs.length := by
    apply List.Sublist.length_le
    -- For duplicate-free finite lists, membership inclusion gives a sublist
    -- after erasing in the order of `ys`; reuse the first inequality theorem
    -- through a symmetric local induction.
    clear hxy
    induction ys generalizing xs with
    | nil => exact List.nil_sublist
    | cons y rest ih =>
        rw [List.nodup_cons] at hy
        have hyin : y ∈ xs := (hmem y).mpr List.mem_cons_self
        obtain ⟨pre, post, rfl⟩ := List.append_of_mem hyin
        apply List.Sublist.trans
          (List.cons_sublist_cons y (ih
            (List.Nodup.of_append_left hx)
            hy.2
            (fun z => by
              constructor
              · intro hz
                have hzall : z ∈ pre ++ y :: post :=
                  (hmem z).mpr (List.mem_cons_of_mem _ hz)
                exact hzall
              · intro hz
                have hzrest : z ∈ rest := by
                  have hzys := (hmem z).mp hz
                  rcases hzys with hzy | hzrest
                  · exact absurd hzy (hy.1 hz)
                  · exact hzrest
                exact hzrest)))
        exact List.sublist_append_right _ _
  omega

/-- **Endpoint accounting theorem.** -/
theorem endpoint_accounting
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells edges : List Nat) (k : Nat)
    (hcells : cells.Nodup)
    (hends : (edgeEnds m edges).Nodup)
    (hselected : ∀ c ∈ cells,
      reg m e r0 k c ∈ edgeEnds m edges)
    (hendCells : ∀ x ∈ edgeEnds m edges,
      m.cellOf x ∈ cells)
    (hocc : ∀ s ∈ edges, Occupied m e r0 k s) :
    edges.length + trueCount (fullBits m e r0 edges k) =
      cells.length := by
  have hsnd := selectedSlots_nodup m e r0 hr0 cells k hcells
  have hcnd := confirmedEnds_nodup m e r0 edges k hends
  have hmem : ∀ x,
      x ∈ confirmedEnds m e r0 edges k ↔
        x ∈ selectedSlots m e r0 cells k := by
    intro x
    rw [mem_confirmedEnds_iff]
    constructor
    · intro hx
      exact confirmed_mem_selectedSlots m e r0
        (hendCells x hx.1) hx.2
    · intro hx
      refine ⟨?_, selected_slot_confirmed m e r0 hr0 hx⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact hselected c hc
  have hlen := nodup_same_members_length hcnd hsnd hmem
  rw [confirmedEnds_length_eq m e r0 edges k hocc,
    selectedSlots_length] at hlen
  exact hlen

end Echo
