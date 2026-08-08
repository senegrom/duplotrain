import SparseEpochCertificateCore

/-!
# Endpoint accounting, minimal proof

Confirmed endpoints of the represented support edges are exactly the selected
register slots of the represented cells.  Duplicate-free mutual inclusion
gives equal lengths.  Edgewise, occupancy contributes one endpoint and
fullness contributes precisely one additional endpoint, yielding

    cells = edges + full edges.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Both endpoints of every represented jump edge. -/
def accountingEdgeEnds : List Nat → List Nat
  | [] => []
  | s :: rest => s :: m.bar s :: accountingEdgeEnds rest

/-- One selected register slot per represented cell. -/
def accountingSelected (cells : List Nat) (k : Nat) : List Nat :=
  cells.map (fun c => reg m e r0 k c)

open Classical in
noncomputable def accountingConfirmed
    (edges : List Nat) (k : Nat) : List Nat :=
  (accountingEdgeEnds m edges).filter
    (fun s => Confirmed m e r0 k s)

theorem accountingSelected_length (cells : List Nat) (k : Nat) :
    (accountingSelected m e r0 cells k).length = cells.length := by
  simp [accountingSelected]

/-- Different represented cells select different slots. -/
theorem accountingSelected_nodup
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) (k : Nat)
    (hnd : cells.Nodup) :
    (accountingSelected m e r0 cells k).Nodup := by
  induction cells with
  | nil => simp [accountingSelected]
  | cons c rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [accountingSelected, List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨d, hd, heq⟩ := List.mem_map.mp hm
        have hcells := congrArg m.cellOf heq
        rw [reg_cell m e r0 hr0 k c,
          reg_cell m e r0 hr0 k d] at hcells
        exact hnd.1 (hcells ▸ hd)
      · exact ih hnd.2

/-- Filtering preserves endpoint duplicate-freeness. -/
theorem accountingConfirmed_nodup
    (edges : List Nat) (k : Nat)
    (hnd : (accountingEdgeEnds m edges).Nodup) :
    (accountingConfirmed m e r0 edges k).Nodup := by
  classical
  exact hnd.filter _

theorem mem_accountingConfirmed_iff
    (edges : List Nat) (k x : Nat) :
    x ∈ accountingConfirmed m e r0 edges k ↔
      x ∈ accountingEdgeEnds m edges ∧
        Confirmed m e r0 k x := by
  classical
  simp [accountingConfirmed]

/-- Every selected register slot is confirmed. -/
theorem accounting_selected_confirmed
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {cells : List Nat} {k x : Nat}
    (hx : x ∈ accountingSelected m e r0 cells k) :
    Confirmed m e r0 k x := by
  unfold accountingSelected at hx
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  exact old_register_confirmed m e r0 hr0 k c

/-- Every confirmed endpoint whose cell is represented is selected by that
cell. -/
theorem accounting_confirmed_selected
    {cells : List Nat} {k x : Nat}
    (hcell : m.cellOf x ∈ cells)
    (hx : Confirmed m e r0 k x) :
    x ∈ accountingSelected m e r0 cells k := by
  unfold accountingSelected
  apply List.mem_map.mpr
  refine ⟨m.cellOf x, hcell, ?_⟩
  unfold Confirmed at hx
  exact hx

/-- Edgewise endpoint count. -/
theorem accountingConfirmed_length
    (edges : List Nat) (k : Nat)
    (hocc : ∀ s ∈ edges, Occupied m e r0 k s) :
    (accountingConfirmed m e r0 edges k).length =
      edges.length + trueCount (fullBits m e r0 edges k) := by
  classical
  induction edges with
  | nil =>
      simp [accountingConfirmed, accountingEdgeEnds,
        fullBits, trueCount]
  | cons s rest ih =>
      have hsocc := hocc s List.mem_cons_self
      have hrest : ∀ t ∈ rest, Occupied m e r0 k t := by
        intro t ht
        exact hocc t (List.mem_cons_of_mem _ ht)
      have hi := ih hrest
      by_cases hs : Confirmed m e r0 k s
      · by_cases hb : Confirmed m e r0 k (m.bar s)
        · simp [accountingConfirmed, accountingEdgeEnds,
            fullBits, trueCount, Full, hs, hb, hi]
        · simp [accountingConfirmed, accountingEdgeEnds,
            fullBits, trueCount, Full, hs, hb, hi]
      · by_cases hb : Confirmed m e r0 k (m.bar s)
        · simp [accountingConfirmed, accountingEdgeEnds,
            fullBits, trueCount, Full, hs, hb, hi]
        · exfalso
          rcases hsocc with h | h
          · exact hs h
          · exact hb h

private theorem nodup_subset_length_accounting
    {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α}
    (hx : xs.Nodup)
    (hsub : ∀ z ∈ xs, z ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hx
      have hxy : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ z ∈ rest, z ∈ ys.erase x := by
        intro z hz
        have hzy := hsub z (List.mem_cons_of_mem _ hz)
        have hzx : z ≠ x := fun h => hx.1 (h ▸ hz)
        exact (List.mem_erase_of_ne hzx).mpr hzy
      have hle := ih hx.2 hsub'
      rw [List.length_erase_of_mem hxy] at hle
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hxy
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

private theorem nodup_same_members_length_accounting
    {α : Type} [BEq α] [LawfulBEq α]
    {xs ys : List α}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hmem : ∀ z, z ∈ xs ↔ z ∈ ys) :
    xs.length = ys.length := by
  apply Nat.le_antisymm
  · exact nodup_subset_length_accounting hx
      (fun z hz => (hmem z).mp hz)
  · exact nodup_subset_length_accounting hy
      (fun z hz => (hmem z).mpr hz)

/-- **Cells = occupied support edges + full edges.** -/
theorem endpoint_accounting_core
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells edges : List Nat) (k : Nat)
    (hcells : cells.Nodup)
    (hends : (accountingEdgeEnds m edges).Nodup)
    (hselected : ∀ c ∈ cells,
      reg m e r0 k c ∈ accountingEdgeEnds m edges)
    (hendCells : ∀ x ∈ accountingEdgeEnds m edges,
      m.cellOf x ∈ cells)
    (hocc : ∀ s ∈ edges, Occupied m e r0 k s) :
    edges.length + trueCount (fullBits m e r0 edges k) =
      cells.length := by
  have hsnd := accountingSelected_nodup m e r0 hr0 cells k hcells
  have hcnd := accountingConfirmed_nodup m e r0 edges k hends
  have hmem : ∀ x,
      x ∈ accountingConfirmed m e r0 edges k ↔
        x ∈ accountingSelected m e r0 cells k := by
    intro x
    rw [mem_accountingConfirmed_iff]
    constructor
    · intro hx
      exact accounting_confirmed_selected m e r0
        (hendCells x hx.1) hx.2
    · intro hx
      refine ⟨?_, accounting_selected_confirmed m e r0 hr0 hx⟩
      unfold accountingSelected at hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact hselected c hc
  have hlen := nodup_same_members_length_accounting hcnd hsnd hmem
  rw [accountingConfirmed_length m e r0 edges k hocc,
    accountingSelected_length] at hlen
  exact hlen

end Echo
