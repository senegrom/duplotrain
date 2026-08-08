import SupportMove

/-!
# Standalone endpoint accounting

For a duplicate-free list of represented support edges, retain the confirmed
endpoints.  These are exactly the selected register slots of the represented
cells.  Every occupied edge contributes one confirmed endpoint, and a full
edge contributes one additional endpoint.  Hence

    represented cells = support edges + full edges.

Only confirmed endpoints are required to belong to the represented cell set;
an unconfirmed opposite endpoint may lie in an active lobe cell outside the
projected block.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Both endpoints of each represented jump edge. -/
def standaloneEdgeEnds : List Nat → List Nat
  | [] => []
  | s :: rest => s :: m.bar s :: standaloneEdgeEnds rest

/-- One selected register slot per represented cell. -/
def standaloneSelected (cells : List Nat) (k : Nat) : List Nat :=
  cells.map (fun c => reg m e r0 k c)

/-- Number of true entries. -/
def endpointTrueCount : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + endpointTrueCount rest

/-- Full-edge indicator. -/
noncomputable def endpointFullBits
    (m : Machine) (e r0 : Nat → Nat)
    (edges : List Nat) (k : Nat) : List Bool := by
  classical
  exact edges.map (fun s => decide (Full m e r0 k s))

/-- Confirmed represented endpoints. -/
noncomputable def standaloneConfirmed
    (m : Machine) (e r0 : Nat → Nat)
    (edges : List Nat) (k : Nat) : List Nat := by
  classical
  exact (standaloneEdgeEnds m edges).filter
    (fun s => Confirmed m e r0 k s)

theorem standaloneSelected_length (cells : List Nat) (k : Nat) :
    (standaloneSelected m e r0 cells k).length = cells.length := by
  simp [standaloneSelected]

theorem endpointFullBits_length (edges : List Nat) (k : Nat) :
    (endpointFullBits m e r0 edges k).length = edges.length := by
  simp [endpointFullBits]

/-- Distinct cells select distinct slots. -/
theorem standaloneSelected_nodup
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) (k : Nat)
    (hnd : cells.Nodup) :
    (standaloneSelected m e r0 cells k).Nodup := by
  induction cells with
  | nil => simp [standaloneSelected]
  | cons c rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [standaloneSelected, List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨d, hd, heq⟩ := List.mem_map.mp hm
        have hcells := congrArg m.cellOf heq
        rw [reg_cell m e r0 hr0 k c,
          reg_cell m e r0 hr0 k d] at hcells
        exact hnd.1 (hcells ▸ hd)
      · exact ih hnd.2

/-- Filtering endpoint representatives preserves duplicate-freeness. -/
theorem standaloneConfirmed_nodup
    (edges : List Nat) (k : Nat)
    (hnd : (standaloneEdgeEnds m edges).Nodup) :
    (standaloneConfirmed m e r0 edges k).Nodup := by
  classical
  exact hnd.filter _

theorem mem_standaloneConfirmed_iff
    (edges : List Nat) (k x : Nat) :
    x ∈ standaloneConfirmed m e r0 edges k ↔
      x ∈ standaloneEdgeEnds m edges ∧
        Confirmed m e r0 k x := by
  classical
  simp [standaloneConfirmed]

/-- Every selected register slot is confirmed. -/
theorem standalone_selected_confirmed
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {cells : List Nat} {k x : Nat}
    (hx : x ∈ standaloneSelected m e r0 cells k) :
    Confirmed m e r0 k x := by
  unfold standaloneSelected at hx
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  exact old_register_confirmed m e r0 hr0 k c

/-- Every confirmed endpoint whose cell is represented occurs in the selected
slot list. -/
theorem standalone_confirmed_selected
    {cells : List Nat} {k x : Nat}
    (hcell : m.cellOf x ∈ cells)
    (hx : Confirmed m e r0 k x) :
    x ∈ standaloneSelected m e r0 cells k := by
  unfold standaloneSelected
  apply List.mem_map.mpr
  refine ⟨m.cellOf x, hcell, ?_⟩
  unfold Confirmed at hx
  exact hx

/-- Edgewise endpoint count. -/
theorem standaloneConfirmed_length
    (edges : List Nat) (k : Nat)
    (hocc : ∀ s ∈ edges, Occupied m e r0 k s) :
    (standaloneConfirmed m e r0 edges k).length =
      edges.length + endpointTrueCount
        (endpointFullBits m e r0 edges k) := by
  classical
  induction edges with
  | nil =>
      simp [standaloneConfirmed, standaloneEdgeEnds,
        endpointFullBits, endpointTrueCount]
  | cons s rest ih =>
      have hsocc := hocc s List.mem_cons_self
      have hrest : ∀ t ∈ rest, Occupied m e r0 k t := by
        intro t ht
        exact hocc t (List.mem_cons_of_mem _ ht)
      have hi := ih hrest
      by_cases hs : Confirmed m e r0 k s
      · by_cases hb : Confirmed m e r0 k (m.bar s)
        · simp [standaloneConfirmed, standaloneEdgeEnds,
            endpointFullBits, endpointTrueCount, Full, hs, hb] at hi ⊢
          omega
        · simp [standaloneConfirmed, standaloneEdgeEnds,
            endpointFullBits, endpointTrueCount, Full, hs, hb] at hi ⊢
          omega
      · by_cases hb : Confirmed m e r0 k (m.bar s)
        · simp [standaloneConfirmed, standaloneEdgeEnds,
            endpointFullBits, endpointTrueCount, Full, hs, hb] at hi ⊢
          omega
        · exfalso
          rcases hsocc with h | h
          · exact hs h
          · exact hb h

private theorem standalone_nodup_subset_length
    {xs ys : List Nat}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ z ∈ rest, z ∈ ys.erase x := by
        intro z hz
        have hzy := hsub z (List.mem_cons_of_mem _ hz)
        have hzx : z ≠ x := fun h => hnd.1 (h ▸ hz)
        exact (List.mem_erase_of_ne hzx).mpr hzy
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- **Endpoint accounting with an active-lobe boundary.** -/
theorem endpoint_accounting_standalone
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells edges : List Nat) (k : Nat)
    (hcells : cells.Nodup)
    (hends : (standaloneEdgeEnds m edges).Nodup)
    (hselected : ∀ c ∈ cells,
      reg m e r0 k c ∈ standaloneEdgeEnds m edges)
    (hconfirmedCells : ∀ x ∈ standaloneEdgeEnds m edges,
      Confirmed m e r0 k x → m.cellOf x ∈ cells)
    (hocc : ∀ s ∈ edges, Occupied m e r0 k s) :
    edges.length + endpointTrueCount
      (endpointFullBits m e r0 edges k) = cells.length := by
  have hsnd := standaloneSelected_nodup m e r0 hr0 cells k hcells
  have hcnd := standaloneConfirmed_nodup m e r0 edges k hends
  have hmem : ∀ x,
      x ∈ standaloneConfirmed m e r0 edges k ↔
        x ∈ standaloneSelected m e r0 cells k := by
    intro x
    rw [mem_standaloneConfirmed_iff]
    constructor
    · intro hx
      exact standalone_confirmed_selected m e r0
        (hconfirmedCells x hx.1 hx.2) hx.2
    · intro hx
      refine ⟨?_, standalone_selected_confirmed m e r0 hr0 hx⟩
      unfold standaloneSelected at hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact hselected c hc
  have hxy :
      (standaloneConfirmed m e r0 edges k).length ≤
        (standaloneSelected m e r0 cells k).length :=
    standalone_nodup_subset_length hcnd
      (fun x hx => (hmem x).mp hx)
  have hyx :
      (standaloneSelected m e r0 cells k).length ≤
        (standaloneConfirmed m e r0 edges k).length :=
    standalone_nodup_subset_length hsnd
      (fun x hx => (hmem x).mpr hx)
  have hlen :
      (standaloneConfirmed m e r0 edges k).length =
        (standaloneSelected m e r0 cells k).length := by
    omega
  rw [standaloneConfirmed_length m e r0 edges k hocc,
    standaloneSelected_length] at hlen
  exact hlen

end Echo
