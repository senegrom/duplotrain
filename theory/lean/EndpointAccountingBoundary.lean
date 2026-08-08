import EndpointAccountingCore

/-!
# Endpoint accounting across an active-lobe boundary

A projected support edge may have an unconfirmed endpoint in an active lobe
cell.  The counting proof only needs every *confirmed* represented endpoint to
belong to a projected cell.  This boundary-aware version weakens the endpoint
closure hypothesis accordingly while proving the same identity.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Boundary-aware endpoint accounting.** -/
theorem endpoint_accounting_boundary
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells edges : List Nat) (k : Nat)
    (hcells : cells.Nodup)
    (hends : (accountingEdgeEnds m edges).Nodup)
    (hselected : ∀ c ∈ cells,
      reg m e r0 k c ∈ accountingEdgeEnds m edges)
    (hconfirmedCells : ∀ x ∈ accountingEdgeEnds m edges,
      Confirmed m e r0 k x → m.cellOf x ∈ cells)
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
        (hconfirmedCells x hx.1 hx.2) hx.2
    · intro hx
      refine ⟨?_, accounting_selected_confirmed m e r0 hr0 hx⟩
      unfold accountingSelected at hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact hselected c hc
  have hxy :
      (accountingConfirmed m e r0 edges k).length ≤
        (accountingSelected m e r0 cells k).length := by
    apply nodup_subset_length_accounting hcnd
    intro x hx
    exact (hmem x).mp hx
  have hyx :
      (accountingSelected m e r0 cells k).length ≤
        (accountingConfirmed m e r0 edges k).length := by
    apply nodup_subset_length_accounting hsnd
    intro x hx
    exact (hmem x).mpr hx
  have hlen :
      (accountingConfirmed m e r0 edges k).length =
        (accountingSelected m e r0 cells k).length := by
    omega
  rw [accountingConfirmed_length m e r0 edges k hocc,
    accountingSelected_length] at hlen
  exact hlen

end Echo
