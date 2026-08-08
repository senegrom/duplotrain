import FullMarkerReplay

/-!
# Full-marker replay with a frozen residual block

Cells in full-edge components replay from the full indicator; lobe cells replay
from their exact endpoint code.  Any remaining no-full non-lobe components are
frozen by `FrozenNoFull`.  Appending such a frozen block preserves the same
component-free code capacity.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Full/lobe coverage on the variable block plus a frozen residual block
implies exact replay of their concatenation. -/
theorem fullLobeDetermines_append_frozen
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (edges lobes variable frozen : List Nat)
    (hcover : FullLobeCovered m e r0 times
      edges lobes variable)
    (hfreeze : FrozenOn m e r0 times frozen) :
    FullLobeDetermines m e r0 times edges lobes
      (variable ++ frozen) := by
  have hvar := fullLobeDetermines_of_covered m e r0 hr0
    edges lobes variable hcover
  intro i hi j hj hsupport hfull hlobe
  have hv := hvar i hi j hj hsupport hfull hlobe
  have hf := hfreeze i hi j hj
  unfold snap at hv hf ⊢
  simp only [List.map_append]
  rw [hv, hf]

/-- Direct component-free count with a frozen residual block. -/
theorem sparse_full_lobe_frozen_epoch_count
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (edges lobes variable frozen ks : List Nat) (M F : Nat)
    (hcover : FullLobeCovered m e r0 times
      edges lobes variable)
    (hfreeze : FrozenOn m e r0 times frozen)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      trueCount (fullBits m e r0 edges k) = F)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0
      (variable ++ frozen))).Nodup) :
    ks.length ≤ sparseCount M * 2 ^ lobes.length := by
  exact sparse_full_lobe_epoch_count m e r0
    edges lobes (variable ++ frozen) ks M F
    (fullLobeDetermines_append_frozen m e r0 hr0
      edges lobes variable frozen hcover hfreeze)
    hks hsupport hEF hfull hloop hocc hnd

/-- Strict `7/8`-exponent form with a frozen residual block. -/
theorem sparse_full_lobe_frozen_eighth_bound
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (edges lobes variable frozen ks : List Nat)
    (C M F : Nat)
    (hcover : FullLobeCovered m e r0 times
      edges lobes variable)
    (hfreeze : FrozenOn m e r0 times frozen)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hEF : edges.length + F = M)
    (hfull : ∀ k ∈ ks,
      trueCount (fullBits m e r0 edges k) = F)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k ∈ ks, ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hnd : (ks.map (snap m e r0
      (variable ++ frozen))).Nodup)
    (hC : C = lobes.length + M)
    (hhalf : lobes.length ≤ M) :
    sparseEighth ks.length ≤ 2^(7*C + 8) := by
  apply sparse_full_lobe_eighth_bound m e r0
    edges lobes (variable ++ frozen) ks C M F
    (fullLobeDetermines_append_frozen m e r0 hr0
      edges lobes variable frozen hcover hfreeze)
    hks hsupport hEF hfull hloop hocc hnd hC hhalf

end Echo
