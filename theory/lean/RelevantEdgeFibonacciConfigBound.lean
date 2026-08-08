import EchoConfigCount
import RelevantEdgeFibonacciGlobalBound

/-!
# Configuration count from the physical-edge Fibonacci snapshot bound
-/

namespace Echo

private theorem edgeFibConfig_sum_le
    (xs : List Nat) (B : Nat)
    (h : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hx := h x List.mem_cons_self
      have hr : ∀ y ∈ rest, y ≤ B := by
        intro y hy
        exact h y (List.mem_cons_of_mem _ hy)
      have hi := ih hr
      simp only [List.sum_cons, List.length_cons]
      calc
        x + rest.sum ≤ B + rest.length * B := Nat.add_le_add hx hi
        _ = (rest.length + 1) * B := by
          simp [Nat.add_mul, Nat.add_comm]

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Distinct finite configurations cost one improved snapshot fibre per entry. -/
theorem relevantFrame_config_edge_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots entries ks : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0 globalLo globalHi cells)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2*N)
    (hentriesNodup : entries.Nodup)
    (hentryCover : ∀ k ∈ ks, e k ∈ entries)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hcfg : (ks.map (configSnap m e r0 cells)).Nodup) :
    ks.length ≤ entries.length *
      ((N + 1) * fibBalancedCapacity N + 4) := by
  let sizes := entryFibreSizes entries e ks
  have hsum : sizes.sum = ks.length := by
    dsimp [sizes]
    exact entryFibreSizes_sum entries e ks hentriesNodup hentryCover
  have heach : ∀ s ∈ sizes,
      s ≤ (N + 1) * fibBalancedCapacity N + 4 := by
    intro s hs
    dsimp [sizes, entryFibreSizes] at hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    let fibre := ks.filter (fun k => e k = q)
    have htime : ∀ k ∈ fibre, globalLo ≤ k ∧ k ≤ globalHi := by
      intro k hk
      have hkFilter : k ∈ ks.filter (fun j => e j = q) := by
        simpa only [fibre] using hk
      exact hks k (List.mem_filter.mp hkFilter).1
    have hndSnap : (fibre.map (snap m e r0 cells)).Nodup := by
      dsimp [fibre]
      exact entryFibre_snap_nodup m e r0 cells ks q hcfg
    have hbound := relevant_finiteFrame_N_edge_fibonacci_bound
      m e r0 hrun hr0 N globalLo globalHi cells slots fibre
      frame hfullRelevant hcells hslots htime hndSnap
    simpa [entryFibreSize, fibre] using hbound
  have hagg := edgeFibConfig_sum_le sizes
    ((N + 1) * fibBalancedCapacity N + 4) heach
  have hlen : sizes.length = entries.length := by
    simp [sizes, entryFibreSizes]
  rw [hsum, hlen] at hagg
  exact hagg

/-- At most `2*N` current entries. -/
theorem relevantFrame_config_atMost_N_edge_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots entries ks : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0 globalLo globalHi cells)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2*N)
    (hentriesNodup : entries.Nodup)
    (hentriesLength : entries.length ≤ 2*N)
    (hentryCover : ∀ k ∈ ks, e k ∈ entries)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hcfg : (ks.map (configSnap m e r0 cells)).Nodup) :
    ks.length ≤ (2*N) * ((N + 1) * fibBalancedCapacity N + 4) := by
  have hbase := relevantFrame_config_edge_fibonacci_bound
    m e r0 hrun hr0 N globalLo globalHi cells slots entries ks
    frame hfullRelevant hcells hslots hentriesNodup
    hentryCover hks hcfg
  have hmul := Nat.mul_le_mul_right
    ((N + 1) * fibBalancedCapacity N + 4) hentriesLength
  exact Nat.le_trans hbase hmul

end Echo
