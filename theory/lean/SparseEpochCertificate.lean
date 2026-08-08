import FullMarkerFrozenReplay

/-!
# A component-free strict epoch certificate

This certificate is weaker and simpler than `StrictEpochCert`.  It avoids an
explicit tree-component partition.  It records only:

* a representative list of projected support edges;
* the active lobe representatives;
* full/lobe reachability coverage plus a frozen residual block;
* endpoint accounting `E + F = M`; and
* star separation of active lobe cells.

The main theorem gives the integer strict-base estimate

    (# distinct snapshots)^8 ≤ 2^(7C+8).

Thus, apart from a harmless factor 2, the epoch has at most
`2^(7C/8) ≈ 1.834^C` states.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

structure SparseEpochCert
    (times : Nat → Prop) (allCells : List Nat) where
  edges : List Nat
  lobes : List Nat
  variable : List Nat
  frozen : List Nat
  cover : allCells = variable ++ frozen
  variable_covered : FullLobeCovered m e r0 times
    edges lobes variable
  frozen_on : FrozenOn m e r0 times frozen
  lobe_loop : ∀ a ∈ lobes,
    m.cellOf (m.bar a) = m.cellOf a
  lobe_occupied : ∀ k, times k → ∀ a ∈ lobes,
    Occupied m e r0 k a
  projectedCells : Nat
  endpoint_accounting : ∀ k, times k,
    edges.length + trueCount (fullBits m e r0 edges k) = projectedCells
  cell_count : allCells.length = lobes.length + projectedCells
  allCells_nodup : allCells.Nodup
  active_star_separated : StarSeparated m (lobeCells m lobes)
  active_star_closed : ∀ c ∈ lobeCells m lobes,
    c ∈ allCells ∧ m.star c ∈ allCells

/-- Star separation plus the cell count gives the density inequality required
by the sparse arithmetic. -/
theorem SparseEpochCert.lobes_le_projected
    {times : Nat → Prop} {allCells : List Nat}
    (cert : SparseEpochCert m e r0 times allCells) :
    cert.lobes.length ≤ cert.projectedCells := by
  have hhalf := starSeparated_count m (lobeCells m cert.lobes)
    allCells cert.active_star_separated cert.allCells_nodup
    cert.active_star_closed
  have hlen : (lobeCells m cert.lobes).length = cert.lobes.length := by
    simp [lobeCells]
  rw [hlen, cert.cell_count] at hhalf
  omega

/-- **Component-free strict fixed-epoch theorem.** -/
theorem sparse_epoch_bound_of_cert
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {times : Nat → Prop} {allCells : List Nat}
    (cert : SparseEpochCert m e r0 times allCells)
    (ks : List Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    sparseEighth ks.length ≤ 2^(7*allCells.length + 8) := by
  rw [cert.cover] at hnd
  let F := cert.projectedCells - cert.edges.length
  have hEF : cert.edges.length + F = cert.projectedCells := by
    have hacc := cert.endpoint_accounting
      (match ks with | [] => 0 | k :: _ => k)
    by_cases hnil : ks = []
    · subst ks
      simp at hnd
      omega
    · obtain ⟨k, hk⟩ : ∃ k, k ∈ ks := by
        cases ks with
        | nil => contradiction
        | cons k rest => exact ⟨k, List.mem_cons_self⟩
      have h := cert.endpoint_accounting k (hks k hk)
      unfold F
      omega
  have hfull : ∀ k ∈ ks,
      trueCount (fullBits m e r0 cert.edges k) = F := by
    intro k hk
    have h := cert.endpoint_accounting k (hks k hk)
    unfold F
    omega
  have hdet := fullLobeDetermines_append_frozen m e r0 hr0
    cert.edges cert.lobes cert.variable cert.frozen
    cert.variable_covered cert.frozen_on
  apply sparse_full_lobe_eighth_bound m e r0
    cert.edges cert.lobes (cert.variable ++ cert.frozen) ks
    allCells.length cert.projectedCells F
    hdet hks hsupport hEF hfull cert.lobe_loop
    (fun k hk a ha => cert.lobe_occupied k (hks k hk) a ha)
    hnd
  · exact cert.cell_count.symm
  · exact cert.lobes_le_projected

/-- Structural obligation isolated as a proposition. -/
def SparseEpochDecomposable
    (times : Nat → Prop) (allCells : List Nat) : Prop :=
  Nonempty (SparseEpochCert m e r0 times allCells)

end Echo
