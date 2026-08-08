import FullMarkerFrozenReplay

/-!
# Corrected component-free strict epoch certificate

The empty sample list is discharged before the endpoint count is read from an
actual epoch time.  For a nonempty list, one sampled time proves
`edges.length ≤ projectedCells`, so the constant full count may be written as
the natural subtraction `projectedCells - edges.length`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

structure SparseEpochCertCore
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

/-- Active lobe count is no larger than the projected-cell count. -/
theorem SparseEpochCertCore.lobes_le_projected
    {times : Nat → Prop} {allCells : List Nat}
    (cert : SparseEpochCertCore m e r0 times allCells) :
    cert.lobes.length ≤ cert.projectedCells := by
  have hhalf := starSeparated_count m (lobeCells m cert.lobes)
    allCells cert.active_star_separated cert.allCells_nodup
    cert.active_star_closed
  have hlen : (lobeCells m cert.lobes).length = cert.lobes.length := by
    simp [lobeCells]
  rw [hlen, cert.cell_count] at hhalf
  omega

/-- **Component-free strict fixed-epoch theorem.** -/
theorem sparse_epoch_bound_of_cert_core
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {times : Nat → Prop} {allCells : List Nat}
    (cert : SparseEpochCertCore m e r0 times allCells)
    (ks : List Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    sparseEighth ks.length ≤ 2^(7*allCells.length + 8) := by
  cases ks with
  | nil =>
      simp [sparseEighth, fourth]
  | cons k rest =>
      have hk : k ∈ k :: rest := List.mem_cons_self
      have hktime : times k := hks k hk
      let F := cert.projectedCells - cert.edges.length
      have hacc := cert.endpoint_accounting k hktime
      have hEF : cert.edges.length + F = cert.projectedCells := by
        unfold F
        omega
      have hfull : ∀ j ∈ k :: rest,
          trueCount (fullBits m e r0 cert.edges j) = F := by
        intro j hj
        have h := cert.endpoint_accounting j (hks j hj)
        unfold F
        omega
      have hdet := fullLobeDetermines_append_frozen m e r0 hr0
        cert.edges cert.lobes cert.variable cert.frozen
        cert.variable_covered cert.frozen_on
      rw [cert.cover] at hnd
      apply sparse_full_lobe_eighth_bound m e r0
        cert.edges cert.lobes (cert.variable ++ cert.frozen)
        (k :: rest) allCells.length cert.projectedCells F
        hdet hks hsupport hEF hfull cert.lobe_loop
        (fun j hj a ha => cert.lobe_occupied j (hks j hj) a ha)
        hnd
      · exact cert.cell_count
      · exact cert.lobes_le_projected

/-- Isolated structural obligation. -/
def SparseEpochDecomposableCore
    (times : Nat → Prop) (allCells : List Nat) : Prop :=
  Nonempty (SparseEpochCertCore m e r0 times allCells)

end Echo
