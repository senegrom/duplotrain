import EndpointAccountingCore

/-!
# Constructing the sparse epoch certificate from local support data

The endpoint equation in `SparseEpochCertCore` is filled automatically by
`endpoint_accounting_core`.  What remains in the constructor inputs is purely
structural/dynamical: replay coverage, a frozen residual block, the active
lobe data, and ordinary finite support coverage.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Build the component-free strict-bound certificate from local edge/cell
coverage at every time. -/
def sparseEpochCertOfLocal
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (times : Nat → Prop)
    (allCells projected edges lobes variable frozen : List Nat)
    (hcover : allCells = variable ++ frozen)
    (hvariable : FullLobeCovered m e r0 times
      edges lobes variable)
    (hfrozen : FrozenOn m e r0 times frozen)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hlobeOcc : ∀ k, times k → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hprojectedNodup : projected.Nodup)
    (hendsNodup : (accountingEdgeEnds m edges).Nodup)
    (hselected : ∀ k, times k → ∀ c ∈ projected,
      reg m e r0 k c ∈ accountingEdgeEnds m edges)
    (hendCells : ∀ x ∈ accountingEdgeEnds m edges,
      m.cellOf x ∈ projected)
    (hedgeOcc : ∀ k, times k → ∀ s ∈ edges,
      Occupied m e r0 k s)
    (hcellCount : allCells.length = lobes.length + projected.length)
    (hallNodup : allCells.Nodup)
    (hstarSep : StarSeparated m (lobeCells m lobes))
    (hstarClosed : ∀ c ∈ lobeCells m lobes,
      c ∈ allCells ∧ m.star c ∈ allCells) :
    SparseEpochCertCore m e r0 times allCells where
  edges := edges
  lobes := lobes
  variable := variable
  frozen := frozen
  cover := hcover
  variable_covered := hvariable
  frozen_on := hfrozen
  lobe_loop := hloop
  lobe_occupied := hlobeOcc
  projectedCells := projected.length
  endpoint_accounting := fun k hk =>
    endpoint_accounting_core m e r0 hr0 projected edges k
      hprojectedNodup hendsNodup
      (hselected k hk) hendCells (hedgeOcc k hk)
  cell_count := hcellCount
  allCells_nodup := hallNodup
  active_star_separated := hstarSep
  active_star_closed := hstarClosed

/-- The resulting certificate immediately gives the strict `7/8` epoch
bound. -/
theorem sparse_epoch_bound_of_local
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (times : Nat → Prop)
    (allCells projected edges lobes variable frozen ks : List Nat)
    (hcover : allCells = variable ++ frozen)
    (hvariable : FullLobeCovered m e r0 times
      edges lobes variable)
    (hfrozen : FrozenOn m e r0 times frozen)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hlobeOcc : ∀ k, times k → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hprojectedNodup : projected.Nodup)
    (hendsNodup : (accountingEdgeEnds m edges).Nodup)
    (hselected : ∀ k, times k → ∀ c ∈ projected,
      reg m e r0 k c ∈ accountingEdgeEnds m edges)
    (hendCells : ∀ x ∈ accountingEdgeEnds m edges,
      m.cellOf x ∈ projected)
    (hedgeOcc : ∀ k, times k → ∀ s ∈ edges,
      Occupied m e r0 k s)
    (hcellCount : allCells.length = lobes.length + projected.length)
    (hallNodup : allCells.Nodup)
    (hstarSep : StarSeparated m (lobeCells m lobes))
    (hstarClosed : ∀ c ∈ lobeCells m lobes,
      c ∈ allCells ∧ m.star c ∈ allCells)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    sparseEighth ks.length ≤ 2^(7*allCells.length + 8) := by
  let cert := sparseEpochCertOfLocal m e r0 hr0 times
    allCells projected edges lobes variable frozen
    hcover hvariable hfrozen hloop hlobeOcc
    hprojectedNodup hendsNodup hselected hendCells hedgeOcc
    hcellCount hallNodup hstarSep hstarClosed
  exact sparse_epoch_bound_of_cert_core m e r0 hr0
    cert ks hks hsupport hnd

end Echo
