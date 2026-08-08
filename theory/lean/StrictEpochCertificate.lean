import FrozenNoFull

/-!
# One certificate for the strict fixed-support bound

All dynamical and counting ingredients are packaged into a single object.  A
`StrictEpochCert` partitions the covered cells into:

* reachable full-edge tree blocks;
* persistent lobe representatives; and
* a frozen block.

It also records the elementary tree-size equations and the star-separation of
active lobe cells.  The main theorem turns any such certificate into

    (# distinct covered snapshots)^4 ≤ 2^(3C).

Consequently the remaining structural theorem is sharply isolated: construct
this certificate for every fixed-support interval before the first Gray-square
absorption.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Complete certificate for one fixed-support epoch. -/
structure StrictEpochCert
    (times : Nat → Prop) (allCells : List Nat) where
  blocks : List (TreeBlockCert m e r0 times)
  lobes : List Nat
  frozen : List Nat
  cover : allCells = coveredCells m e r0 blocks lobes frozen
  frozen_on : FrozenOn m e r0 times frozen
  lobe_loop : ∀ a ∈ lobes,
    m.cellOf (m.bar a) = m.cellOf a
  lobe_occupied : ∀ k, times k → ∀ a ∈ lobes,
    Occupied m e r0 k a
  tree_size : ∀ b ∈ blocks,
    b.edges.length + 1 = b.cells.length
  tree_nontrivial : ∀ b ∈ blocks, 2 ≤ b.cells.length
  cell_count : allCells.length =
    treeCellCount m e r0 blocks + lobes.length + frozen.length
  allCells_nodup : allCells.Nodup
  active_star_separated : StarSeparated m (lobeCells m lobes)
  active_star_closed : ∀ c ∈ lobeCells m lobes,
    c ∈ allCells ∧ m.star c ∈ allCells

/-- Active lobe representatives occupy at most half the certified cells. -/
theorem StrictEpochCert.lobe_half
    {times : Nat → Prop} {allCells : List Nat}
    (cert : StrictEpochCert m e r0 times allCells) :
    2 * cert.lobes.length ≤ allCells.length := by
  have h := starSeparated_count m (lobeCells m cert.lobes)
    allCells cert.active_star_separated cert.allCells_nodup
    cert.active_star_closed
  simpa [lobeCells] using h

/-- **Strict fixed-epoch theorem from one certificate.** -/
theorem strict_epoch_bound_of_cert
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {times : Nat → Prop} {allCells : List Nat}
    (cert : StrictEpochCert m e r0 times allCells)
    (ks : List Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    fourth ks.length ≤ 2 ^ (3 * allCells.length) := by
  rw [cert.cover] at hnd
  apply certified_tree_lobe_frozen_bound m e r0 hr0
    cert.blocks cert.lobes cert.frozen ks allCells.length
    cert.frozen_on hks hsupport cert.lobe_loop
    (fun k hk a ha => cert.lobe_occupied k (hks k hk) a ha)
    hnd cert.tree_size cert.tree_nontrivial
  · exact cert.cell_count.symm
  · exact cert.lobe_half

/-- Existence form of the isolated structural obligation. -/
def StrictEpochDecomposable
    (times : Nat → Prop) (allCells : List Nat) : Prop :=
  Nonempty (StrictEpochCert m e r0 times allCells)

/-- Once the structural certificate exists, the numerical theorem is
immediate. -/
theorem strict_epoch_bound_of_decomposable
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {times : Nat → Prop} {allCells : List Nat}
    (hdec : StrictEpochDecomposable m e r0 times allCells)
    (ks : List Nat)
    (hks : ∀ k ∈ ks, times k)
    (hsupport : ∀ i ∈ ks, ∀ j ∈ ks, ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hnd : (ks.map (snap m e r0 allCells)).Nodup) :
    fourth ks.length ≤ 2 ^ (3 * allCells.length) := by
  rcases hdec with ⟨cert⟩
  exact strict_epoch_bound_of_cert m e r0 hr0 cert ks
    hks hsupport hnd

end Echo
