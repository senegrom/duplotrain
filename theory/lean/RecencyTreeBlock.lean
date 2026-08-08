import RecencyRank

/-!
# Certified tree blocks from unique full edges and write recency

`RecencyRank.lean` shows that every selected edge which is both non-full and
non-lobed points toward a cell written more recently.  This file packages that
fact into the `TreeBlockCert` required by the finite fixed-support code.

The only structural input left for one block is now:

* a finite cell list closed under the currently selected target;
* one designated full edge, unique up to physical edge representation;
* no lobe edge away from the two root endpoints; and
* every listed cell has already been written at a positive time.

The recency rank is manufactured internally.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- If the selected edge of `c` is physically the root edge, then `c` is one
of the two root endpoint cells. -/
theorem selected_sameEdge_root
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k f c : Nat}
    (h : SameEdge m f (reg m e r0 k c)) :
    c = m.cellOf f ∨ c = m.cellOf (m.bar f) := by
  have hc := reg_cell m e r0 hr0 k c
  rcases h with h | h
  · left
    rw [h] at hc
    exact hc.symm
  · right
    rw [h] at hc
    exact hc.symm

/-- Uniqueness of the full physical edge forces every non-root selected edge
to be non-full. -/
theorem selected_not_full_away_root
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k f c : Nat}
    (hunique : Full m e r0 k (reg m e r0 k c) →
      SameEdge m f (reg m e r0 k c))
    (hl : c ≠ m.cellOf f)
    (hr : c ≠ m.cellOf (m.bar f)) :
    ¬ Full m e r0 k (reg m e r0 k c) := by
  intro hfull
  rcases selected_sameEdge_root m e r0 hr0
      (hunique hfull) with h | h
  · exact hl h
  · exact hr h

/-- A fixed-support tree block whose root and orientation are recovered from
last-write recency. -/
noncomputable def recencyTreeBlock
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (times : Nat → Prop)
    (cells edges : List Nat)
    (fullAt : Nat → Nat)
    (hmem : ∀ k, times k → fullAt k ∈ edges)
    (hfull : ∀ k, times k → Full m e r0 k (fullAt k))
    (hunique : ∀ k, times k → ∀ c ∈ cells,
      Full m e r0 k (reg m e r0 k c) →
        SameEdge m (fullAt k) (reg m e r0 k c))
    (hvisit : ∀ k, times k → ∀ c ∈ cells,
      ∃ j, 0 < j ∧ j ≤ k ∧ m.cellOf (e j) = c)
    (htarget : ∀ k, times k → ∀ c ∈ cells,
      m.cellOf (m.bar (reg m e r0 k c)) ∈ cells)
    (hnlobe : ∀ k, times k → ∀ c ∈ cells,
      c ≠ m.cellOf (fullAt k) →
      c ≠ m.cellOf (m.bar (fullAt k)) →
      m.cellOf (m.bar (reg m e r0 k c)) ≠ c) :
    TreeBlockCert m e r0 times where
  cells := cells
  edges := edges
  fullAt := fullAt
  full_mem := hmem
  full_full := hfull
  rooted := fun k hk => by
    let lw := positiveLastWriteMapOfVisits m e k cells (hvisit k hk)
    apply rootedCells_of_rank m e r0 k (fullAt k) cells
      (recencyRank m e k lw)
    exact rankedToward_of_recency m e r0 hrun hr0 k (fullAt k)
      cells lw (htarget k hk) (hnlobe k hk)
      (fun c hc hl hr =>
        selected_not_full_away_root m e r0 hr0
          (hunique k hk c hc) hl hr)

end Echo
