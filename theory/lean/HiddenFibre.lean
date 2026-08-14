import ReversalFacts

/-!
# The hidden fibre of the cell-level projection

`nextCell` forgets the exact slot and remembers only the two endpoint cells of
a jump edge.  This file proves that this is the *only* information it loses.

For step `k`, let

* `new = e(k+1)` be the newly written slot;
* `old = reg k (cellOf new)` be the overwritten slot.

The cell-level arrow function is unchanged exactly when `old` and `new` are
parallel jump edges: their near endpoints lie in the same cell (automatic),
and their `bar` endpoints lie in the same cell.  Thus every productive state
change splits cleanly into either

1. a genuine cell-level mirror reversal, or
2. a move inside one finite parallel-edge fibre.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The register value overwritten at step `k`. -/
def oldSlot (k : Nat) : Nat :=
  reg m e r0 k (m.cellOf (e (k+1)))

/-- Two slots represent parallel jump edges with the same ordered pair of
endpoint cells. -/
def ParallelEdge (s t : Nat) : Prop :=
  m.cellOf s = m.cellOf t ∧
  m.cellOf (m.bar s) = m.cellOf (m.bar t)

/-- The old and new slots always have the same near endpoint cell. -/
theorem old_new_cell
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (k : Nat) :
    m.cellOf (oldSlot m e r0 k) = m.cellOf (e (k+1)) := by
  unfold oldSlot
  exact reg_cell m e r0 hr0 k _

/-- The arrow which can be overwritten at step `k` points through the old
slot's jump edge. -/
theorem mirror_source_before (k : Nat) :
    nextCell m e r0 k (m.star (m.cellOf (e (k+1)))) =
      m.cellOf (m.bar (oldSlot m e r0 k)) := by
  unfold nextCell oldSlot
  rw [m.star_invol]

/-- The new slot's far endpoint is the mouth partner of the preceding cell. -/
theorem new_far_cell
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) :
    m.cellOf (m.bar (e (k+1))) = m.star (m.cellOf (e k)) := by
  exact (witness m e r0 hrun hr0 k).1

/-- If the cell projection stalls, the overwritten and written slots are
parallel edges. -/
theorem parallel_of_mirror_present
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (hpresent : nextCell m e r0 k
      (m.star (m.cellOf (e (k+1)))) = m.star (m.cellOf (e k))) :
    ParallelEdge m (oldSlot m e r0 k) (e (k+1)) := by
  constructor
  · exact old_new_cell m e r0 hr0 k
  · rw [← mirror_source_before m e r0 k, hpresent]
    exact (new_far_cell m e r0 hrun hr0 k).symm

/-- Conversely, parallel old/new edges make the cell projection stall. -/
theorem mirror_present_of_parallel
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (hpar : ParallelEdge m (oldSlot m e r0 k) (e (k+1))) :
    nextCell m e r0 k (m.star (m.cellOf (e (k+1)))) =
      m.star (m.cellOf (e k)) := by
  rw [mirror_source_before m e r0 k]
  rw [hpar.2]
  exact new_far_cell m e r0 hrun hr0 k

/-- Exact characterisation: the complete cell-level arrow function is
unchanged iff the old and new slots are parallel edges. -/
theorem cell_projection_stall_iff_parallel
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) :
    (∀ c, nextCell m e r0 (k+1) c = nextCell m e r0 k c) ↔
      ParallelEdge m (oldSlot m e r0 k) (e (k+1)) := by
  constructor
  · intro hstall
    have hpresent : nextCell m e r0 k
        (m.star (m.cellOf (e (k+1)))) = m.star (m.cellOf (e k)) := by
      have h := hstall (m.star (m.cellOf (e (k+1))))
      rw [reversed_arrow m e r0 hrun hr0 k] at h
      exact h.symm
    exact parallel_of_mirror_present m e r0 hrun hr0 k hpresent
  · intro hpar
    exact nextCell_stall_of_mirror_present m e r0 hrun hr0 k
      (mirror_present_of_parallel m e r0 hrun hr0 k hpar)

/-- A productive hidden-fibre move changes to a genuinely different parallel
slot. -/
theorem productive_parallel_ne {k : Nat}
    (hp : ProductiveStep m e r0 k) :
    oldSlot m e r0 k ≠ e (k+1) := by
  intro h
  apply hp
  exact h.symm

end Echo
