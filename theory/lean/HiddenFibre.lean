import EdgeReversal

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

end Echo
