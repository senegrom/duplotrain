import SupportMove

/-!
# Cell-level edge reversal

Collapse a register state to a function on cells.  At time `k`, define

    nextCell k c = cellOf (bar (reg k (star c))).

For the actually visited cell `c_k = cellOf (e k)`, the machine step says
`nextCell k c_k = c_{k+1}`.  The write made by that step installs the exact
star-reversed arrow at the next time:

    nextCell (k+1) (star c_{k+1}) = star c_k.

Thus every traversed cell-level arrow is immediately reversed, with `star`
applied to both endpoints.  This is the graph-theoretic core of the echo
machine and is independent of slot labels.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The cell reached by following the current register pointer of `star c`
through its jump edge. -/
def nextCell (k c : Nat) : Nat :=
  m.cellOf (m.bar (reg m e r0 k (m.star c)))

/-- The actual run follows `nextCell`. -/
theorem cell_step (hrun : IsRun m e r0) (k : Nat) :
    nextCell m e r0 k (m.cellOf (e k)) = m.cellOf (e (k+1)) := by
  unfold nextCell
  rw [← hrun k]

/-- **Immediate star-reversal.**  After traversing the cell-level arrow
`c_k -> c_{k+1}`, the arrow out of `star c_{k+1}` at the next time points
back to `star c_k`. -/
theorem reversed_arrow
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) :
    nextCell m e r0 (k+1) (m.star (m.cellOf (e (k+1))))
      = m.star (m.cellOf (e k)) := by
  unfold nextCell
  rw [m.star_invol]
  have hw : reg m e r0 (k+1) (m.cellOf (e (k+1))) = e (k+1) :=
    reg_write m e r0 rfl
  rw [hw]
  exact (witness m e r0 hrun hr0 k).1

/-- Slot-level form of the same reversal: after step `k`, the register of the
arrival cell is precisely the arrival slot. -/
theorem reversed_register (k : Nat) :
    reg m e r0 (k+1) (m.cellOf (e (k+1))) = e (k+1) := by
  exact reg_write m e r0 rfl

/-- The reversed arrow is involutively paired with the traversed arrow: taking
`star` of both endpoints recovers the original endpoints. -/
theorem reversed_arrow_endpoints (hrun : IsRun m e r0) (k : Nat) :
    m.star (nextCell m e r0 k (m.cellOf (e k))) =
      m.star (m.cellOf (e (k+1))) := by
  rw [cell_step m e r0 hrun k]

end Echo
