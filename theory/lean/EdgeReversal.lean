import SupportMove

/-!
# Cell-level edge reversal

Collapse a register state to a function on cells.  At time `k`, define

    nextCell k c = cellOf (bar (reg k (star c))).

For the actually visited cell `c_k = cellOf (e k)`, the machine step says
`nextCell k c_k = c_{k+1}`.  The write made by that step installs the exact
star-reversed arrow at the next time:

    nextCell (k+1) (star c_{k+1}) = star c_k.

All other cell-level arrows are unchanged.  Thus a step is literally a
single-arrow reversal, with `star` applied to both endpoints.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The cell reached by following the current register pointer of `star c`
through its jump edge. -/
def nextCell (k c : Nat) : Nat :=
  m.cellOf (m.bar (reg m e r0 k (m.star c)))
end Echo
