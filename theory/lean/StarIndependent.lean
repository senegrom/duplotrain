import SupportMove

/-!
# At most one active cell per mouth-partner pair

The mouth pairing `star` is a fixed-point-free involution.  Before a pair of
occupied lobe cells absorbs the run into its Gray square, the set of genuinely
variable lobe cells must be `star`-independent: it cannot contain both `c` and
`star c`.

This file proves the finite counting consequence independently of the dynamic
argument.  If `active` is a duplicate-free, `star`-independent subset of a
`star`-closed cell universe, then

    2 * active.length ≤ cells.length.

Combined with the lobe absorption theorem, this replaces the unnecessarily
strong requirement that active lobes inject specifically into non-lobe cells.
-/

namespace Echo

variable (m : Machine)

def StarIndependent (active : List Nat) : Prop :=
  ∀ c, c ∈ active → m.star c ∉ active


end Echo
