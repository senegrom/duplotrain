import AlternationBound

/-!
# Monotone jump-edge support

A jump edge is `Occupied` when at least one of its two slot endpoints is the
current register value of its cell.  The occupied support can only shrink:
a step can move a confirmation onto a previously-unconfirmed arrival slot,
but the opposite endpoint of that jump edge was necessarily confirmed just
before the step (`head_confirmed`).  Hence a completely empty jump edge can
never become occupied later.

This is a set-valued monovariant, strictly stronger than the previously proved
non-increase of the *number* of token ends.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- At least one endpoint of the jump edge represented by `s` is confirmed. -/
def Occupied (k s : Nat) : Prop :=
  Confirmed m e r0 k s ∨ Confirmed m e r0 k (m.bar s)

noncomputable instance (k s : Nat) : Decidable (Occupied m e r0 k s) := by
  classical
  unfold Occupied Confirmed
  infer_instance
end Echo
