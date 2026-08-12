import ConcreteTreeCodes

/-!
# The canonical concrete echo machine

For a realised concrete cascade entry `p`:

* its echo slot is the even code `encodeSlot p`;
* its cell is the paired code of its canonical root;
* its emitted overwrite word is `entryAction w p`;
* jump pairing is the physical branch–branch edge; and
* mouth pairing is `mateNat` on the root codes.

This file proves the local compatibility equations.  The remaining compiler
work is temporal: show that a live physical run decomposes into these maximal
cascades and that each partner descent reads the most recent entry register.
-/

namespace GeneralN

/-- Canonical physical branch-port-to-cell assignment. -/
noncomputable def canonicalPhysicalCellOf (w : Wiring) (p : Nat) : Nat :=
  rootCode w (entryRoot w p)

/-- Total canonical echo machine associated to the concrete wiring. -/
noncomputable def canonicalEchoMachine (w : Wiring) : Echo.Machine :=
  encodedMachine w (canonicalPhysicalCellOf w)

/-- Canonical overwrite word emitted by one finite echo configuration. -/
noncomputable def canonicalEchoAction
    (w : Wiring) (config : Nat × List Nat) : List Nat :=
  entryAction w (decodeSlot config.1)

@[simp] theorem canonicalEchoMachine_cell
    (w : Wiring) (p : Nat) :
    (canonicalEchoMachine w).cellOf (encodeSlot p) =
      rootCode w (entryRoot w p) := by
  simp [canonicalEchoMachine, canonicalPhysicalCellOf]

@[simp] theorem canonicalEchoMachine_bar
    (w : Wiring) (p : Nat) :
    (canonicalEchoMachine w).bar (encodeSlot p) =
      encodeSlot (wireBar w p) := by
  simp [canonicalEchoMachine]

@[simp] theorem canonicalEchoAction_encode
    (w : Wiring) (p : Nat) (snapshot : List Nat) :
    canonicalEchoAction w (encodeSlot p, snapshot) = entryAction w p := by
  unfold canonicalEchoAction decodeSlot encodeSlot
  congr
  omega

/-- A physical free slot is a realised branch entry whose branch edge leads
to another realised branch entry. -/
def IsCanonicalEchoSlot (w : Wiring) (p : Nat) : Prop :=
  IsDescentEntry w p ∧
  p % 3 ≠ 0 ∧
  w.link p = some (wireBar w p) ∧
  (wireBar w p) % 3 ≠ 0 ∧
  IsDescentEntry w (wireBar w p)

theorem canonicalEchoMachine_star_entry
    {w : Wiring} {p : Nat}
    (hp : IsDescentEntry w p)
    (hproper : ProperMouthRoot w (entryRoot w p)) :
    (canonicalEchoMachine w).star
        ((canonicalEchoMachine w).cellOf (encodeSlot p)) =
      rootCode w (entryLanding w p / 3) := by
  rcases hproper with ⟨partner, hmouth, hne⟩
  have hcanonical := entryRoot_mouthPaired hp
  have hpartnerEq : partner = entryLanding w p / 3 :=
    mouthPaired_right_unique hmouth hcanonical
  subst partner
  simp only [canonicalEchoMachine_cell, canonicalEchoMachine,
    encodedMachine, encodedCellOf_encodeSlot, canonicalPhysicalCellOf]
  exact rootCode_mouth_partner hcanonical hne

end GeneralN
