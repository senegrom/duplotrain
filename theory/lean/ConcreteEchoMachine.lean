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

/-- Physical free slots are closed under the jump involution. -/
theorem canonicalEchoSlot_bar
    {w : Wiring} {p : Nat}
    (hp : IsCanonicalEchoSlot w p) :
    IsCanonicalEchoSlot w (wireBar w p) := by
  rcases hp with ⟨hpDesc, hpBranch, hpLink,
    hbarBranch, hbarDesc⟩
  have hback : w.link (wireBar w p) = some p :=
    w.symm _ _ hpLink
  have hbarbar : wireBar w (wireBar w p) = p :=
    wireBar_invol w p
  refine ⟨hbarDesc, hbarBranch, ?_, ?_, ?_⟩
  · rw [hbarbar]
    exact hback
  · rw [hbarbar]
    exact hpBranch
  · rw [hbarbar]
    exact hpDesc

/-- The encoded list of physical free slots is closed under the echo jump
involution. -/
theorem encoded_canonical_slot_bar
    {w : Wiring} {p : Nat}
    (hp : IsCanonicalEchoSlot w p) :
    (canonicalEchoMachine w).bar (encodeSlot p) =
      encodeSlot (wireBar w p) := by
  simp [canonicalEchoMachine]

/-- Every branch in one canonical action has the same echo cell. -/
theorem canonicalAction_cell_constant
    {w : Wiring} {p b : Nat}
    (hp : IsDescentEntry w p)
    (hb : b ∈ entryAction w p) :
    (canonicalEchoMachine w).cellOf (encodeSlot b) =
      (canonicalEchoMachine w).cellOf (encodeSlot p) := by
  simp only [canonicalEchoMachine_cell]
  exact rootCode_eq_of_mem_entryAction hp hb

/-- A realised entry with a proper mouth root is sent by `star` to the code of
its physical landing-root partner. -/
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

/-- Full local mouth compatibility with another realised slot in the partner
tree. -/
theorem canonicalEchoMachine_star_cell
    {w : Wiring} {p f : Nat}
    (hp : IsDescentEntry w p)
    (hproper : ProperMouthRoot w (entryRoot w p))
    (hfRoot : entryRoot w f = entryLanding w p / 3) :
    (canonicalEchoMachine w).star
        ((canonicalEchoMachine w).cellOf (encodeSlot p)) =
      (canonicalEchoMachine w).cellOf (encodeSlot f) := by
  rw [canonicalEchoMachine_star_entry hp hproper]
  simp only [canonicalEchoMachine_cell]
  rw [hfRoot]

/-- The concrete branch word has exactly the canonical echo action. -/
theorem descent_result_eq_canonicalEchoAction
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t')
    (snapshot : List Nat) :
    t' = pinList
      (canonicalEchoAction w (encodeSlot p, snapshot)) t := by
  rw [canonicalEchoAction_encode]
  exact descent_result_eq_entryAction h

/-- Canonical action length remains at most `N`. -/
theorem canonicalEchoAction_length_le
    {w : Wiring} {N p : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3*N ∧ b < 3*N)
    (hp : IsDescentEntry w p)
    (snapshot : List Nat) :
    (canonicalEchoAction w (encodeSlot p, snapshot)).length ≤ N := by
  rw [canonicalEchoAction_encode]
  exact entryAction_length_le hN hp

/-- Encoding a duplicate-free finite free-slot list preserves the concrete
`2*N` cardinality bound. -/
theorem canonicalEchoSlot_list_length_le
    {w : Wiring} {N : Nat} {physicalSlots : List Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3*N ∧ b < 3*N)
    (hnd : physicalSlots.Nodup)
    (hslots : ∀ p ∈ physicalSlots, IsCanonicalEchoSlot w p) :
    (physicalSlots.map encodeSlot).length ≤ 2*N := by
  apply encoded_descent_entry_list_length_le_two_mul hN hnd
  intro p hp
  exact (hslots p hp).1

end GeneralN
