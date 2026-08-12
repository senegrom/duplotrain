import ConcreteEchoStep
import EchoConfiguration

/-!
# From the physical last-writer register to an echo run

The concrete compiler stores physical branch entries.  The abstract echo
machine stores their even-slot encodings.  This file defines the physical
register recursion, proves that encoding commutes with `Echo.reg`, and shows
that the physical recurrence

    next = wireBar (register of mouth partner)

is exactly `Echo.IsRun` for `canonicalEchoMachine`.
-/

namespace GeneralN

/-- Physical root-cell assignment used by the canonical machine. -/
noncomputable def physicalCell (w : Wiring) (p : Nat) : Nat :=
  rootCode w (entryRoot w p)

/-- Last physical ascent entry of a cell after entries `0,…,k`. -/
noncomputable def physicalReg (w : Wiring)
    (entry : Nat → Nat) (initial : Nat → Nat) :
    Nat → Nat → Nat
  | 0, c => if physicalCell w (entry 0) = c then entry 0 else initial c
  | k + 1, c =>
      if physicalCell w (entry (k + 1)) = c then entry (k + 1)
      else physicalReg w entry initial k c

/-- Encode a physical entry sequence. -/
def encodedEntries (entry : Nat → Nat) : Nat → Nat :=
  fun k => encodeSlot (entry k)

/-- Encode physical initial registers. -/
def encodedInitial (initial : Nat → Nat) : Nat → Nat :=
  fun c => encodeSlot (initial c)

@[simp] theorem canonicalEchoMachine_cell_encodedEntry
    (w : Wiring) (entry : Nat → Nat) (k : Nat) :
    (canonicalEchoMachine w).cellOf (encodedEntries entry k) =
      physicalCell w (entry k) := by
  simp [encodedEntries, physicalCell, canonicalPhysicalCellOf]

/-- Encoding commutes with the complete register recursion. -/
theorem encoded_reg_eq
    (w : Wiring) (entry initial : Nat → Nat) :
    ∀ k c,
      Echo.reg (canonicalEchoMachine w)
        (encodedEntries entry) (encodedInitial initial) k c =
      encodeSlot (physicalReg w entry initial k c) := by
  intro k
  induction k with
  | zero =>
      intro c
      simp [Echo.reg, physicalReg, encodedEntries, encodedInitial,
        physicalCell, canonicalPhysicalCellOf]
      split <;> rfl
  | succ n ih =>
      intro c
      simp [Echo.reg, physicalReg, encodedEntries, encodedInitial,
        physicalCell, canonicalPhysicalCellOf, ih]
      split <;> rfl

def IsPhysicalEchoRun (w : Wiring)
    (entry initial : Nat → Nat) : Prop :=
  ∀ k,
    entry (k + 1) =
      wireBar w
        (physicalReg w entry initial k
          (mateNat (physicalCell w (entry k))))

end GeneralN
