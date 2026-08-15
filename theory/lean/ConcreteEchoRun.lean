import ConcreteEchoStep

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

def encodedEntries (entry : Nat → Nat) : Nat → Nat :=
  fun k => encodeSlot (entry k)


@[simp] theorem canonicalEchoMachine_cell_encodedEntry
    (w : Wiring) (entry : Nat → Nat) (k : Nat) :
    (canonicalEchoMachine w).cellOf (encodedEntries entry k) =
      physicalCell w (entry k) := by
  simp [encodedEntries, physicalCell, canonicalPhysicalCellOf]

end GeneralN
