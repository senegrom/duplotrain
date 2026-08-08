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
def physicalCell (w : Wiring) (p : Nat) : Nat :=
  rootCode w (entryRoot w p)

/-- Last physical ascent entry of a cell after entries `0,…,k`. -/
def physicalReg (w : Wiring)
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
  | succ n ih =>
      intro c
      simp [Echo.reg, physicalReg, encodedEntries, encodedInitial,
        physicalCell, canonicalPhysicalCellOf, ih]

/-- Physical initial registers are well-formed exactly when their entries
belong to their indexed root cells. -/
theorem encodedInitial_wellFormed
    (w : Wiring) (initial : Nat → Nat)
    (hinitial : ∀ c, physicalCell w (initial c) = c) :
    ∀ c,
      (canonicalEchoMachine w).cellOf (encodedInitial initial c) = c := by
  intro c
  simp [encodedInitial, physicalCell, canonicalPhysicalCellOf,
    hinitial c]

/-- The physical last-writer recurrence. -/
def IsPhysicalEchoRun (w : Wiring)
    (entry initial : Nat → Nat) : Prop :=
  ∀ k,
    entry (k + 1) =
      wireBar w
        (physicalReg w entry initial k
          (mateNat (physicalCell w (entry k))))

/-- **Physical recurrence transfers to the canonical echo machine.** -/
theorem canonicalEcho_isRun
    (w : Wiring) (entry initial : Nat → Nat)
    (hrun : IsPhysicalEchoRun w entry initial) :
    Echo.IsRun (canonicalEchoMachine w)
      (encodedEntries entry) (encodedInitial initial) := by
  intro k
  have hk := hrun k
  have hencoded := congrArg encodeSlot hk
  simp only [encodedEntries]
  rw [encoded_reg_eq]
  simpa [canonicalEchoMachine, encodedMachine, physicalCell,
    canonicalPhysicalCellOf] using hencoded

/-- A physical register holding a realised entry is encoded as that same
canonical echo slot. -/
theorem encoded_reg_of_physicalReg
    (w : Wiring) (entry initial : Nat → Nat)
    (k c : Nat) :
    Echo.reg (canonicalEchoMachine w)
      (encodedEntries entry) (encodedInitial initial) k c =
      encodeSlot (physicalReg w entry initial k c) :=
  encoded_reg_eq w entry initial k c

/-- The current canonical echo configuration contains the physical entry and
the encoded last-writer registers. -/
theorem canonical_config_fst
    (w : Wiring) (entry initial : Nat → Nat)
    (cells : List Nat) (k : Nat) :
    (Echo.configSnap (canonicalEchoMachine w)
      (encodedEntries entry) (encodedInitial initial) cells k).1 =
      encodeSlot (entry k) := by
  rfl

end GeneralN
