import ConcreteFiniteBounds
import EchoMachine

/-!
# A total echo machine built from concrete ports

Concrete free branch ports are encoded as even natural numbers.  Odd numbers
are reserved for initial/synthetic slots.  This separates the totality needed
by `Echo.Machine` from the finite set of physical ports used by a run:

* `encodeSlot p = 2*p`;
* the concrete track involution acts on even slots;
* odd slots are fixed by the jump involution;
* a caller-provided physical cell map is read on even slots; and
* odd slot `2*c+1` belongs definitionally to cell `c`.

Cells are globally mouth-paired by the elementary fixed-point-free involution
`mateNat`, which swaps 0/1, 2/3, 4/5, ... .  A concrete forest catalogue only
has to assign paired trees consecutive codes.
-/

namespace GeneralN

/-- Swap consecutive natural numbers: 0↔1, 2↔3, ... . -/
def mateNat : Nat → Nat
  | 0 => 1
  | 1 => 0
  | n + 2 => mateNat n + 2

theorem mateNat_invol : ∀ n, mateNat (mateNat n) = n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simp [mateNat, mateNat_invol n]

theorem mateNat_ne : ∀ n, mateNat n ≠ n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by
      intro h
      have h' : mateNat n = n := by
        simpa [mateNat] using h
      exact mateNat_ne n h'

/-- Encode a physical branch port as an even echo slot. -/
def encodeSlot (p : Nat) : Nat := 2 * p

/-- A canonical odd slot belonging to cell `c`. -/
def syntheticSlot (c : Nat) : Nat := 2 * c + 1

/-- Decode the physical port carried by an even echo slot. -/
def decodeSlot (s : Nat) : Nat := s / 2

/-- Lift the concrete partial wiring involution to all echo slots.  Even slots
follow physical track edges; odd slots are fixed. -/
def encodedBar (w : Wiring) (s : Nat) : Nat :=
  if s % 2 = 0 then encodeSlot (wireBar w (decodeSlot s)) else s

theorem encodedBar_encodeSlot (w : Wiring) (p : Nat) :
    encodedBar w (encodeSlot p) = encodeSlot (wireBar w p) := by
  unfold encodedBar encodeSlot decodeSlot
  have heven : (2 * p) % 2 = 0 := by omega
  rw [if_pos heven]
  congr
  omega

theorem encodedBar_syntheticSlot (w : Wiring) (c : Nat) :
    encodedBar w (syntheticSlot c) = syntheticSlot c := by
  unfold encodedBar syntheticSlot
  have hodd : (2 * c + 1) % 2 ≠ 0 := by omega
  rw [if_neg hodd]

/-- The lifted jump map is an involution on every natural slot. -/
theorem encodedBar_invol (w : Wiring) (s : Nat) :
    encodedBar w (encodedBar w s) = s := by
  by_cases hs : s % 2 = 0
  · have hsEq : encodeSlot (decodeSlot s) = s := by
      unfold encodeSlot decodeSlot
      omega
    rw [← hsEq, encodedBar_encodeSlot,
      encodedBar_encodeSlot, wireBar_invol]
  · simp [encodedBar, hs]

/-- Lift a physical branch-port-to-cell assignment to all echo slots. -/
def encodedCellOf (physicalCellOf : Nat → Nat) (s : Nat) : Nat :=
  if s % 2 = 0 then physicalCellOf (decodeSlot s)
  else (s - 1) / 2

theorem encodedCellOf_encodeSlot
    (physicalCellOf : Nat → Nat) (p : Nat) :
    encodedCellOf physicalCellOf (encodeSlot p) = physicalCellOf p := by
  unfold encodedCellOf encodeSlot decodeSlot
  have heven : (2 * p) % 2 = 0 := by omega
  rw [if_pos heven]
  congr
  omega

theorem encodedCellOf_syntheticSlot
    (physicalCellOf : Nat → Nat) (c : Nat) :
    encodedCellOf physicalCellOf (syntheticSlot c) = c := by
  unfold encodedCellOf syntheticSlot
  have hodd : (2 * c + 1) % 2 ≠ 0 := by omega
  rw [if_neg hodd]
  omega

/-- The total echo machine associated to a physical wiring and a cell
assignment on physical branch ports. -/
def encodedMachine (w : Wiring)
    (physicalCellOf : Nat → Nat) : Echo.Machine where
  cellOf := encodedCellOf physicalCellOf
  star := mateNat
  bar := encodedBar w
  star_invol := mateNat_invol
  star_ne := mateNat_ne
  bar_invol := encodedBar_invol w

@[simp] theorem encodedMachine_cell_encode
    (w : Wiring) (physicalCellOf : Nat → Nat) (p : Nat) :
    (encodedMachine w physicalCellOf).cellOf (encodeSlot p) =
      physicalCellOf p :=
  encodedCellOf_encodeSlot physicalCellOf p

@[simp] theorem encodedMachine_cell_synthetic
    (w : Wiring) (physicalCellOf : Nat → Nat) (c : Nat) :
    (encodedMachine w physicalCellOf).cellOf (syntheticSlot c) = c :=
  encodedCellOf_syntheticSlot physicalCellOf c

@[simp] theorem encodedMachine_bar_encode
    (w : Wiring) (physicalCellOf : Nat → Nat) (p : Nat) :
    (encodedMachine w physicalCellOf).bar (encodeSlot p) =
      encodeSlot (wireBar w p) :=
  encodedBar_encodeSlot w p

@[simp] theorem encodedMachine_bar_synthetic
    (w : Wiring) (physicalCellOf : Nat → Nat) (c : Nat) :
    (encodedMachine w physicalCellOf).bar (syntheticSlot c) =
      syntheticSlot c :=
  encodedBar_syntheticSlot w c

theorem encodeSlot_injective : Function.Injective encodeSlot := by
  intro p q h
  unfold encodeSlot at h
  omega
end GeneralN
