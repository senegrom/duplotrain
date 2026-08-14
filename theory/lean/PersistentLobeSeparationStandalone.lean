import HiddenFibre

/-!
# Active lobe separation before the Gray tail

If a visited occupied lobe has an occupied lobe in its mouth-partner cell, the
existing `absorb_entries` theorem traps the future in four slots.  Thus, before
any such tail begins, the active lobe cells form a star-separated list and
occupy at most half of the finite cell universe.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One endpoint of the lobe is visited during the interval. -/
def StandaloneLobeVisited
    (m : Machine) (e r0 : Nat → Nat)
    (lo hi a : Nat) : Prop :=
  ∃ k, lo ≤ k ∧ k ≤ hi ∧
    (e k = a ∨ e k = m.bar a)

/-- A four-slot tail begins at `k`. -/
def StandaloneFourTailFrom
    (m : Machine) (e r0 : Nat → Nat)
    (k : Nat) : Prop :=
  ∃ a b, ∀ j, k ≤ j →
    e j = a ∨ e j = m.bar a ∨
    e j = b ∨ e j = m.bar b

/-- No four-slot tail begins within `[lo,hi]`. -/
def StandaloneNoFourTailIn
    (m : Machine) (e r0 : Nat → Nat)
    (lo hi : Nat) : Prop :=
  ∀ k, lo ≤ k → k ≤ hi →
    ¬ StandaloneFourTailFrom m e r0 k

/-- Occupancy of a lobe determines one of its two endpoint registers. -/
theorem standalone_occupied_lobe_cases
    {k a : Nat}
    (hloop : m.cellOf (m.bar a) = m.cellOf a)
    (hocc : Occupied m e r0 k a) :
    reg m e r0 k (m.cellOf a) = a ∨
      reg m e r0 k (m.cellOf a) = m.bar a := by
  rcases hocc with ha | hb
  · left
    unfold Confirmed at ha
    exact ha
  · right
    unfold Confirmed at hb
    rw [hloop] at hb
    exact hb

/-- A visited lobe and an occupied partner lobe force absorption. -/
theorem standalone_partner_lobes_absorb
    (hrun : IsRun m e r0)
    {k a b : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hstar : m.star (m.cellOf a) = m.cellOf b)
    (he : e k = a)
    (hocc : Occupied m e r0 k b) :
    StandaloneFourTailFrom m e r0 k := by
  have hreg := standalone_occupied_lobe_cases m e r0 hb hocc
  exact ⟨a, b, absorb_entries m e r0 hrun
    ha hb hstar he hreg⟩

/-- Cells represented by active lobe slots. -/
def standaloneActiveLobeCells (lobes : List Nat) : List Nat :=
  lobes.map m.cellOf

end Echo
