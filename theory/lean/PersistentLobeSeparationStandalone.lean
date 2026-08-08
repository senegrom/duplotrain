import HiddenAbsorb
import StarPairCountingCore

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
def StandaloneLobeVisited (lo hi a : Nat) : Prop :=
  ∃ k, lo ≤ k ∧ k ≤ hi ∧
    (e k = a ∨ e k = m.bar a)

/-- A four-slot tail begins at `k`. -/
def StandaloneFourTailFrom (k : Nat) : Prop :=
  ∃ a b, ∀ j, k ≤ j →
    e j = a ∨ e j = m.bar a ∨
    e j = b ∨ e j = m.bar b

/-- No four-slot tail begins within `[lo,hi]`. -/
def StandaloneNoFourTailIn (lo hi : Nat) : Prop :=
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

/-- **Before absorption, active lobe cells are star-separated.** -/
theorem standaloneActiveLobes_starSeparated
    (hrun : IsRun m e r0)
    (lo hi : Nat) (lobes : List Nat)
    (hnd : (standaloneActiveLobeCells m lobes).Nodup)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hvisit : ∀ a ∈ lobes,
      StandaloneLobeVisited m e r0 lo hi a)
    (hno : StandaloneNoFourTailIn m e r0 lo hi) :
    StarSeparatedCore m (standaloneActiveLobeCells m lobes) := by
  constructor
  · exact hnd
  · intro c hc hstarMem
    obtain ⟨a, ha, hac⟩ := List.mem_map.mp hc
    obtain ⟨b, hb, hbc⟩ := List.mem_map.mp hstarMem
    rcases hvisit a ha with ⟨k, hkLo, hkHi, he | he⟩
    · have hstar : m.star (m.cellOf a) = m.cellOf b := by
        rw [hac, hbc]
      have htail := standalone_partner_lobes_absorb m e r0 hrun
        (hloop a ha) (hloop b hb) hstar he
        (hocc k hkLo hkHi b hb)
      exact (hno k hkLo hkHi) htail
    · let a' := m.bar a
      have ha' : m.cellOf (m.bar a') = m.cellOf a' := by
        dsimp [a']
        rw [m.bar_invol]
        exact (hloop a ha).symm
      have hcellA' : m.cellOf a' = m.cellOf a := by
        dsimp [a']
        exact hloop a ha
      have hstar : m.star (m.cellOf a') = m.cellOf b := by
        rw [hcellA', hac, hbc]
      have htail := standalone_partner_lobes_absorb m e r0 hrun
        ha' (hloop b hb) hstar he
        (hocc k hkLo hkHi b hb)
      exact (hno k hkLo hkHi) htail

/-- Quantitative half-density in a finite star-closed universe. -/
theorem standaloneActiveLobes_half
    (hrun : IsRun m e r0)
    (lo hi : Nat) (lobes cells : List Nat)
    (hnd : (standaloneActiveLobeCells m lobes).Nodup)
    (hcells : cells.Nodup)
    (hclosed : ∀ c ∈ standaloneActiveLobeCells m lobes,
      c ∈ cells ∧ m.star c ∈ cells)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hvisit : ∀ a ∈ lobes,
      StandaloneLobeVisited m e r0 lo hi a)
    (hno : StandaloneNoFourTailIn m e r0 lo hi) :
    2 * lobes.length ≤ cells.length := by
  have hsep := standaloneActiveLobes_starSeparated m e r0 hrun
    lo hi lobes hnd hloop hocc hvisit hno
  have hhalf := starSeparatedCore_count m
    (standaloneActiveLobeCells m lobes) cells
    hsep hcells hclosed
  simpa [standaloneActiveLobeCells] using hhalf

end Echo
