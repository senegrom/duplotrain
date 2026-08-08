import HiddenAbsorb

/-!
# Active lobe cells are star-separated before absorption

A lobe representative is active on an interval when one of its endpoints is
visited during the interval, while its edge remains occupied throughout.  If
two such lobe cells are mouth partners, the visit to the first one and the
partner register immediately satisfy `absorb_entries`; the future walk is
trapped in four slots.  Therefore, before any four-slot tail begins, the active
lobe cells are star-separated.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- One endpoint of the lobe is visited in the interval. -/
def LobeVisited (lo hi a : Nat) : Prop :=
  ∃ k, lo ≤ k ∧ k ≤ hi ∧
    (e k = a ∨ e k = m.bar a)

/-- A four-slot tail begins at time `k`. -/
def FourSlotTailFrom (k : Nat) : Prop :=
  ∃ a b, ∀ j, k ≤ j →
    e j = a ∨ e j = m.bar a ∨
    e j = b ∨ e j = m.bar b

/-- No four-slot tail starts inside the interval. -/
def NoFourSlotTailIn (lo hi : Nat) : Prop :=
  ∀ k, lo ≤ k → k ≤ hi → ¬ FourSlotTailFrom m e r0 k

/-- Occupancy of a lobe restricts its register to the two endpoints. -/
theorem occupied_lobe_reg_cases_core
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

/-- Visiting one lobe while an occupied partner lobe is present forces the
four-slot tail. -/
theorem partner_lobe_visit_absorbs
    (hrun : IsRun m e r0)
    {k a b : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hstar : m.star (m.cellOf a) = m.cellOf b)
    (he : e k = a)
    (hocc : Occupied m e r0 k b) :
    FourSlotTailFrom m e r0 k := by
  have hreg := occupied_lobe_reg_cases_core m e r0 hb hocc
  exact ⟨a, b, absorb_entries m e r0 hrun
    ha hb hstar he hreg⟩

/-- Lobe cells represented by the slot list. -/
def activeLobeCells (lobes : List Nat) : List Nat :=
  lobes.map m.cellOf

/-- **Pre-absorption star separation.** -/
theorem activeLobeCells_starSeparated
    (hrun : IsRun m e r0)
    (lo hi : Nat) (lobes : List Nat)
    (hnd : (activeLobeCells m lobes).Nodup)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hvisit : ∀ a ∈ lobes, LobeVisited m e r0 lo hi a)
    (hno : NoFourSlotTailIn m e r0 lo hi) :
    StarSeparated m (activeLobeCells m lobes) := by
  constructor
  · exact hnd
  · intro c hc hstarMem
    obtain ⟨a, ha, hac⟩ := List.mem_map.mp hc
    obtain ⟨b, hb, hbc⟩ := List.mem_map.mp hstarMem
    rcases hvisit a ha with ⟨k, hkLo, hkHi, he | he⟩
    · have hstar : m.star (m.cellOf a) = m.cellOf b := by
        rw [hac, hbc]
      have htail := partner_lobe_visit_absorbs m e r0 hrun
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
      have he' : e k = a' := by
        exact he
      have htail := partner_lobe_visit_absorbs m e r0 hrun
        ha' (hloop b hb) hstar he'
        (hocc k hkLo hkHi b hb)
      exact (hno k hkLo hkHi) htail

end Echo
