import LobeForestBlock

/-!
# Active lobe-forest roots are mouth-pair independent

The trees attached to a lobe root do not weaken the absorption argument.  If
two mouth-partner lobe roots both vary while their lobe edges stay occupied,
`varying_partner_lobes_absorb` still produces a Gray tail.  Therefore, before
that tail, the roots of the varying lobe-forest blocks contain at most one
cell from each `star` pair.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Root list has one entry per block. -/
theorem lobeForestRoots_length
    (blocks : List (SupportLobeForestEpoch m e r0 times)) :
    (lobeForestRoots m e r0 blocks).length = blocks.length := by
  simp [lobeForestRoots]

/-- Before the first Gray tail, varying lobe-forest roots are
`star`-independent. -/
theorem active_lobe_forests_star_independent
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j : Nat} (hij : i ≤ j)
    (blocks : List (SupportLobeForestEpoch m e r0 times))
    (htimes : ∀ k, i ≤ k → k ≤ j → times k)
    (hvar : ∀ B ∈ blocks,
      VariesOnInterval m e r0 i j (B.root m))
    (hnoGray : ∀ k, i < k → k ≤ j → ¬ GrayTail m e r0 k) :
    StarIndependent m (lobeForestRoots m e r0 blocks) := by
  intro c hc hstar
  obtain ⟨B, hB, hBc⟩ := List.mem_map.mp hc
  obtain ⟨D, hD, hDc⟩ := List.mem_map.mp hstar
  have htCell : m.cellOf D.rootSlot =
      m.star (m.cellOf B.rootSlot) := by
    calc
      m.cellOf D.rootSlot = D.root m := rfl
      _ = m.star c := hDc
      _ = m.star (B.root m) := by rw [hBc]
      _ = m.star (m.cellOf B.rootSlot) := rfl
  obtain ⟨k, hik, hkj, htail⟩ :=
    varying_partner_lobes_absorb m e r0 hrun hr0 hij htCell
      B.root_lobe D.root_lobe
      (fun q hiq hqj =>
        B.occupied q (htimes q hiq hqj) B.rootSlot B.root_mem)
      (fun q hiq hqj =>
        D.occupied q (htimes q hiq hqj) D.rootSlot D.root_mem)
      (by simpa [SupportLobeForestEpoch.root] using hvar B hB)
  exact (hnoGray k hik hkj) htail

/-- Quantitative root bound for active lobe-forest blocks. -/
theorem active_lobe_forests_half
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j : Nat} (hij : i ≤ j)
    (allCells : List Nat)
    (blocks : List (SupportLobeForestEpoch m e r0 times))
    (hrootsNodup : (lobeForestRoots m e r0 blocks).Nodup)
    (hrootsSub : ∀ c ∈ lobeForestRoots m e r0 blocks,
      c ∈ allCells)
    (hclosed : StarClosed m allCells)
    (htimes : ∀ k, i ≤ k → k ≤ j → times k)
    (hvar : ∀ B ∈ blocks,
      VariesOnInterval m e r0 i j (B.root m))
    (hnoGray : ∀ k, i < k → k ≤ j → ¬ GrayTail m e r0 k) :
    2 * blocks.length ≤ allCells.length := by
  have hhalf := star_independent_length m allCells
    (lobeForestRoots m e r0 blocks)
    hrootsNodup hrootsSub hclosed
    (active_lobe_forests_star_independent m e r0 hrun hr0 hij
      blocks htimes hvar hnoGray)
  rw [lobeForestRoots_length] at hhalf
  exact hhalf

end Echo
