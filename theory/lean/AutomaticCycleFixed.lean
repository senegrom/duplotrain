import AutomaticTreeBlock

/-!
# Equal-sized support blocks are automatically frozen

A connected pseudoforest component with the same number of occupied edges and
cells is unicyclic.  The finite counting theorem `no_full_of_equal_size` shows
that such a non-lobe block has no full edge.  `NoFullFixed` then implies that
all of its registers are constant during a fixed-support epoch.

As a result only tree components and active lobe cells need to appear in the
state code.
-/

namespace Echo

/-- Fixed finite equal-sized support data across a set of times. -/
structure SupportCycleEpoch
    (m : Machine) (e r0 : Nat → Nat) (times : Nat → Prop) where
  cells : List Nat
  edges : List Nat
  cells_nodup : cells.Nodup
  edge_reps : EdgeRepresentatives m edges
  occupied : ∀ k, times k → ∀ s, s ∈ edges → Occupied m e r0 k s
  endpoints : ∀ s, s ∈ edges →
    m.cellOf s ∈ cells ∧ m.cellOf (m.bar s) ∈ cells
  selected_covered : ∀ k, times k → ∀ c, c ∈ cells →
    ∃ s, s ∈ edges ∧ SameEdge m s (reg m e r0 k c)
  cycle_size : edges.length = cells.length
  nonlobe : ∀ s, s ∈ edges → ¬ LobeSlot m s

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- The one-time block underlying the epoch component. -/
def SupportCycleEpoch.at
    (T : SupportCycleEpoch m e r0 times) (k : Nat) (hk : times k) :
    SupportBlockAt m e r0 k where
  cells := T.cells
  edges := T.edges
  cells_nodup := T.cells_nodup
  edge_reps := T.edge_reps
  occupied := T.occupied k hk
  endpoints := T.endpoints
  selected_covered := T.selected_covered k hk

/-- No selected edge in an equal-sized block is full. -/
theorem SupportCycleEpoch.selected_nonfull
    (T : SupportCycleEpoch m e r0 times)
    {k c : Nat} (hk : times k) (hc : c ∈ T.cells) :
    ¬ Full m e r0 k (reg m e r0 k c) := by
  obtain ⟨s, hs, hsame⟩ := T.selected_covered k hk c hc
  have hsnf := no_full_of_equal_size m e r0
    (SupportCycleEpoch.at m e r0 T k hk)
    T.cycle_size T.nonlobe s hs
  intro hfull
  exact hsnf ((full_sameEdge_iff m e r0 hsame).mpr hfull)

/-- No selected edge in the block is a lobe. -/
theorem SupportCycleEpoch.selected_nonlobe
    (T : SupportCycleEpoch m e r0 times)
    {k c : Nat} (hk : times k) (hc : c ∈ T.cells) :
    ¬ LobeSlot m (reg m e r0 k c) := by
  obtain ⟨s, hs, hsame⟩ := T.selected_covered k hk c hc
  intro hlobe
  exact T.nonlobe s hs ((lobe_sameEdge_iff m hsame).mpr hlobe)

/-- **Automatic freezing of a unicyclic non-lobe block.** -/
theorem SupportCycleEpoch.stable
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (T : SupportCycleEpoch m e r0 times)
    {i j : Nat} (hij : i ≤ j)
    (htimes : ∀ k, i ≤ k → k < j → times k)
    (hsupport : ∀ k, i ≤ k → k < j → ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s) :
    ∀ c ∈ T.cells, reg m e r0 j c = reg m e r0 i c := by
  apply nofull_nonlobe_component_stable m e r0 hrun hr0
    T.cells hij hsupport
  · intro k hik hkj c hc
    exact T.selected_nonfull m e r0 (htimes k hik hkj) hc
  · intro k hik hkj c hc
    exact T.selected_nonlobe m e r0 (htimes k hik hkj) hc

end Echo
