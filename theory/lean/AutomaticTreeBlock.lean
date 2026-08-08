import SupportTreeFull

/-!
# Tree blocks are automatic from finite fixed-support data

This module closes the remaining local gap between a finite support component
and the replay code used by `CertifiedEpochBound`.

A `SupportTreeEpoch` gives the same finite cell/edge block throughout a set of
times, with `edges + 1 = cells`, no lobe edges, and every listed cell already
visited.  `SupportTreeFull` supplies the unique full edge at each time;
`RecencyTreeBlock` then supplies the rooted orientation certificate from last-
write recency.  No rank, root path, or full-edge choice is supplied by hand.
-/

namespace Echo

/-- Fixed finite tree-support data across a set of times. -/
structure SupportTreeEpoch
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
  tree_size : edges.length + 1 = cells.length
  nonlobe : ∀ s, s ∈ edges → ¬ LobeSlot m s
  positive_visit : ∀ k, times k → ∀ c ∈ cells,
    ∃ j, 0 < j ∧ j ≤ k ∧ m.cellOf (e j) = c

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- The one-time support block underlying an epoch block. -/
def SupportTreeEpoch.at
    (T : SupportTreeEpoch m e r0 times) (k : Nat) (hk : times k) :
    SupportBlockAt m e r0 k where
  cells := T.cells
  edges := T.edges
  cells_nodup := T.cells_nodup
  edge_reps := T.edge_reps
  occupied := T.occupied k hk
  endpoints := T.endpoints
  selected_covered := T.selected_covered k hk

/-- Fullness is invariant under changing the representative of a physical
jump edge. -/
theorem full_sameEdge_iff {k s t : Nat}
    (h : SameEdge m s t) :
    Full m e r0 k s ↔ Full m e r0 k t := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · unfold Full
    rw [m.bar_invol]
    exact and_comm

/-- The lobe property is likewise physical-edge invariant. -/
theorem lobe_sameEdge_iff {s t : Nat}
    (h : SameEdge m s t) :
    LobeSlot m s ↔ LobeSlot m t := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact (lobe_bar m).symm

/-- Noncomputably choose the unique full edge at a time in the epoch.  Outside
the epoch the value is irrelevant and set to zero. -/
noncomputable def SupportTreeEpoch.fullAt
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (T : SupportTreeEpoch m e r0 times) (k : Nat) : Nat := by
  classical
  exact if hk : times k then
    (exists_unique_full_of_tree_size m e r0 hr0 (SupportTreeEpoch.at m e r0 T k hk)
      T.tree_size T.nonlobe).choose
  else 0

theorem SupportTreeEpoch.fullAt_mem
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (T : SupportTreeEpoch m e r0 times)
    {k : Nat} (hk : times k) :
    T.fullAt m e r0 hr0 k ∈ T.edges := by
  classical
  unfold SupportTreeEpoch.fullAt
  rw [dif_pos hk]
  exact (exists_unique_full_of_tree_size m e r0 hr0 (SupportTreeEpoch.at m e r0 T k hk)
    T.tree_size T.nonlobe).choose_spec.1

theorem SupportTreeEpoch.fullAt_full
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (T : SupportTreeEpoch m e r0 times)
    {k : Nat} (hk : times k) :
    Full m e r0 k (T.fullAt m e r0 hr0 k) := by
  classical
  unfold SupportTreeEpoch.fullAt
  rw [dif_pos hk]
  exact (exists_unique_full_of_tree_size m e r0 hr0 (SupportTreeEpoch.at m e r0 T k hk)
    T.tree_size T.nonlobe).choose_spec.2.1

theorem SupportTreeEpoch.fullAt_unique
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (T : SupportTreeEpoch m e r0 times)
    {k : Nat} (hk : times k)
    {g : Nat} (hg : g ∈ T.edges)
    (hgf : Full m e r0 k g) :
    g = T.fullAt m e r0 hr0 k := by
  classical
  unfold SupportTreeEpoch.fullAt
  rw [dif_pos hk]
  exact (exists_unique_full_of_tree_size m e r0 hr0 (SupportTreeEpoch.at m e r0 T k hk)
    T.tree_size T.nonlobe).choose_spec.2.2 g hg hgf

/-- Following a selected edge stays inside the finite block. -/
theorem SupportTreeEpoch.selected_target_mem
    (T : SupportTreeEpoch m e r0 times)
    {k c : Nat} (hk : times k) (hc : c ∈ T.cells) :
    m.cellOf (m.bar (reg m e r0 k c)) ∈ T.cells := by
  obtain ⟨s, hs, hsame⟩ := T.selected_covered k hk c hc
  rcases hsame with h | h
  · rw [h]
    exact (T.endpoints s hs).2
  · rw [h, m.bar_invol]
    exact (T.endpoints s hs).1

/-- A selected edge in this block is non-lobed. -/
theorem SupportTreeEpoch.selected_nonlobe
    (T : SupportTreeEpoch m e r0 times)
    {k c : Nat} (hk : times k) (hc : c ∈ T.cells) :
    ¬ LobeSlot m (reg m e r0 k c) := by
  obtain ⟨s, hs, hsame⟩ := T.selected_covered k hk c hc
  intro hlobe
  exact T.nonlobe s hs ((lobe_sameEdge_iff m hsame).mpr hlobe)

/-- Any full selected edge of a listed cell is the chosen unique root edge. -/
theorem SupportTreeEpoch.selected_full_same_root
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (T : SupportTreeEpoch m e r0 times)
    {k c : Nat} (hk : times k) (hc : c ∈ T.cells)
    (hfull : Full m e r0 k (reg m e r0 k c)) :
    SameEdge m (T.fullAt m e r0 hr0 k) (reg m e r0 k c) := by
  obtain ⟨s, hs, hsame⟩ := T.selected_covered k hk c hc
  have hsfull : Full m e r0 k s :=
    (full_sameEdge_iff m e r0 hsame).mpr hfull
  have hroot : s = T.fullAt m e r0 hr0 k :=
    T.fullAt_unique m e r0 hr0 hk hs hsfull
  rw [← hroot]
  exact hsame

/-- **Automatic certified tree block.** -/
noncomputable def SupportTreeEpoch.toTreeBlock
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (T : SupportTreeEpoch m e r0 times) :
    TreeBlockCert m e r0 times :=
  recencyTreeBlock m e r0 hrun hr0 times T.cells T.edges
    (T.fullAt m e r0 hr0)
    (fun k hk => T.fullAt_mem m e r0 hr0 hk)
    (fun k hk => T.fullAt_full m e r0 hr0 hk)
    (fun k hk c hc hfull =>
      T.selected_full_same_root m e r0 hr0 hk hc hfull)
    T.positive_visit
    (fun k hk c hc => T.selected_target_mem m e r0 hk hc)
    (fun k hk c hc _ _ h =>
      T.selected_nonlobe m e r0 hk hc (by
        unfold LobeSlot
        exact h.trans (reg_cell m e r0 hr0 k c).symm))

end Echo
