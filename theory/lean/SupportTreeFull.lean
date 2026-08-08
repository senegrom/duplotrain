import NoFullFixed

/-!
# A finite tree-sized support block has a unique full edge

This is the static counting lemma needed to manufacture the `fullAt` field of
`recencyTreeBlock`.  A support block lists cells and one representative of each
occupied physical jump edge.  Every cell's selected register lies on one of
those edges.

If no edge were full, assigning each cell to its selected physical edge would
be injective.  Hence a block with `edges + 1 = cells` must contain a full edge.
If two distinct edges were full, one can choose both confirmed endpoints of
each while choosing one confirmed endpoint of every other occupied edge; this
would inject `edges + 2` objects into only `cells = edges + 1` cells.  Thus the
full edge is unique.
-/

namespace Echo

/-- Finite support data at one time.  Connectivity is not needed by the
counting proof; the tree-size equation is supplied separately. -/
structure SupportBlockAt
    (m : Machine) (e r0 : Nat → Nat) (k : Nat) where
  cells : List Nat
  edges : List Nat
  cells_nodup : cells.Nodup
  edge_reps : EdgeRepresentatives m edges
  occupied : ∀ s, s ∈ edges → Occupied m e r0 k s
  endpoints : ∀ s, s ∈ edges →
    m.cellOf s ∈ cells ∧ m.cellOf (m.bar s) ∈ cells
  selected_covered : ∀ c, c ∈ cells →
    ∃ s, s ∈ edges ∧ SameEdge m s (reg m e r0 k c)

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The physical support edge selected by a listed cell. -/
noncomputable def selectedEdge
    {k : Nat} (B : SupportBlockAt m e r0 k) (c : Nat) : Nat := by
  classical
  exact if hc : c ∈ B.cells then
    (B.selected_covered c hc).choose
  else 0

theorem selectedEdge_mem
    {k : Nat} (B : SupportBlockAt m e r0 k)
    {c : Nat} (hc : c ∈ B.cells) :
    selectedEdge m e r0 B c ∈ B.edges := by
  classical
  unfold selectedEdge
  rw [dif_pos hc]
  exact (B.selected_covered c hc).choose_spec.1

theorem selectedEdge_same
    {k : Nat} (B : SupportBlockAt m e r0 k)
    {c : Nat} (hc : c ∈ B.cells) :
    SameEdge m (selectedEdge m e r0 B c) (reg m e r0 k c) := by
  classical
  unfold selectedEdge
  rw [dif_pos hc]
  exact (B.selected_covered c hc).choose_spec.2

/-- Under absence of full edges, different cells select different physical
edges. -/
theorem selectedEdge_injective_of_nofull
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k : Nat} (B : SupportBlockAt m e r0 k)
    (hnfull : ∀ s, s ∈ B.edges → ¬ Full m e r0 k s)
    {c d : Nat} (hc : c ∈ B.cells) (hd : d ∈ B.cells)
    (hedge : selectedEdge m e r0 B c = selectedEdge m e r0 B d) :
    c = d := by
  let f := selectedEdge m e r0 B c
  have hfmem : f ∈ B.edges := selectedEdge_mem m e r0 B hc
  have hcsel := selectedEdge_same m e r0 B hc
  have hdsel := selectedEdge_same m e r0 B hd
  rw [← hedge] at hdsel
  change SameEdge m f (reg m e r0 k c) at hcsel
  change SameEdge m f (reg m e r0 k d) at hdsel
  have hccell := reg_cell m e r0 hr0 k c
  have hdcell := reg_cell m e r0 hr0 k d
  rcases hcsel with hcsel | hcsel <;>
    rcases hdsel with hdsel | hdsel
  · rw [hcsel] at hccell
    rw [hdsel] at hdcell
    exact hccell.symm.trans hdcell
  · have hfc : m.cellOf f = c := by
      calc
        m.cellOf f = m.cellOf (reg m e r0 k c) :=
          congrArg m.cellOf hcsel.symm
        _ = c := hccell
    have hbd : m.cellOf (m.bar f) = d := by
      calc
        m.cellOf (m.bar f) = m.cellOf (reg m e r0 k d) :=
          congrArg m.cellOf hdsel.symm
        _ = d := hdcell
    have hcf : Confirmed m e r0 k f := by
      unfold Confirmed
      rw [hfc]
      exact hcsel
    have hdb : Confirmed m e r0 k (m.bar f) := by
      unfold Confirmed
      rw [hbd]
      exact hdsel
    exact False.elim (hnfull f hfmem ⟨hcf, hdb⟩)
  · have hbc : m.cellOf (m.bar f) = c := by
      calc
        m.cellOf (m.bar f) = m.cellOf (reg m e r0 k c) :=
          congrArg m.cellOf hcsel.symm
        _ = c := hccell
    have hfd : m.cellOf f = d := by
      calc
        m.cellOf f = m.cellOf (reg m e r0 k d) :=
          congrArg m.cellOf hdsel.symm
        _ = d := hdcell
    have hcb : Confirmed m e r0 k (m.bar f) := by
      unfold Confirmed
      rw [hbc]
      exact hcsel
    have hdf : Confirmed m e r0 k f := by
      unfold Confirmed
      rw [hfd]
      exact hdsel
    exact False.elim (hnfull f hfmem ⟨hdf, hcb⟩)
  · rw [hcsel] at hccell
    rw [hdsel] at hdcell
    exact hccell.symm.trans hdcell

private theorem nodup_map_on_cells
    {f : Nat → Nat} {cells : List Nat}
    (hinj : ∀ c, c ∈ cells → ∀ d, d ∈ cells → f c = f d → c = d)
    (hnd : cells.Nodup) :
    (cells.map f).Nodup := by
  induction cells with
  | nil => simp
  | cons c rest ih =>
      simp only [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨d, hd, hfd⟩ := List.mem_map.mp hm
        have hcd := hinj c List.mem_cons_self d
          (List.mem_cons_of_mem _ hd) hfd.symm
        exact hnd.1 (hcd ▸ hd)
      · exact ih
          (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx)
            y (List.mem_cons_of_mem _ hy)) hnd.2

private theorem nodup_subset_length_nat_tree {l S : List Nat}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) :
    l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- If a support block has no full edge, its cells inject into its edges. -/
theorem cells_le_edges_of_nofull
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k : Nat} (B : SupportBlockAt m e r0 k)
    (hnfull : ∀ s, s ∈ B.edges → ¬ Full m e r0 k s) :
    B.cells.length ≤ B.edges.length := by
  have hnd : (B.cells.map (selectedEdge m e r0 B)).Nodup :=
    nodup_map_on_cells
      (fun c hc d hd =>
        selectedEdge_injective_of_nofull m e r0 hr0 B hnfull hc hd)
      B.cells_nodup
  have hsub : ∀ s ∈ B.cells.map (selectedEdge m e r0 B),
      s ∈ B.edges := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    exact selectedEdge_mem m e r0 B hc
  have hle := nodup_subset_length_nat_tree hnd hsub
  simpa only [List.length_map] using hle

/-- A tree-sized support block contains at least one full edge. -/
theorem exists_full_of_tree_size
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k : Nat} (B : SupportBlockAt m e r0 k)
    (hsize : B.edges.length + 1 = B.cells.length) :
    ∃ f, f ∈ B.edges ∧ Full m e r0 k f := by
  by_cases hex : ∃ f, f ∈ B.edges ∧ Full m e r0 k f
  · exact hex
  · have hnofull : ∀ s, s ∈ B.edges → ¬ Full m e r0 k s := by
      intro s hs hf
      exact hex ⟨s, hs, hf⟩
    have hle := cells_le_edges_of_nofull m e r0 hr0 B hnofull
    omega

/-- The chosen endpoint is the represented endpoint whenever that endpoint is
confirmed. -/
theorem chosenEndpoint_eq_of_confirmed {k s : Nat}
    (h : Confirmed m e r0 k s) :
    chosenEndpoint m e r0 k s = s := by
  classical
  unfold chosenEndpoint
  rw [if_pos h]

/-- The chosen confirmed endpoint list contains no duplicate slots. -/
theorem chosenEndpoints_nodup
    {k : Nat} (B : SupportBlockAt m e r0 k) :
    (B.edges.map (chosenEndpoint m e r0 k)).Nodup := by
  apply nodup_map_on_cells
  · intro s hs t ht heq
    have hst : SameEdge m s t := by
      have h1 := chosenEndpoint_sameEdge m e r0 k s
      have h2 := sameEdge_symm m
        (chosenEndpoint_sameEdge m e r0 k t)
      rw [← heq] at h2
      exact sameEdge_trans m h1 h2
    exact B.edge_reps.2 s hs t ht hst
  · exact B.edge_reps.1

/-- The opposite endpoint of a full non-lobe edge is not already the chosen
endpoint of any support representative. -/
theorem bar_full_not_mem_chosen
    {k : Nat} (B : SupportBlockAt m e r0 k)
    {f : Nat} (hfmem : f ∈ B.edges)
    (hfnlobe : ¬ LobeSlot m f)
    (hfull : Full m e r0 k f) :
    m.bar f ∉ B.edges.map (chosenEndpoint m e r0 k) := by
  intro hm
  obtain ⟨s, hs, heq⟩ := List.mem_map.mp hm
  have hsf : SameEdge m s f := by
    have h1 := chosenEndpoint_sameEdge m e r0 k s
    rw [heq] at h1
    exact sameEdge_trans m h1
      (sameEdge_symm m (sameEdge_bar m f))
  have hsfEq : s = f := B.edge_reps.2 s hs f hfmem hsf
  have hchoose : chosenEndpoint m e r0 k f = f :=
    chosenEndpoint_eq_of_confirmed m e r0 hfull.1
  rw [hsfEq, hchoose] at heq
  have hfb : f = m.bar f := heq
  apply hfnlobe
  unfold LobeSlot
  rw [← hfb]

/-- The jump involution is injective. -/
theorem bar_injective : Function.Injective m.bar := by
  intro s t h
  have h' := congrArg m.bar h
  simpa only [m.bar_invol] using h'

private theorem confirmed_cells_nodup
    {k : Nat} {slots : List Nat}
    (hnd : slots.Nodup)
    (hconf : ∀ s ∈ slots, Confirmed m e r0 k s) :
    (slots.map m.cellOf).Nodup := by
  apply nodup_map_on_cells
  · intro s hs t ht hcell
    exact confirmed_same_cell_eq m e r0
      (hconf s hs) (hconf t ht) hcell
  · exact hnd

/-- A tree-sized non-lobe support block has at most one full physical edge. -/
theorem full_unique_of_tree_size
    {k : Nat} (B : SupportBlockAt m e r0 k)
    (hsize : B.edges.length + 1 = B.cells.length)
    (hnlobe : ∀ s, s ∈ B.edges → ¬ LobeSlot m s)
    {f g : Nat}
    (hfmem : f ∈ B.edges) (hgmem : g ∈ B.edges)
    (hffull : Full m e r0 k f) (hgfull : Full m e r0 k g) :
    f = g := by
  by_cases hfg : f = g
  · exact hfg
  · exfalso
    let base := B.edges.map (chosenEndpoint m e r0 k)
    let extra := [m.bar f, m.bar g]
    let slots := base ++ extra
    have hbase : base.Nodup := by
      dsimp [base]
      exact chosenEndpoints_nodup m e r0 B
    have hbarf : m.bar f ∉ base := by
      dsimp [base]
      exact bar_full_not_mem_chosen m e r0 B hfmem (hnlobe f hfmem) hffull
    have hbarg : m.bar g ∉ base := by
      dsimp [base]
      exact bar_full_not_mem_chosen m e r0 B hgmem (hnlobe g hgmem) hgfull
    have hbars : m.bar f ≠ m.bar g := by
      intro h
      exact hfg (bar_injective m h)
    have hextra : extra.Nodup := by
      dsimp [extra]
      simp [hbars]
    have hslots : slots.Nodup := by
      dsimp [slots]
      rw [List.nodup_append]
      refine ⟨hbase, hextra, ?_⟩
      intro a ha b hb hab
      dsimp [extra] at hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · apply hbarf
        simpa [hab] using ha
      · rcases hb with rfl | hb
        · apply hbarg
          simpa [hab] using ha
        · cases hb
    have hconf : ∀ s ∈ slots, Confirmed m e r0 k s := by
      intro s hs
      dsimp [slots] at hs
      simp only [List.mem_append] at hs
      rcases hs with hs | hs
      · dsimp [base] at hs
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
        exact chosenEndpoint_confirmed m e r0 (B.occupied t ht)
      · dsimp [extra] at hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact hffull.2
        · rcases hs with rfl | hs
          · exact hgfull.2
          · cases hs
    have hcellnd : (slots.map m.cellOf).Nodup :=
      confirmed_cells_nodup m e r0 hslots hconf
    have hsub : ∀ c ∈ slots.map m.cellOf, c ∈ B.cells := by
      intro c hc
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      dsimp [slots] at hs
      simp only [List.mem_append] at hs
      rcases hs with hs | hs
      · dsimp [base] at hs
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
        rcases chosenEndpoint_sameEdge m e r0 k t with h | h
        · rw [h]
          exact (B.endpoints t ht).1
        · rw [h]
          exact (B.endpoints t ht).2
      · dsimp [extra] at hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact (B.endpoints f hfmem).2
        · rcases hs with rfl | hs
          · exact (B.endpoints g hgmem).2
          · cases hs
    have hle := nodup_subset_length_nat_tree hcellnd hsub
    have hlen : slots.length = B.edges.length + 2 := by
      dsimp [slots, base, extra]
      simp
    rw [List.length_map, hlen] at hle
    omega

/-- A tree-sized non-lobe support block has exactly one full physical edge. -/
theorem exists_unique_full_of_tree_size
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k : Nat} (B : SupportBlockAt m e r0 k)
    (hsize : B.edges.length + 1 = B.cells.length)
    (hnlobe : ∀ s, s ∈ B.edges → ¬ LobeSlot m s) :
    ∃ f, f ∈ B.edges ∧ Full m e r0 k f ∧
      ∀ g, g ∈ B.edges → Full m e r0 k g → g = f := by
  obtain ⟨f, hfmem, hffull⟩ :=
    exists_full_of_tree_size m e r0 hr0 B hsize
  refine ⟨f, hfmem, hffull, ?_⟩
  intro g hgmem hgfull
  exact full_unique_of_tree_size m e r0 B hsize hnlobe
    hgmem hfmem hgfull hffull

/-- In an equal-sized support block, any full edge must be a lobe.  Other
edges in the block are allowed to be lobes; the contradiction only uses that
the hypothetical full edge itself has distinct endpoint cells. -/
theorem no_full_nonlobe_of_equal_size
    {k : Nat} (B : SupportBlockAt m e r0 k)
    (hsize : B.edges.length = B.cells.length)
    {f : Nat} (hfmem : f ∈ B.edges)
    (hfnlobe : ¬ LobeSlot m f) :
    ¬ Full m e r0 k f := by
  intro hffull
  let base := B.edges.map (chosenEndpoint m e r0 k)
  let slots := base ++ [m.bar f]
  have hbase : base.Nodup := by
    dsimp [base]
    exact chosenEndpoints_nodup m e r0 B
  have hbar : m.bar f ∉ base := by
    dsimp [base]
    exact bar_full_not_mem_chosen m e r0 B hfmem hfnlobe hffull
  have hslots : slots.Nodup := by
    dsimp [slots]
    rw [List.nodup_append]
    refine ⟨hbase, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · apply hbar
      simpa [hab] using ha
    · cases hb
  have hconf : ∀ s ∈ slots, Confirmed m e r0 k s := by
    intro s hs
    dsimp [slots] at hs
    simp only [List.mem_append] at hs
    rcases hs with hs | hs
    · dsimp [base] at hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      exact chosenEndpoint_confirmed m e r0 (B.occupied t ht)
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact hffull.2
      · cases hs
  have hcellnd : (slots.map m.cellOf).Nodup :=
    confirmed_cells_nodup m e r0 hslots hconf
  have hsub : ∀ c ∈ slots.map m.cellOf, c ∈ B.cells := by
    intro c hc
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
    dsimp [slots] at hs
    simp only [List.mem_append] at hs
    rcases hs with hs | hs
    · dsimp [base] at hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      rcases chosenEndpoint_sameEdge m e r0 k t with h | h
      · rw [h]
        exact (B.endpoints t ht).1
      · rw [h]
        exact (B.endpoints t ht).2
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact (B.endpoints f hfmem).2
      · cases hs
  have hle := nodup_subset_length_nat_tree hcellnd hsub
  have hlen : slots.length = B.edges.length + 1 := by
    dsimp [slots, base]
    simp
  rw [List.length_map, hlen] at hle
  omega

/-- An equal-sized non-lobe support block (`edges = cells`) has no full edge. -/
theorem no_full_of_equal_size
    {k : Nat} (B : SupportBlockAt m e r0 k)
    (hsize : B.edges.length = B.cells.length)
    (hnlobe : ∀ s, s ∈ B.edges → ¬ LobeSlot m s) :
    ∀ f, f ∈ B.edges → ¬ Full m e r0 k f := by
  intro f hfmem
  exact no_full_nonlobe_of_equal_size m e r0 B hsize hfmem
    (hnlobe f hfmem)

end Echo
