import BoundaryReplay

/-!
# Unicyclic lobe components are one-bit rooted forests

A support component whose unique cycle is a lobe consists of one lobe root
with ordinary tree edges feeding into it.  The lobe root register is binary.
Every other cell points, by last-write recency, toward that externally encoded
root.

This module packages the component directly from fixed-support data.  An
`edges = cells` block with one physical lobe edge has no full non-lobe edge;
therefore every non-root cell receives a boundary-root certificate.  Equality
of one Boolean root bit replays the complete component snapshot.
-/

namespace Echo

/-- Fixed finite support data for a unicyclic component whose only lobe edge
is `rootSlot`. -/
structure SupportLobeForestEpoch
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
  rootSlot : Nat
  root_mem : rootSlot ∈ edges
  root_lobe : LobeSlot m rootSlot
  only_lobe : ∀ s, s ∈ edges → LobeSlot m s →
    SameEdge m rootSlot s
  positive_visit : ∀ k, times k → ∀ c ∈ cells,
    ∃ j, 0 < j ∧ j ≤ k ∧ m.cellOf (e j) = c

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)
variable {times : Nat → Prop}

/-- Root cell of a lobe-forest block. -/
def SupportLobeForestEpoch.root
    (B : SupportLobeForestEpoch m e r0 times) : Nat :=
  m.cellOf B.rootSlot

/-- One-time support block. -/
def SupportLobeForestEpoch.at
    (B : SupportLobeForestEpoch m e r0 times)
    (k : Nat) (hk : times k) : SupportBlockAt m e r0 k where
  cells := B.cells
  edges := B.edges
  cells_nodup := B.cells_nodup
  edge_reps := B.edge_reps
  occupied := B.occupied k hk
  endpoints := B.endpoints
  selected_covered := B.selected_covered k hk

/-- The root belongs to the component. -/
theorem SupportLobeForestEpoch.root_cell_mem
    (B : SupportLobeForestEpoch m e r0 times) :
    B.root m ∈ B.cells := by
  exact (B.endpoints B.rootSlot B.root_mem).1

/-- The root lobe stays occupied throughout the epoch. -/
theorem SupportLobeForestEpoch.root_occupied
    (B : SupportLobeForestEpoch m e r0 times)
    {k : Nat} (hk : times k) :
    Occupied m e r0 k B.rootSlot :=
  B.occupied k hk B.rootSlot B.root_mem

/-- Following any selected edge remains inside the component. -/
theorem SupportLobeForestEpoch.selected_target_mem
    (B : SupportLobeForestEpoch m e r0 times)
    {k c : Nat} (hk : times k) (hc : c ∈ B.cells) :
    m.cellOf (m.bar (reg m e r0 k c)) ∈ B.cells := by
  obtain ⟨s, hs, hsame⟩ := B.selected_covered k hk c hc
  rcases hsame with h | h
  · rw [h]
    exact (B.endpoints s hs).2
  · rw [h, m.bar_invol]
    exact (B.endpoints s hs).1

/-- A selected lobe edge can occur only at the distinguished root cell. -/
theorem SupportLobeForestEpoch.selected_nonlobe_away_root
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (B : SupportLobeForestEpoch m e r0 times)
    {k c : Nat} (hk : times k) (hc : c ∈ B.cells)
    (hroot : c ≠ B.root m) :
    ¬ LobeSlot m (reg m e r0 k c) := by
  obtain ⟨s, hs, hsame⟩ := B.selected_covered k hk c hc
  intro hregLobe
  have hsLobe : LobeSlot m s :=
    (lobe_sameEdge_iff m hsame).mpr hregLobe
  have hrootSame : SameEdge m B.rootSlot (reg m e r0 k c) :=
    sameEdge_trans m (B.only_lobe s hs hsLobe) hsame
  rcases selected_sameEdge_root m e r0 hr0 hrootSame with h | h
  · exact hroot h
  · apply hroot
    unfold SupportLobeForestEpoch.root
    rw [← B.root_lobe]
    exact h

/-- Away from the encoded lobe root, no selected edge is full. -/
theorem SupportLobeForestEpoch.selected_nonfull_away_root
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (B : SupportLobeForestEpoch m e r0 times)
    {k c : Nat} (hk : times k) (hc : c ∈ B.cells)
    (hroot : c ≠ B.root m) :
    ¬ Full m e r0 k (reg m e r0 k c) := by
  obtain ⟨s, hs, hsame⟩ := B.selected_covered k hk c hc
  have hsNonlobe : ¬ LobeSlot m s := by
    intro hsLobe
    apply B.selected_nonlobe_away_root m e r0 hr0 hk hc hroot
    exact (lobe_sameEdge_iff m hsame).mp hsLobe
  have hsnf := no_full_nonlobe_of_equal_size m e r0
    (B.at m e r0 k hk) B.cycle_size hs hsNonlobe
  intro hfull
  exact hsnf ((full_sameEdge_iff m e r0 hsame).mpr hfull)

/-- Recency automatically roots the attached forest at the lobe cell. -/
theorem SupportLobeForestEpoch.boundary_rooted
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (B : SupportLobeForestEpoch m e r0 times)
    {k : Nat} (hk : times k) :
    BoundaryRootedCells m e r0 k [B.root m] B.cells := by
  let lw := positiveLastWriteMapOfVisits m e k B.cells
    (B.positive_visit k hk)
  apply boundaryRootedCells_of_rank m e r0 k [B.root m]
    B.cells (recencyRank m e k lw)
  exact rankedTowardBoundary_of_recency m e r0 hrun hr0 k
    [B.root m] B.cells lw
    (fun c hc => B.selected_target_mem m e r0 hk hc)
    (fun c hc hnot => by
      have hnl := B.selected_nonlobe_away_root m e r0 hr0 hk hc (by
        intro hroot
        apply hnot
        simp [hroot])
      unfold LobeSlot at hnl
      intro htarget
      exact hnl (htarget.trans (reg_cell m e r0 hr0 k c).symm))
    (fun c hc hnot =>
      B.selected_nonfull_away_root m e r0 hr0 hk hc (by
        intro hroot
        apply hnot
        simp [hroot]))

/-- One Boolean records the lobe root register. -/
def SupportLobeForestEpoch.bit
    (B : SupportLobeForestEpoch m e r0 times) (k : Nat) : Bool :=
  decide (reg m e r0 k (B.root m) = m.bar B.rootSlot)

/-- Equal root bits give equal root registers. -/
theorem SupportLobeForestEpoch.bit_eq_root_reg_eq
    (B : SupportLobeForestEpoch m e r0 times)
    {i j : Nat} (hi : times i) (hj : times j)
    (hbit : B.bit m e r0 i = B.bit m e r0 j) :
    reg m e r0 i (B.root m) = reg m e r0 j (B.root m) := by
  exact lobeBit_eq_reg_eq m e r0 (fun _ => B.rootSlot)
    (by rfl) B.root_lobe
    (B.root_occupied m e r0 hi)
    (B.root_occupied m e r0 hj)
    hbit

/-- Equal root registers and support replay the whole lobe-forest block. -/
theorem SupportLobeForestEpoch.root_reg_eq_snap_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (B : SupportLobeForestEpoch m e r0 times)
    {i j : Nat} (hi : times i)
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hroot : reg m e r0 j (B.root m) =
      reg m e r0 i (B.root m)) :
    snap m e r0 B.cells j = snap m e r0 B.cells i := by
  exact boundaryRootedCells_snap_replay m e r0 hr0
    [B.root m] B.cells hsupport
    (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact hroot)
    (B.boundary_rooted m e r0 hrun hr0 hi)

/-- Equality of the root bit and support replays the whole lobe-forest block. -/
theorem SupportLobeForestEpoch.bit_eq_snap_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (B : SupportLobeForestEpoch m e r0 times)
    {i j : Nat} (hi : times i) (hj : times j)
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hbit : B.bit m e r0 i = B.bit m e r0 j) :
    snap m e r0 B.cells i = snap m e r0 B.cells j := by
  have hroot : reg m e r0 j (B.root m) =
      reg m e r0 i (B.root m) :=
    (B.bit_eq_root_reg_eq m e r0 hi hj hbit).symm
  have h := boundaryRootedCells_snap_replay m e r0 hr0
    [B.root m] B.cells hsupport
    (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact hroot)
    (B.boundary_rooted m e r0 hrun hr0 hi)
  exact h.symm

/-- Cells covered by a list of lobe-forest blocks. -/
def lobeForestCells
    (blocks : List (SupportLobeForestEpoch m e r0 times)) : List Nat :=
  blocks.flatMap (fun B => B.cells)

/-- Root-cell list. -/
def lobeForestRoots
    (blocks : List (SupportLobeForestEpoch m e r0 times)) : List Nat :=
  blocks.map (fun B => B.root m)

/-- One Boolean per lobe-forest block. -/
def lobeForestBits
    (blocks : List (SupportLobeForestEpoch m e r0 times))
    (k : Nat) : List Bool :=
  blocks.map (fun B => B.bit m e r0 k)

theorem lobeForestBits_length
    (blocks : List (SupportLobeForestEpoch m e r0 times)) (k : Nat) :
    (lobeForestBits m e r0 blocks k).length = blocks.length := by
  simp [lobeForestBits]

/-- Equal block-bit vectors replay every lobe-forest block. -/
theorem lobeForestBits_eq_snap_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) :
    ∀ (blocks : List (SupportLobeForestEpoch m e r0 times))
      {i j : Nat},
      times i → times j →
      (∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s) →
      lobeForestBits m e r0 blocks i =
        lobeForestBits m e r0 blocks j →
      snap m e r0 (lobeForestCells m e r0 blocks) i =
        snap m e r0 (lobeForestCells m e r0 blocks) j := by
  intro blocks
  induction blocks with
  | nil => intro i j hi hj hs hb; rfl
  | cons B rest ih =>
      intro i j hi hj hsupport hbits
      change B.bit m e r0 i :: lobeForestBits m e r0 rest i =
        B.bit m e r0 j :: lobeForestBits m e r0 rest j at hbits
      have hp := List.cons.inj hbits
      have hhead := B.bit_eq_snap_eq m e r0 hrun hr0 hi hj
        hsupport hp.1
      have htail := ih hi hj hsupport hp.2
      unfold lobeForestCells at htail ⊢
      simp only [List.flatMap_cons]
      unfold snap at hhead htail ⊢
      simp only [List.map_append]
      rw [hhead, htail]

/-- If every block root register is fixed between two states, all lobe-forest
component snapshots agree. -/
theorem lobeForestRoots_fixed_snap_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) :
    ∀ (blocks : List (SupportLobeForestEpoch m e r0 times))
      {i j : Nat},
      times i →
      (∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s) →
      (∀ B ∈ blocks, reg m e r0 j (B.root m) =
        reg m e r0 i (B.root m)) →
      snap m e r0 (lobeForestCells m e r0 blocks) j =
        snap m e r0 (lobeForestCells m e r0 blocks) i := by
  intro blocks
  induction blocks with
  | nil => intro i j hi hs hr; rfl
  | cons B rest ih =>
      intro i j hi hsupport hroots
      have hhead := B.root_reg_eq_snap_eq m e r0 hrun hr0 hi
        hsupport (hroots B List.mem_cons_self)
      have htail := ih hi hsupport
        (fun D hD => hroots D (List.mem_cons_of_mem _ hD))
      unfold lobeForestCells at htail ⊢
      simp only [List.flatMap_cons]
      unfold snap at hhead htail ⊢
      simp only [List.map_append]
      rw [hhead, htail]

end Echo
