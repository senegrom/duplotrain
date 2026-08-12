import StationaryTail
import TreeReplay
import RestorationFrames
import OneReserveFromNoTail
import PairedRouterRoundtrip

/-!
# Reduction of the visible recurrent branch

This file separates the already formal consequences of exact recurrence from
the still-open seriality/crossing claim.

* A nonstationary `nextCell` step on an exact recurrent tail is productive and
  transfers a full edge to a different full edge.
* If the `nextCell` projection is stationary, `StationaryTail` already gives
  the four-snapshot bound.
* If a later visible chip move returns the original full edge, `TreeReplay`
  restores every rooted component snapshot.
* `VisibleRecurrentChipClosure` is the first missing implication.  It is a
  proposition, not a hidden assumption and not a theorem claimed below.  Supplying a
  proof of it closes the remaining visible branch and therefore gives the
  four-snapshot recurrent-tail theorem.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Exact entry and register recurrence from time `K`, with positive period
`q`. -/
def ExactRecurrentTail (K q : Nat) : Prop :=
  0 < q ∧
  (∀ t, K ≤ t → e (t+q) = e t) ∧
  ∀ t c, K ≤ t → reg m e r0 (t+q) c = reg m e r0 t c

/-- The complete cell-level pointer projection is stationary from `K`. -/
def ProjectionStationary (K : Nat) : Prop :=
  ∀ t, K ≤ t → ∀ c,
    nextCell m e r0 (t+1) c = nextCell m e r0 t c

/-- The complete cell-level pointer projection changes at step `k`. -/
def ProjectionChanges (k : Nat) : Prop :=
  ∃ c, nextCell m e r0 (k+1) c ≠ nextCell m e r0 k c

/-- At most four complete register snapshots occur at or after `K`. -/
def FourSnapshotTail (K : Nat) : Prop :=
  ∀ (cells ks : List Nat),
    (∀ j ∈ ks, K ≤ j) →
    (ks.map (snap m e r0 cells)).Nodup →
    ks.length ≤ 4

/-- A visible productive step on a fixed-support recurrent tail transfers the
unique redundant confirmation from one physical edge to a genuinely
different physical edge.  Both the old edge before the step and the new edge
after the step are full. -/
structure VisibleFullEdgeChipMove (k : Nat) : Prop where
  visible : ProjectionChanges m e r0 k
  productive : ProductiveStep m e r0 k
  supportFixed : SupportFixedStep m e r0 k
  differentEdge : ¬ SameEdge m (oldSlot m e r0 k) (e (k+1))
  oldFull : Full m e r0 k (oldSlot m e r0 k)
  newFull : Full m e r0 (k+1) (e (k+1))

/-- A changed `nextCell` projection cannot come from an unproductive write. -/
theorem projection_change_productive {k : Nat}
    (hchange : ProjectionChanges m e r0 k) :
    ProductiveStep m e r0 k := by
  obtain ⟨c, hc⟩ := hchange
  apply Classical.byContradiction
  intro hnot
  have heq : e (k+1) = reg m e r0 k (m.cellOf (e (k+1))) := by
    exact Classical.not_not.mp hnot
  have hstall := unproductive_stall m e r0 k heq
  apply hc
  unfold nextCell
  rw [hstall (m.star c)]

/-- A visible productive step cannot merely exchange the two endpoints of one
physical edge; such a lobe move is invisible in the cell projection. -/
theorem projection_change_different_edge
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c) {k : Nat}
    (hchange : ProjectionChanges m e r0 k)
    (hprod : ProductiveStep m e r0 k) :
    ¬ SameEdge m (oldSlot m e r0 k) (e (k+1)) := by
  have hnotParallel :
      ¬ ParallelEdge m (oldSlot m e r0 k) (e (k+1)) := by
    intro hparallel
    obtain ⟨c, hc⟩ := hchange
    have hstall :=
      (cell_projection_stall_iff_parallel m e r0 hrun hr0 k).mpr hparallel
    exact hc (hstall c)
  intro hsame
  apply hnotParallel
  rcases hsame with heq | hbar
  · exfalso
    apply hprod
    simpa [oldSlot] using heq
  · have hnear := old_new_cell m e r0 hr0 k
    have hnearBar :
        m.cellOf (oldSlot m e r0 k) =
          m.cellOf (m.bar (oldSlot m e r0 k)) := by
      simpa [hbar] using hnear
    constructor
    · exact hnear
    · rw [hbar, m.bar_invol]
      exact hnearBar.symm

/-- **Visible recurrent step = full-edge-chip move.**

Exact register recurrence fixes occupied support throughout the tail.  Hence a
nonstationary cell-level step is productive, uses a different physical edge,
and transfers fullness from its evicted edge to its arrival edge. -/
theorem recurrent_projection_change_is_chip_move
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q k : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (hk : K ≤ k)
    (hchange : ProjectionChanges m e r0 k) :
    VisibleFullEdgeChipMove m e r0 k := by
  have hfixed : SupportFixedStep m e r0 k :=
    support_fixed_of_register_period m e r0 hrun hr0 hrec.1 hrec.2.2 k hk
  have hprod : ProductiveStep m e r0 k :=
    projection_change_productive m e r0 hchange
  have hdiff : ¬ SameEdge m (oldSlot m e r0 k) (e (k+1)) :=
    projection_change_different_edge m e r0 hrun hr0 hchange hprod
  have hbefore : Occupied m e r0 k (oldSlot m e r0 k) :=
    old_edge_occupied_before m e r0 hr0 k
  have hpres : Occupied m e r0 (k+1) (oldSlot m e r0 k) :=
    (hfixed (oldSlot m e r0 k)).mpr hbefore
  have hold : Full m e r0 k (oldSlot m e r0 k) := by
    simpa [oldSlot] using
      old_edge_full_of_preserved m e r0 hrun hr0 k hprod
        (by simpa [oldSlot] using hpres)
        (by simpa [oldSlot] using hdiff)
  have hnew : Full m e r0 (k+1) (e (k+1)) := by
    exact new_edge_full_of_preserved m e r0 hrun hr0 k hprod
      (by simpa [oldSlot] using hdiff)
  exact ⟨hchange, hprod, hfixed, hdiff, hold, hnew⟩

/-- Exact recurrence has only two cell-projection cases: the projection is
stationary, or some tail step is a visible full-edge-chip move. -/
theorem recurrent_stationary_or_visible_chip
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q : Nat}
    (hrec : ExactRecurrentTail m e r0 K q) :
    ProjectionStationary m e r0 K ∨
      ∃ k, K ≤ k ∧ VisibleFullEdgeChipMove m e r0 k := by
  by_cases hchange : ∃ k, K ≤ k ∧ ProjectionChanges m e r0 k
  · right
    obtain ⟨k, hk, hvis⟩ := hchange
    exact ⟨k, hk,
      recurrent_projection_change_is_chip_move
        m e r0 hrun hr0 hrec hk hvis⟩
  · left
    intro k hk c
    apply Classical.byContradiction
    intro hne
    exact hchange ⟨k, hk, c, hne⟩

/-- The stationary side of the recurrent dichotomy is already closed by
`StationaryTail`. -/
theorem stationary_recurrent_four
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (hstationary : ProjectionStationary m e r0 K) :
    FourSnapshotTail m e r0 K := by
  intro cells ks hks hnd
  exact stationary_recurrent_tail_four_complete
    m e r0 hrun hr0 hrec.1 hrec.2.1 hrec.2.2
      hstationary cells ks hks hnd

theorem recurrent_occupied_iff
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q i j s : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (hi : K ≤ i) (hj : K ≤ j) :
    Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  by_cases hij : i ≤ j
  · have hfixed : PairedSupportFixed m e r0 i j := by
      intro t hit htj slot
      exact (support_fixed_of_register_period m e r0 hrun hr0
        hrec.1 hrec.2.2 t (Nat.le_trans hi hit) slot).symm
    exact pairedSupportFixed_between_of_le m e r0 hfixed
      (Nat.le_refl _) hij (Nat.le_refl _) s
  · have hji : j ≤ i := by omega
    have hfixed : PairedSupportFixed m e r0 j i := by
      intro t hjt hti slot
      exact (support_fixed_of_register_period m e r0 hrun hr0
        hrec.1 hrec.2.2 t (Nat.le_trans hj hjt) slot).symm
    exact (pairedSupportFixed_between_of_le m e r0 hfixed
      (Nat.le_refl _) hji (Nat.le_refl _) s).symm

/-- The only ways in which the four cells of two adjacent external
reflectors fail to be pairwise distinct are the two genuine two-cell
collapses: the support edge is internal to one cell, or it directly joins a
cell to its mouth partner. -/
def CollapsedReflectorGeometry (x : Nat) : Prop :=
  m.cellOf (m.bar x) = m.cellOf x ∨
  m.cellOf (m.bar x) = m.star (m.cellOf x)

/-- Pure cell geometry for the reflector classification. -/
theorem reflector_cells_distinct_or_collapsed (x : Nat) :
    ReflectorCellsDistinct
        (m.star (m.cellOf x)) (m.cellOf x)
        (m.cellOf (m.bar x)) (m.star (m.cellOf (m.bar x))) ∨
      CollapsedReflectorGeometry m x := by
  let X := m.cellOf x
  let Y := m.cellOf (m.bar x)
  by_cases hYX : Y = X
  · exact Or.inr (Or.inl hYX)
  · by_cases hYstarX : Y = m.star X
    · exact Or.inr (Or.inr hYstarX)
    · apply Or.inl
      dsimp [ReflectorCellsDistinct, X, Y] at *
      refine ⟨m.star_ne _, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun h => hYstarX h.symm
      · intro h
        apply hYX
        have h' := congrArg m.star h
        simpa only [m.star_invol] using h'.symm
      · exact fun h => hYX h.symm
      · intro h
        apply hYstarX
        have h' := congrArg m.star h
        simpa only [m.star_invol] using h'.symm
      · exact fun h => m.star_ne _ h.symm

/-- **Fully lobed recurrent component: separated reflector tail or exact
two-cell collapse.**

At a component visit, choose the two occupied external lobes used by the
four-step roundtrip.  Exact register recurrence makes both choices occupied
for the whole recurrent tail.  The cell-geometry lemma then leaves precisely
the separated `CompatibleTwoReflectorTail` or one of the two explicit
collapsed geometries; there is no unnamed crossing or seriality premise. -/
theorem compatible_external_reflector_trap_or_collapsed
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q lo : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (hKlo : K ≤ lo)
    (cells : List Nat)
    (hcompat : SelectedClosedFrom m e r0 cells lo ∧
      FullyExternallyLobedFrom m e r0 cells lo ∧
      ComponentVisitedFrom m e cells lo) :
    ∃ k x a b,
      lo ≤ k ∧ e k = x ∧
        (CompatibleTwoReflectorTail m e r0 k x a b ∨
          CollapsedReflectorGeometry m x) := by
  rcases hcompat.2.2 with ⟨k, hk, hentry⟩
  have hfirst := hcompat.2.1 k hk (m.cellOf (e k)) hentry
  rcases hfirst with ⟨a, haCell, haLobe, haOcc⟩
  have hround := fully_lobed_component_roundtrip
    m e r0 hrun hr0 cells hcompat.1 hcompat.2.1 hk hentry
  have hwrite : reg m e r0 k (m.cellOf (e k)) = e k :=
    reg_write m e r0 rfl
  have hnextEntry : m.cellOf (e (k+2)) ∈ cells := by
    rw [hround.1]
    have hclosed := hcompat.1 k hk (m.cellOf (e k)) hentry
    rwa [hwrite] at hclosed
  have hsecond := hcompat.2.1 (k+2) (by omega)
    (m.cellOf (e (k+2))) hnextEntry
  rcases hsecond with ⟨b, hbCell, hbLobe, hbOcc⟩
  have hbCell' :
      m.cellOf b = m.star (m.cellOf (m.bar (e k))) := by
    rw [← hround.1]
    exact hbCell
  have haPartner :
      m.cellOf (e k) = m.star (m.cellOf a) := by
    rw [haCell, m.star_invol]
  have hbPartner :
      m.cellOf (m.bar (e k)) = m.star (m.cellOf b) := by
    rw [hbCell', m.star_invol]
  have haForever : ∀ t, k ≤ t → Occupied m e r0 t a := by
    intro t hkt
    exact (recurrent_occupied_iff m e r0 hrun hr0 hrec
      (Nat.le_trans hKlo hk)
      (Nat.le_trans hKlo (Nat.le_trans hk hkt))).mp haOcc
  have hbForever : ∀ t, k ≤ t → Occupied m e r0 t b := by
    intro t hkt
    exact (recurrent_occupied_iff m e r0 hrun hr0 hrec
      (Nat.le_trans hKlo (by omega : lo ≤ k+2))
      (Nat.le_trans hKlo (Nat.le_trans hk hkt))).mp hbOcc
  refine ⟨k, e k, a, b, hk, rfl, ?_⟩
  rcases reflector_cells_distinct_or_collapsed m (e k) with
      hdistinct | hcollapsed
  · apply Or.inl
    refine ⟨rfl, haLobe, haPartner, hbLobe, hbPartner,
      haForever, hbForever, ?_⟩
    rw [haCell, hbCell']
    exact hdistinct
  · exact Or.inr hcollapsed

/-- A closed, visited component whose every cell has an occupied external
lobe partner.  These are exactly the component hypotheses under which
`FullyLobedComponentTrap` produces a four-return entry orbit. -/
def CompatibleExternalReflectorComponent
    (cells : List Nat) (lo : Nat) : Prop :=
  SelectedClosedFrom m e r0 cells lo ∧
  FullyExternallyLobedFrom m e r0 cells lo ∧
  ComponentVisitedFrom m e cells lo

theorem closed_component_reflector_or_collapsed_or_reserve
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q lo : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (hKlo : K ≤ lo)
    (cells roots : List Nat)
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hvisit : ComponentVisitedFrom m e cells lo)
    (hactive : PersistentActiveLobeRoots m e r0 roots lo) :
    (∃ k x a b, lo ≤ k ∧ e k = x ∧
      CompatibleTwoReflectorTail m e r0 k x a b) ∨
    (∃ k x, lo ≤ k ∧ e k = x ∧
      CollapsedReflectorGeometry m x) ∨
    ∃ c, c ∈ cells ∧ m.star c ∉ roots := by
  classical
  by_cases hlubed : FullyExternallyLobedFrom m e r0 cells lo
  · rcases compatible_external_reflector_trap_or_collapsed
      m e r0 hrun hr0 hrec hKlo cells
        ⟨hclosed, hlubed, hvisit⟩ with
      ⟨k, x, a, b, hk, hx, htrap | hcollapsed⟩
    · exact Or.inl ⟨k, x, a, b, hk, hx, htrap⟩
    · exact Or.inr (Or.inl ⟨k, x, hk, hx, hcollapsed⟩)
  · apply Or.inr
    apply Or.inr
    have hunreflected : ∃ c, c ∈ cells ∧
        ∃ j, lo ≤ j ∧
          ¬ OccupiedLobeAt m e r0 j (m.star c) := by
      apply Classical.byContradiction
      intro hnone
      apply hlubed
      intro j hj c hc
      apply Classical.byContradiction
      intro hnot
      apply hnone
      exact ⟨c, hc, j, hj, hnot⟩
    rcases hunreflected with ⟨c, hc, j, hj, hunreflected⟩
    exact ⟨c, hc,
      unreflected_not_active_partner m e r0 roots lo c j
        hactive hj hunreflected⟩

/-- A cell is the root of a lobe edge which stays occupied for the whole
tail beginning at `lo`. -/
def PersistentLobeRootAt (c lo : Nat) : Prop :=
  ∃ a,
    m.cellOf a = c ∧
    m.cellOf (m.bar a) = m.cellOf a ∧
    ∀ j, lo ≤ j → Occupied m e r0 j a

/-- The finite root list is exact relative to one finite component: it lists
precisely the mouth partners of component cells which carry persistent
occupied lobes.  Restricting completeness to the component is essential in
the `Nat`-indexed abstract machine, where irrelevant cells need not form a
finite global support. -/
def CompletePersistentLobeRoots
    (cells roots : List Nat) (lo : Nat) : Prop :=
  ∀ r, r ∈ roots ↔
    PersistentLobeRootAt m e r0 r lo ∧
      ∃ c, c ∈ cells ∧ r = m.star c

/-- The complete-root version of the component trichotomy gives a genuine
unlobed reserve, rather than a cell merely absent from an arbitrary list. -/
theorem closed_component_reflector_or_collapsed_or_unlobed_reserve
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q lo : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (hKlo : K ≤ lo)
    (cells roots : List Nat)
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hvisit : ComponentVisitedFrom m e cells lo)
    (hroots : CompletePersistentLobeRoots m e r0 cells roots lo) :
    (∃ k x a b, lo ≤ k ∧ e k = x ∧
      CompatibleTwoReflectorTail m e r0 k x a b) ∨
    (∃ k x, lo ≤ k ∧ e k = x ∧
      CollapsedReflectorGeometry m x) ∨
    ∃ c, c ∈ cells ∧
      ¬ PersistentLobeRootAt m e r0 (m.star c) lo := by
  have hactive : PersistentActiveLobeRoots m e r0 roots lo := by
    intro c hc
    exact ((hroots c).mp hc).1
  rcases closed_component_reflector_or_collapsed_or_reserve
      m e r0 hrun hr0 hrec hKlo cells roots hclosed hvisit hactive with
    htrap | hcollapsed | ⟨c, hc, hreserve⟩
  · exact Or.inl htrap
  · exact Or.inr (Or.inl hcollapsed)
  · apply Or.inr
    apply Or.inr
    refine ⟨c, hc, ?_⟩
    intro hpersistent
    exact hreserve ((hroots (m.star c)).mpr
      ⟨hpersistent, c, hc, rfl⟩)

/-- A finite component certificate tied to one actual visible full-edge-chip
move.  Both physical endpoint cells belong to the component, selected edges
stay inside it, and `roots` lists *all* persistent occupied lobe roots. -/
structure VisibleChipComponentFrame
    (K lo k : Nat) (cells roots : List Nat) : Prop where
  tailStart : K ≤ lo
  moveTime : lo ≤ k
  move : VisibleFullEdgeChipMove m e r0 k
  oldCell : m.cellOf (oldSlot m e r0 k) ∈ cells
  newCell : m.cellOf (e (k+1)) ∈ cells
  selectedClosed : SelectedClosedFrom m e r0 cells lo
  rootsComplete : CompletePersistentLobeRoots m e r0 cells roots lo

/-- **The exact component-extraction gap.**

Every nonstationary exact recurrent tail is expected to furnish a finite
complete-root component frame anchored at one of its visible chip moves.  No crossing,
seriality, reflector, or snapshot conclusion is included in this proposition.
-/
def VisibleChipComponentExtraction : Prop :=
  ∀ (m : Machine) (e r0 : Nat → Nat) (K q : Nat),
    IsRun m e r0 →
    (∀ c, m.cellOf (r0 c) = c) →
    ExactRecurrentTail m e r0 K q →
    (∃ k, K ≤ k ∧ VisibleFullEdgeChipMove m e r0 k) →
    ∃ lo k cells roots,
      VisibleChipComponentFrame m e r0 K lo k cells roots

def CompatiblePairedRouterAt (k : Nat) : Prop :=
  ∃ s,
    e k = s ∧
    LobeEntryAt m e (k+2) ∧
    LobeEntryAt m e (k+5) ∧
    ∀ i, k < i → i ≤ k+3 →
      m.cellOf (e i) ≠ m.cellOf s

def VisibleRecurrentChipClosure : Prop :=
  ∀ (m : Machine) (e r0 : Nat → Nat) (K q : Nat),
    IsRun m e r0 →
    (∀ c, m.cellOf (r0 c) = c) →
    ExactRecurrentTail m e r0 K q →
    (∃ k, K ≤ k ∧ VisibleFullEdgeChipMove m e r0 k) →
    FourSnapshotTail m e r0 K

end Echo
