import StationaryTail
import TreeReplay

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

/-- **Returned full edge replays its rooted component.**

The first visible move certifies that its evicted edge is full.  If a later
visible move installs the same physical edge and support agrees at the two
states, `TreeReplay` restores every register in the rooted component. -/
theorem returned_visible_chip_replays_component
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {i j : Nat}
    (hi : VisibleFullEdgeChipMove m e r0 i)
    (hj : VisibleFullEdgeChipMove m e r0 j)
    (hsupport : ∀ s,
      Occupied m e r0 i s ↔ Occupied m e r0 (j+1) s)
    (hreturn : SameEdge m (oldSlot m e r0 i) (e (j+1)))
    (hroot : RootedCells m e r0 i (oldSlot m e r0 i) cells) :
    snap m e r0 cells (j+1) = snap m e r0 cells i := by
  exact rootedCells_sameEdge_replay m e r0 hr0 cells hsupport
    hi.oldFull hj.newFull hreturn hroot

/-- **The first missing implication.**

On an exact recurrent tail, if the cell projection really moves, the visible
full-edge chip must be serial: its recurrent motion has at most four complete
register snapshots.  Proving this proposition requires the unresolved
foreign/foreign crossing argument.  This file deliberately does not assume it
silently and does not claim to prove it. -/
def VisibleRecurrentChipClosure : Prop :=
  ∀ (m : Machine) (e r0 : Nat → Nat) (K q : Nat),
    IsRun m e r0 →
    (∀ c, m.cellOf (r0 c) = c) →
    ExactRecurrentTail m e r0 K q →
    (∃ k, K ≤ k ∧ VisibleFullEdgeChipMove m e r0 k) →
    FourSnapshotTail m e r0 K

/-- Closing precisely `VisibleRecurrentChipClosure` closes the complete
four-snapshot recurrent-tail theorem.  The stationary branch is discharged by
`StationaryTail`; the visible branch is passed explicitly to `hclosure`. -/
theorem recurrent_tail_four_of_visible_chip_closure
    (hclosure : VisibleRecurrentChipClosure)
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q : Nat}
    (hrec : ExactRecurrentTail m e r0 K q) :
    FourSnapshotTail m e r0 K := by
  rcases recurrent_stationary_or_visible_chip
      m e r0 hrun hr0 hrec with hstationary | hvisible
  · exact stationary_recurrent_four m e r0 hrun hr0 hrec hstationary
  · exact hclosure m e r0 K q hrun hr0 hrec hvisible

end Echo
