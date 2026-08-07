import SupportBound

/-!
# What a support-preserving productive step does

The monotone-support theorem says jump edges can disappear but never return.
This file identifies the local dynamics when an edge does *not* disappear.

A confirmed endpoint is a cell's selected register slot.  A jump edge is
`Full` when both endpoints are confirmed.  If a productive write replaces an
old register by an arrival on a genuinely different jump edge, and the old
edge remains occupied afterwards, then the old edge was Full before the step
and the arrival edge is Full afterwards.  In other words, inside a fixed
support epoch a productive non-lobe move transfers the redundancy from one
edge to an adjacent edge.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Both endpoints of the jump edge represented by `s` are selected. -/
def Full (k s : Nat) : Prop :=
  Confirmed m e r0 k s ∧ Confirmed m e r0 k (m.bar s)

/-- Two slots represent the same jump edge. -/
def SameEdge (s t : Nat) : Prop := t = s ∨ t = m.bar s

/-- Same-edge is symmetric. -/
theorem sameEdge_symm {s t : Nat} :
    SameEdge m s t → SameEdge m t s := by
  rintro (rfl | h)
  · exact Or.inl rfl
  · right
    rw [h, m.bar_invol]

/-- A slot and its bar-partner always represent the same edge. -/
theorem sameEdge_bar (s : Nat) : SameEdge m s (m.bar s) := Or.inr rfl

/-- If two confirmed slots belong to one cell, they are equal. -/
theorem confirmed_same_cell_eq
    {k s t : Nat}
    (hs : Confirmed m e r0 k s) (ht : Confirmed m e r0 k t)
    (hc : m.cellOf s = m.cellOf t) : s = t := by
  unfold Confirmed at hs ht
  rw [hc] at hs
  exact hs.symm.trans ht

/-- The old register value is confirmed before it is overwritten. -/
theorem old_register_confirmed
    (hr0 : ∀ c, m.cellOf (r0 c) = c) (k c : Nat) :
    Confirmed m e r0 k (reg m e r0 k c) := by
  unfold Confirmed
  have hc := reg_cell m e r0 hr0 k c
  rw [hc]

/-- Let `new = e(k+1)` and let `old` be the destination cell's previous
register.  If the old jump edge remains occupied afterwards and old/new are
genuinely different jump edges, then the old edge was Full before the write. -/
theorem old_edge_full_of_preserved
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (_hp : ProductiveStep m e r0 k)
    (hpres : Occupied m e r0 (k+1)
      (reg m e r0 k (m.cellOf (e (k+1)))))
    (hdiff : ¬ SameEdge m
      (reg m e r0 k (m.cellOf (e (k+1)))) (e (k+1))) :
    Full m e r0 k (reg m e r0 k (m.cellOf (e (k+1)))) := by
  let old := reg m e r0 k (m.cellOf (e (k+1)))
  let new := e (k+1)
  have hold : Confirmed m e r0 k old := by
    exact old_register_confirmed m e r0 hr0 k (m.cellOf new)
  have hcold : m.cellOf old = m.cellOf new := by
    simpa [old] using reg_cell m e r0 hr0 k (m.cellOf new)
  have hnew : Confirmed m e r0 (k+1) new := by
    unfold Confirmed new
    exact reg_write m e r0 rfl
  rcases hpres with hstill | hbarstill
  · have heq : old = new :=
      confirmed_same_cell_eq m e r0 hstill hnew hcold
    exact absurd (Or.inl heq.symm) hdiff
  · refine ⟨hold, ?_⟩
    have hcb : m.cellOf new ≠ m.cellOf (m.bar old) := by
      intro hc
      have hnewbar : new = m.bar old :=
        confirmed_same_cell_eq m e r0 hnew hbarstill hc
      exact hdiff (Or.inr hnewbar)
    have hskip := reg_skip m e r0 (k := k) (c := m.cellOf (m.bar old)) hcb
    unfold Confirmed at hbarstill ⊢
    rw [hskip] at hbarstill
    exact hbarstill

/-- Under the same different-edge hypothesis, the arrival edge is Full after
its write: its opposite endpoint was the confirmed value read by the step and
cannot be overwritten by this different-edge arrival. -/
theorem new_edge_full_of_preserved
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (_hp : ProductiveStep m e r0 k)
    (hdiff : ¬ SameEdge m
      (reg m e r0 k (m.cellOf (e (k+1)))) (e (k+1))) :
    Full m e r0 (k+1) (e (k+1)) := by
  let new := e (k+1)
  let old := reg m e r0 k (m.cellOf new)
  have hnew : Confirmed m e r0 (k+1) new := by
    unfold Confirmed new
    exact reg_write m e r0 rfl
  have hbarold : Confirmed m e r0 k (m.bar new) :=
    head_confirmed m e r0 hrun hr0 k
  have hold : Confirmed m e r0 k old := by
    exact old_register_confirmed m e r0 hr0 k (m.cellOf new)
  have hcold : m.cellOf old = m.cellOf new := by
    simpa [old] using reg_cell m e r0 hr0 k (m.cellOf new)
  have hcellne : m.cellOf new ≠ m.cellOf (m.bar new) := by
    intro hc
    have heq : old = m.bar new :=
      confirmed_same_cell_eq m e r0 hold hbarold (hcold.trans hc)
    apply hdiff
    right
    have hb := congrArg m.bar heq
    rw [m.bar_invol] at hb
    exact hb.symm
  have hskip := reg_skip m e r0 (k := k) (c := m.cellOf (m.bar new)) hcellne
  refine ⟨hnew, ?_⟩
  unfold Confirmed at hbarold ⊢
  rw [hskip]
  exact hbarold

end Echo
