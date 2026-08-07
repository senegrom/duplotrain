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
support epoch a productive non-lobe move transfers the unique redundancy from
one edge to an adjacent edge.
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
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k s t : Nat}
    (hs : Confirmed m e r0 k s) (ht : Confirmed m e r0 k t)
    (hc : m.cellOf s = m.cellOf t) : s = t := by
  unfold Confirmed at hs ht
  have hcs := reg_cell m e r0 hr0 k (m.cellOf s)
  rw [hs] at hcs
  have hct := reg_cell m e r0 hr0 k (m.cellOf t)
  rw [ht] at hct
  rw [hc] at hs
  exact hs.symm.trans ht

/-- Let `new = e(k+1)` and let `old` be the destination cell's previous
register.  If the step is productive, the old jump edge is still occupied
afterwards, and old/new are genuinely different jump edges, then the old edge
was Full before the write. -/
theorem old_edge_full_of_preserved
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (hp : ProductiveStep m e r0 k)
    (hpres : Occupied m e r0 (k+1)
      (reg m e r0 k (m.cellOf (e (k+1)))))
    (hdiff : ¬ SameEdge m
      (reg m e r0 k (m.cellOf (e (k+1)))) (e (k+1))) :
    Full m e r0 k (reg m e r0 k (m.cellOf (e (k+1)))) := by
  let old := reg m e r0 k (m.cellOf (e (k+1)))
  let new := e (k+1)
  have hold : Confirmed m e r0 k old := by
    unfold Confirmed old
    have hc := reg_cell m e r0 hr0 k (m.cellOf new)
    exact hc.symm
  have hnew : Confirmed m e r0 (k+1) new := by
    unfold Confirmed new
    exact reg_write m e r0 rfl
  rcases hpres with hstill | hbarstill
  · have heq : old = new := by
      apply confirmed_same_cell_eq m e r0 hr0 hstill hnew
      have hcold := reg_cell m e r0 hr0 k (m.cellOf new)
      simpa [old, new] using hcold
    exact absurd (Or.inl heq.symm) hdiff
  · exact ⟨hold, by
      have hcb : m.cellOf (m.bar old) ≠ m.cellOf new := by
        intro hc
        have hnewbar : m.bar old = new :=
          confirmed_same_cell_eq m e r0 hr0 hbarstill hnew hc
        exact hdiff (Or.inr hnewbar.symm)
      have hskip := reg_skip m e r0 (k := k) (c := m.cellOf (m.bar old))
        (by simpa [new] using hcb.symm)
      unfold Confirmed at hbarstill ⊢
      rw [hskip] at hbarstill
      exact hbarstill⟩

/-- Under the same hypotheses, the arrival edge is Full after the write. -/
theorem new_edge_full_of_preserved
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (hp : ProductiveStep m e r0 k)
    (hdiff : ¬ SameEdge m
      (reg m e r0 k (m.cellOf (e (k+1)))) (e (k+1))) :
    Full m e r0 (k+1) (e (k+1)) := by
  let new := e (k+1)
  have hnew : Confirmed m e r0 (k+1) new := by
    unfold Confirmed new
    exact reg_write m e r0 rfl
  have hbarold : Confirmed m e r0 k (m.bar new) :=
    head_confirmed m e r0 hrun hr0 k
  have hcellne : m.cellOf new ≠ m.cellOf (m.bar new) := by
    intro hc
    have hold : Confirmed m e r0 k
        (reg m e r0 k (m.cellOf new)) := by
      unfold Confirmed
      have hrc := reg_cell m e r0 hr0 k (m.cellOf new)
      exact hrc.symm
    have heq : reg m e r0 k (m.cellOf new) = m.bar new := by
      apply confirmed_same_cell_eq m e r0 hr0 hold hbarold
      have hrc := reg_cell m e r0 hr0 k (m.cellOf new)
      rw [hc]
      exact hrc
    apply hdiff
    right
    exact heq
  have hskip := reg_skip m e r0 (k := k) (c := m.cellOf (m.bar new)) hcellne
  refine ⟨hnew, ?_⟩
  unfold Confirmed at hbarold ⊢
  rw [hskip]
  exact hbarold

end Echo
