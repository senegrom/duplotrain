import HiddenFibre

/-!
# Hidden moves inside a fixed support

A productive cell-projection stall changes between parallel jump edges.  If
those are genuinely different edges, the old edge becomes empty immediately:
its near endpoint was overwritten, while the far endpoint cell already selects
the new parallel edge.  Therefore a productive hidden move which preserves its
old support edge can only flip between the two endpoints of one loop edge — a
lobe.

Two consecutive support-preserving hidden moves are then lobes in mouth-partner
cells.  The already proved `absorb_entries` theorem applies, trapping every
later entry in their four-slot Gray square.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A productive parallel move whose old edge remains occupied must use the
same jump edge. -/
theorem parallel_preserved_sameEdge
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) (hp : ProductiveStep m e r0 k)
    (hpar : ParallelEdge m (oldSlot m e r0 k) (e (k+1)))
    (hpres : Occupied m e r0 (k+1) (oldSlot m e r0 k)) :
    SameEdge m (oldSlot m e r0 k) (e (k+1)) := by
  by_cases hs : SameEdge m (oldSlot m e r0 k) (e (k+1))
  · exact hs
  · have hf := old_edge_full_of_preserved m e r0 hrun hr0 k hp hpres hs
    have hn := head_confirmed m e r0 hrun hr0 k
    have hbar : m.bar (oldSlot m e r0 k) = m.bar (e (k+1)) :=
      confirmed_same_cell_eq m e r0 hf.2 hn hpar.2
    have heq : oldSlot m e r0 k = e (k+1) := by
      have h := congrArg m.bar hbar
      rwa [m.bar_invol, m.bar_invol] at h
    exact absurd (Or.inl heq.symm) hs

/-- If a productive move uses one jump edge, it must cross from one endpoint
to the other. -/
theorem productive_sameEdge_bar {k : Nat}
    (hp : ProductiveStep m e r0 k)
    (hs : SameEdge m (oldSlot m e r0 k) (e (k+1))) :
    e (k+1) = m.bar (oldSlot m e r0 k) := by
  rcases hs with heq | hbar
  · exact absurd heq.symm (productive_parallel_ne m e r0 hp)
  · exact hbar

/-- Structure of a support-preserving hidden productive move: it flips a lobe
in the mouth partner of the preceding cell. -/
theorem hidden_preserved_lobe
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) (hp : ProductiveStep m e r0 k)
    (hstall : ∀ c, nextCell m e r0 (k+1) c = nextCell m e r0 k c)
    (hpres : Occupied m e r0 (k+1) (oldSlot m e r0 k)) :
    e (k+1) = m.bar (oldSlot m e r0 k) ∧
    m.cellOf (m.bar (e (k+1))) = m.cellOf (e (k+1)) ∧
    m.cellOf (e (k+1)) = m.star (m.cellOf (e k)) := by
  have hpar := (cell_projection_stall_iff_parallel m e r0 hrun hr0 k).mp hstall
  have hs := parallel_preserved_sameEdge m e r0 hrun hr0 k hp hpar hpres
  have hnew := productive_sameEdge_bar m e r0 hp hs
  have hback : m.bar (e (k+1)) = oldSlot m e r0 k := by
    rw [hnew, m.bar_invol]
  have hlobe : m.cellOf (m.bar (e (k+1))) = m.cellOf (e (k+1)) := by
    rw [hback]
    exact old_new_cell m e r0 hr0 k
  have hpartner : m.cellOf (e (k+1)) = m.star (m.cellOf (e k)) := by
    calc
      m.cellOf (e (k+1)) = m.cellOf (m.bar (e (k+1))) := hlobe.symm
      _ = m.star (m.cellOf (e k)) := new_far_cell m e r0 hrun hr0 k
  exact ⟨hnew, hlobe, hpartner⟩

/-- **Two hidden fixed-support flips force the Gray trap.**  If two
consecutive productive moves leave the cell projection unchanged and each old
edge remains occupied, every subsequent entry lies in the four lobe slots of
those two moves. -/
theorem two_hidden_preserved_absorb
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (hp0 : ProductiveStep m e r0 k)
    (hs0 : ∀ c, nextCell m e r0 (k+1) c = nextCell m e r0 k c)
    (ho0 : Occupied m e r0 (k+1) (oldSlot m e r0 k))
    (hp1 : ProductiveStep m e r0 (k+1))
    (hs1 : ∀ c, nextCell m e r0 (k+2) c = nextCell m e r0 (k+1) c)
    (ho1 : Occupied m e r0 (k+2) (oldSlot m e r0 (k+1))) :
    ∀ j, k+1 ≤ j →
      e j = e (k+1) ∨
      e j = m.bar (e (k+1)) ∨
      e j = e (k+2) ∨
      e j = m.bar (e (k+2)) := by
  have h0 := hidden_preserved_lobe m e r0 hrun hr0 k hp0 hs0 ho0
  have h1 := hidden_preserved_lobe m e r0 hrun hr0 (k+1) hp1 hs1 ho1
  have hAB : m.star (m.cellOf (e (k+1))) = m.cellOf (e (k+2)) :=
    h1.2.2.symm
  have hstep := hrun (k+1)
  rw [hAB] at hstep
  have hreg : reg m e r0 (k+1) (m.cellOf (e (k+2))) =
      m.bar (e (k+2)) := by
    have h := congrArg m.bar hstep
    rw [m.bar_invol] at h
    exact h.symm
  exact absorb_entries m e r0 hrun h0.2.1 h1.2.1 hAB rfl (Or.inr hreg)

end Echo
