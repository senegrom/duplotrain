import RecencyTreeBlock

/-!
# Components without a full edge are frozen

Inside a fixed-support epoch, a productive write has only two possibilities:

* if it changes to a different physical edge, the overwritten edge was full;
* if it stays on the same physical edge, productivity forces a flip to the
  opposite endpoint, so that edge is a lobe.

Consequently a component containing neither a full selected edge nor a lobe
selected edge cannot change at all while support is preserved.  This covers
the non-tree pseudoforest components: their registers contribute no dynamic
code within one support epoch.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A productive support-preserving write exposes either a full old edge or a
lobe old edge. -/
theorem productive_preserved_full_or_lobe
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (hp : ProductiveStep m e r0 k)
    (hpres : Occupied m e r0 (k+1) (oldSlot m e r0 k)) :
    Full m e r0 k (oldSlot m e r0 k) ∨
      LobeSlot m (oldSlot m e r0 k) := by
  by_cases hs : SameEdge m (oldSlot m e r0 k) (e (k+1))
  · right
    have hnew := productive_sameEdge_bar m e r0 hp hs
    unfold LobeSlot
    have hc := old_new_cell m e r0 hr0 k
    rw [hnew] at hc
    exact hc.symm
  · left
    exact old_edge_full_of_preserved m e r0 hrun hr0 k hp hpres hs

/-- Under fixed support, a write whose old selected edge is neither full nor a
lobe is unproductive. -/
theorem not_productive_of_preserved_nofull_nonlobe
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat)
    (hsupport : ∀ s, Occupied m e r0 k s ↔
      Occupied m e r0 (k+1) s)
    (hnfull : ¬ Full m e r0 k (oldSlot m e r0 k))
    (hnlobe : ¬ LobeSlot m (oldSlot m e r0 k)) :
    ¬ ProductiveStep m e r0 k := by
  intro hp
  have hold : Occupied m e r0 k (oldSlot m e r0 k) := by
    left
    exact old_register_confirmed m e r0 hr0 k
      (m.cellOf (e (k+1)))
  have hpres : Occupied m e r0 (k+1) (oldSlot m e r0 k) :=
    (hsupport (oldSlot m e r0 k)).mp hold
  rcases productive_preserved_full_or_lobe m e r0 hrun hr0 k hp hpres with
      hfull | hlobe
  · exact hnfull hfull
  · exact hnlobe hlobe

/-- One support-preserving step leaves every register of a no-full, non-lobe
component unchanged. -/
theorem nofull_nonlobe_component_step
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) (k : Nat)
    (hsupport : ∀ s, Occupied m e r0 k s ↔
      Occupied m e r0 (k+1) s)
    (hnfull : ∀ c ∈ cells,
      ¬ Full m e r0 k (reg m e r0 k c))
    (hnlobe : ∀ c ∈ cells,
      ¬ LobeSlot m (reg m e r0 k c)) :
    ∀ c ∈ cells, reg m e r0 (k+1) c = reg m e r0 k c := by
  intro c hc
  by_cases hwrite : m.cellOf (e (k+1)) ∈ cells
  · have hnp := not_productive_of_preserved_nofull_nonlobe
      m e r0 hrun hr0 k hsupport
      (by simpa [oldSlot] using
        hnfull (m.cellOf (e (k+1))) hwrite)
      (by simpa [oldSlot] using
        hnlobe (m.cellOf (e (k+1))) hwrite)
    have heq : e (k+1) =
        reg m e r0 k (m.cellOf (e (k+1))) := by
      by_cases h : e (k+1) =
          reg m e r0 k (m.cellOf (e (k+1)))
      · exact h
      · exact False.elim (hnp h)
    exact (unproductive_stall m e r0 k heq) c
  · have hne : m.cellOf (e (k+1)) ≠ c := by
      intro h
      apply hwrite
      rw [h]
      exact hc
    exact reg_skip m e r0 (k := k) (c := c) hne

/-- A no-full, non-lobe component is frozen throughout a fixed-support
interval. -/
theorem nofull_nonlobe_component_stable
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {i j : Nat} (hij : i ≤ j)
    (hsupport : ∀ k, i ≤ k → k < j → ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hnfull : ∀ k, i ≤ k → k < j → ∀ c ∈ cells,
      ¬ Full m e r0 k (reg m e r0 k c))
    (hnlobe : ∀ k, i ≤ k → k < j → ∀ c ∈ cells,
      ¬ LobeSlot m (reg m e r0 k c)) :
    ∀ c ∈ cells, reg m e r0 j c = reg m e r0 i c := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i+d := ⟨j-i, by omega⟩
  intro c hc
  induction d with
  | zero => rfl
  | succ n ih =>
      have hstep := nofull_nonlobe_component_step m e r0 hrun hr0
        cells (i+n)
        (hsupport (i+n) (by omega) (by omega))
        (hnfull (i+n) (by omega) (by omega))
        (hnlobe (i+n) (by omega) (by omega)) c hc
      have ih' := ih (by omega)
        (fun q hiq hqn => hsupport q hiq (by omega))
        (fun q hiq hqn => hnfull q hiq (by omega))
        (fun q hiq hqn => hnlobe q hiq (by omega))
      exact hstep.trans ih'

end Echo
