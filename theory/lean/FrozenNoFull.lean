import TreeLobeFrozenCode

/-!
# No-full, non-lobe cells are frozen in a fixed support

Consider a write to a cell while the occupied jump-edge support is unchanged.
If the old and new slots lie on different jump edges, preservation of the old
edge forces it to have been full before the write.  If they lie on the same
edge and the write is productive, the two slots are opposite endpoints of a
lobe.  Therefore a non-lobe cell incident to no full edge cannot change.

Iterating this one-step statement freezes every such block over an entire
fixed-support interval.  This supplies the `FrozenOn` hypothesis used by the
complete tree/lobe epoch code.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The cell has no lobe slot. -/
def NoLobeCell (c : Nat) : Prop :=
  ∀ s, m.cellOf s = c → m.cellOf (m.bar s) ≠ c

/-- No edge represented from this cell is full at time `k`. -/
def NoFullCell (k c : Nat) : Prop :=
  ∀ s, m.cellOf s = c → ¬ Full m e r0 k s

/-- **One-step freezing lemma.** -/
theorem reg_step_eq_of_noFull_noLobe
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k c : Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hnfull : NoFullCell m e r0 k c)
    (hnlobe : NoLobeCell m c) :
    reg m e r0 (k+1) c = reg m e r0 k c := by
  by_cases hc : c = m.cellOf (e (k+1))
  · let new := e (k+1)
    let old := reg m e r0 k (m.cellOf new)
    have hc' : c = m.cellOf new := hc
    by_cases heq : old = new
    · have hw : reg m e r0 (k+1) (m.cellOf new) = new :=
        reg_write m e r0 rfl
      rw [hc', hw]
      exact heq.symm
    · have hp : ProductiveStep m e r0 k := by
        intro h
        exact heq h.symm
      have holdConf : Confirmed m e r0 k old := by
        exact old_register_confirmed m e r0 hr0 k (m.cellOf new)
      have holdOcc : Occupied m e r0 k old := Or.inl holdConf
      have hpres : Occupied m e r0 (k+1) old :=
        (hsupport old).mp holdOcc
      by_cases hs : SameEdge m old new
      · have hnew : new = m.bar old :=
          productive_sameEdge_bar m e r0 hp hs
        have hback : m.bar new = old := by
          rw [hnew, m.bar_invol]
        have holdCell : m.cellOf old = m.cellOf new := by
          simpa [old] using reg_cell m e r0 hr0 k (m.cellOf new)
        have hlobe : m.cellOf (m.bar new) = m.cellOf new := by
          rw [hback]
          exact holdCell
        exact absurd hlobe (hnlobe new (by simpa [new, hc'] using hc'.symm))
      · have hfull := old_edge_full_of_preserved m e r0
          hrun hr0 k hp hpres hs
        have holdCell : m.cellOf old = c := by
          calc
            m.cellOf old = m.cellOf new := by
              simpa [old] using reg_cell m e r0 hr0 k (m.cellOf new)
            _ = c := hc'.symm
        exact absurd hfull (hnfull old holdCell)
  · exact reg_skip m e r0 (k := k) (c := c) hc.symm

/-- A list of no-full non-lobe cells has an unchanged snapshot for one fixed-
support step. -/
theorem snap_step_eq_of_noFull_noLobe
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) (cells : List Nat)
    (hsupport : ∀ s,
      Occupied m e r0 k s ↔ Occupied m e r0 (k+1) s)
    (hnfull : ∀ c ∈ cells, NoFullCell m e r0 k c)
    (hnlobe : ∀ c ∈ cells, NoLobeCell m c) :
    snap m e r0 cells (k+1) = snap m e r0 cells k := by
  unfold snap
  apply List.map_congr_left
  intro c hc
  exact reg_step_eq_of_noFull_noLobe m e r0 hrun hr0 k c
    hsupport (hnfull c hc) (hnlobe c hc)

/-- Fixed support on an interval. -/
def SupportFixed (lo hi : Nat) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → ∀ j, lo ≤ j → j ≤ hi → ∀ s,
    Occupied m e r0 i s ↔ Occupied m e r0 j s

/-- No listed cell is incident to a full edge anywhere in the interval. -/
def NoFullThroughout (lo hi : Nat) (cells : List Nat) : Prop :=
  ∀ k, lo ≤ k → k ≤ hi → ∀ c ∈ cells,
    NoFullCell m e r0 k c

/-- Snapshot stability from an earlier to a later point in the interval. -/
theorem snap_eq_of_noFull_interval
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat) (cells : List Nat)
    (hfixed : SupportFixed m e r0 lo hi)
    (hnfull : NoFullThroughout m e r0 lo hi cells)
    (hnlobe : ∀ c ∈ cells, NoLobeCell m c)
    {i j : Nat}
    (hlo : lo ≤ i) (hij : i ≤ j) (hjhi : j ≤ hi) :
    snap m e r0 cells j = snap m e r0 cells i := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j-i, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
      have hdi : i + d ≤ i + (d+1) := by omega
      have hloD : lo ≤ i + d := by omega
      have hhiD : i + d ≤ hi := by omega
      have hhiS : i + d + 1 ≤ hi := by omega
      have hs : ∀ s,
          Occupied m e r0 (i+d) s ↔
            Occupied m e r0 (i+d+1) s :=
        hfixed (i+d) hloD hhiD (i+d+1) (by omega) hhiS
      have hstep := snap_step_eq_of_noFull_noLobe m e r0
        hrun hr0 (i+d) cells hs
        (hnfull (i+d) hloD hhiD) hnlobe
      calc
        snap m e r0 cells (i + (d+1))
            = snap m e r0 cells (i+d+1) := by omega
        _ = snap m e r0 cells (i+d) := hstep
        _ = snap m e r0 cells i := ih (by omega)

/-- The interval block satisfies the abstract `FrozenOn` interface. -/
theorem frozenOn_of_noFull_noLobe
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi : Nat) (cells : List Nat)
    (hfixed : SupportFixed m e r0 lo hi)
    (hnfull : NoFullThroughout m e r0 lo hi cells)
    (hnlobe : ∀ c ∈ cells, NoLobeCell m c) :
    FrozenOn m e r0 (fun k => lo ≤ k ∧ k ≤ hi) cells := by
  intro i hiI j hjI
  by_cases hij : i ≤ j
  · exact snap_eq_of_noFull_interval m e r0 hrun hr0
      lo hi cells hfixed hnfull hnlobe hiI.1 hij hjI.2
  · have hji : j ≤ i := by omega
    exact (snap_eq_of_noFull_interval m e r0 hrun hr0
      lo hi cells hfixed hnfull hnlobe hjI.1 hji hiI.2).symm

end Echo
