import CertifiedEpochBound

/-!
# Recency manufactures the tree rank

At a state `k`, suppose cell `c` was most recently written at positive time
`j`.  Its selected edge was created at time `j`; at time `j-1` the opposite
endpoint was selected by the target cell.  If that target cell had not been
written after `j`, the edge would still be full at time `k`.

Therefore every selected edge which is both non-full and non-lobed points to a
cell written strictly more recently.  Ranking a cell by

    k - (time of its most recent write)

then strictly decreases toward the unique full edge.  This is the dynamic
source of the `RankedToward` certificates used by `RootRank.lean`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- `j` is the last entry into cell `c` at or before time `k`. -/
def LastWriteAt (k c j : Nat) : Prop :=
  j ≤ k ∧ m.cellOf (e j) = c ∧
  ∀ l, j < l → l ≤ k → m.cellOf (e l) ≠ c

/-- Last-write witnesses reproduce the current register. -/
theorem reg_eq_of_lastWriteAt {k c j : Nat}
    (h : LastWriteAt m e k c j) :
    reg m e r0 k c = e j := by
  exact reg_last_write m e r0 h.2.1 h.1 h.2.2

/-- Every cell visited by time `k` has a last visit. -/
theorem exists_lastWriteAt {k c : Nat}
    (hex : ∃ j, j ≤ k ∧ m.cellOf (e j) = c) :
    ∃ j, LastWriteAt m e k c j := by
  induction k with
  | zero =>
      obtain ⟨j, hj, hc⟩ := hex
      have hj0 : j = 0 := by omega
      subst j
      exact ⟨0, Nat.le_refl _, hc, fun l h _ => by omega⟩
  | succ n ih =>
      by_cases hk : m.cellOf (e (n+1)) = c
      · exact ⟨n+1, Nat.le_refl _, hk, fun l h _ => by omega⟩
      · have hex' : ∃ j, j ≤ n ∧ m.cellOf (e j) = c := by
          obtain ⟨j, hj, hc⟩ := hex
          by_cases hje : j = n+1
          · exact absurd (hje ▸ hc) hk
          · exact ⟨j, by omega, hc⟩
        obtain ⟨j, hj, hc, hlast⟩ := ih hex'
        refine ⟨j, by omega, hc, ?_⟩
        intro l hjl hlk
        by_cases hle : l = n+1
        · exact hle ▸ hk
        · exact hlast l hjl (by omega)

/-- If a positive visit exists, the last visit is positive too. -/
theorem exists_positive_lastWriteAt {k c : Nat}
    (hex : ∃ j, 0 < j ∧ j ≤ k ∧ m.cellOf (e j) = c) :
    ∃ j, 0 < j ∧ LastWriteAt m e k c j := by
  obtain ⟨q, hqpos, hqk, hqc⟩ := hex
  obtain ⟨j, hj⟩ := exists_lastWriteAt m e
    ⟨q, hqk, hqc⟩
  have hjpos : 0 < j := by
    by_cases hz : j = 0
    · subst j
      exact absurd hqc (hj.2.2 q hqpos hqk)
    · omega
  exact ⟨j, hjpos, hj⟩

/-- A non-full, non-lobed selected edge points to a cell written after the
source cell's last write. -/
theorem later_target_write_of_nonfull
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {j k c : Nat}
    (hjpos : 0 < j)
    (hlast : LastWriteAt m e k c j)
    (hnfull : ¬ Full m e r0 k (reg m e r0 k c))
    (hnlobe : m.cellOf (m.bar (reg m e r0 k c)) ≠ c) :
    ∃ l, j < l ∧ l ≤ k ∧
      m.cellOf (e l) = m.cellOf (m.bar (reg m e r0 k c)) := by
  cases j with
  | zero => omega
  | succ p =>
      have hreg : reg m e r0 k c = e (p+1) :=
        reg_eq_of_lastWriteAt m e r0 hlast
      have hw := witness m e r0 hrun hr0 p
      let d := m.cellOf (m.bar (reg m e r0 k c))
      have hdcell : d = m.star (m.cellOf (e p)) := by
        dsimp [d]
        rw [hreg]
        exact hw.1
      have hdreg : reg m e r0 p d = m.bar (reg m e r0 k c) := by
        rw [hdcell, hreg]
        exact hw.2
      apply Classical.byContradiction
      intro hnone
      have hno : ∀ l, p < l → l ≤ k → m.cellOf (e l) ≠ d := by
        intro l hpl hlk
        by_cases hlj : l = p+1
        · subst l
          rw [hlast.2.1]
          exact hnlobe.symm
        · intro hld
          apply hnone
          exact ⟨l, by omega, hlk, hld⟩
      have hpk : p ≤ k := Nat.le_trans (Nat.le_succ p) hlast.1
      obtain ⟨delta, hk⟩ : ∃ delta, k = p + delta :=
        ⟨k-p, (Nat.add_sub_of_le hpk).symm⟩
      have hstable : reg m e r0 k d = reg m e r0 p d := by
        rw [hk]
        exact reg_stable m e r0 delta
          (fun l hpl hl => hno l hpl (by rw [hk]; exact hl))
      have hs : Confirmed m e r0 k (reg m e r0 k c) :=
        old_register_confirmed m e r0 hr0 k c
      have hb : Confirmed m e r0 k (m.bar (reg m e r0 k c)) := by
        unfold Confirmed
        dsimp [d] at hstable hdreg ⊢
        exact hstable.trans hdreg
      exact hnfull ⟨hs, hb⟩

/-- A map assigning a positive last-write time to every listed cell. -/
structure PositiveLastWriteMap
    (m : Machine) (e : Nat → Nat) (k : Nat) (cells : List Nat) where
  time : Nat → Nat
  positive : ∀ c, c ∈ cells → 0 < time c
  spec : ∀ c, c ∈ cells → LastWriteAt m e k c (time c)

/-- Positive visits to every finite listed cell manufacture a last-write map. -/
noncomputable def positiveLastWriteMapOfVisits
    (k : Nat) (cells : List Nat)
    (hvisit : ∀ c ∈ cells,
      ∃ j, 0 < j ∧ j ≤ k ∧ m.cellOf (e j) = c) :
    PositiveLastWriteMap m e k cells := by
  classical
  let lastTime : Nat → Nat := fun c =>
    if hc : c ∈ cells then
      (exists_positive_lastWriteAt m e (hvisit c hc)).choose
    else 0
  refine ⟨lastTime, ?_, ?_⟩
  · intro c hc
    dsimp [lastTime]
    rw [dif_pos hc]
    exact (exists_positive_lastWriteAt m e (hvisit c hc)).choose_spec.1
  · intro c hc
    dsimp [lastTime]
    rw [dif_pos hc]
    exact (exists_positive_lastWriteAt m e (hvisit c hc)).choose_spec.2

/-- Recency rank at state `k`: more recently written cells have lower rank. -/
def recencyRank {cells : List Nat} (k : Nat)
    (lw : PositiveLastWriteMap m e k cells) (c : Nat) : Nat :=
  k - lw.time c

/-- A finite component with one designated full edge and no lobe edges obtains
its `RankedToward` certificate automatically from last-write recency. -/
theorem rankedToward_of_recency
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k f : Nat) (cells : List Nat)
    (lw : PositiveLastWriteMap m e k cells)
    (htarget : ∀ c ∈ cells,
      m.cellOf (m.bar (reg m e r0 k c)) ∈ cells)
    (hnlobe : ∀ c ∈ cells,
      c ≠ m.cellOf f → c ≠ m.cellOf (m.bar f) →
      m.cellOf (m.bar (reg m e r0 k c)) ≠ c)
    (hnfull : ∀ c ∈ cells,
      c ≠ m.cellOf f → c ≠ m.cellOf (m.bar f) →
      ¬ Full m e r0 k (reg m e r0 k c)) :
    ∀ c ∈ cells,
      RankedToward m e r0 k f cells (recencyRank m e k lw) c := by
  intro c hc
  by_cases hleft : c = m.cellOf f
  · exact Or.inl hleft
  · by_cases hright : c = m.cellOf (m.bar f)
    · exact Or.inr (Or.inl hright)
    · right; right
      refine ⟨hnfull c hc hleft hright, htarget c hc, ?_⟩
      obtain ⟨l, hcl, hlk, hltarget⟩ :=
        later_target_write_of_nonfull m e r0 hrun hr0
          (lw.positive c hc) (lw.spec c hc)
          (hnfull c hc hleft hright) (hnlobe c hc hleft hright)
      let d := m.cellOf (m.bar (reg m e r0 k c))
      have hdmem : d ∈ cells := htarget c hc
      have hlastD := lw.spec d hdmem
      have hld : l ≤ lw.time d := by
        apply Classical.byContradiction
        intro h
        have hafter : lw.time d < l := by omega
        exact (hlastD.2.2 l hafter hlk) hltarget
      unfold recencyRank
      change k - lw.time d < k - lw.time c
      have hcd : lw.time c < lw.time d :=
        Nat.lt_of_lt_of_le hcl hld
      have hdK := hlastD.1
      have hcK : lw.time c < k := Nat.lt_of_lt_of_le hcd hdK
      exact Nat.sub_lt_sub_left hcK hcd

end Echo
