import AutomaticEpochBound

/-!
# Replay of forests rooted at externally encoded boundary cells

A mixed lobe component is a lobe root with ordinary tree edges attached.  The
lobe register is encoded separately as one bit; every attached non-root cell
points by recency toward that encoded root.

`RootedAtBoundary` generalises `RootedAt`: roots are an arbitrary finite cell
list whose register values are supplied externally.  Equal boundary registers
and equal occupied support then replay every certified attached cell.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A cell has a finite selected-edge route to an externally encoded root. -/
inductive RootedAtBoundary (k : Nat) (roots : List Nat) : Nat → Prop
  | root (c : Nat) (hc : c ∈ roots) : RootedAtBoundary k roots c
  | step (c : Nat)
      (hnfull : ¬ Full m e r0 k (reg m e r0 k c))
      (next : RootedAtBoundary k roots
        (m.cellOf (m.bar (reg m e r0 k c)))) :
      RootedAtBoundary k roots c

/-- Boundary-root replay at one cell. -/
theorem rootedAtBoundary_replay
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j c : Nat} {roots : List Nat}
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hroots : ∀ r ∈ roots, reg m e r0 j r = reg m e r0 i r)
    (hroot : RootedAtBoundary m e r0 i roots c) :
    reg m e r0 j c = reg m e r0 i c := by
  induction hroot with
  | root c hc => exact hroots c hc
  | step c hnfull next ih =>
      let s := reg m e r0 i c
      have hsI : Confirmed m e r0 i s := by
        dsimp [s]
        exact register_confirmed m e r0 hr0 i c
      have hoccI : Occupied m e r0 i s := Or.inl hsI
      have hoccJ : Occupied m e r0 j s :=
        (hsupport s).mp hoccI
      have hnotBar : ¬ Confirmed m e r0 j (m.bar s) := by
        intro hbJ
        have hregNext : reg m e r0 j (m.cellOf (m.bar s)) =
            reg m e r0 i (m.cellOf (m.bar s)) := by
          simpa [s] using ih
        have hbI : Confirmed m e r0 i (m.bar s) := by
          unfold Confirmed at hbJ ⊢
          rw [← hregNext]
          exact hbJ
        exact hnfull ⟨hsI, hbI⟩
      have hsJ : Confirmed m e r0 j s :=
        hoccJ.resolve_right hnotBar
      unfold Confirmed at hsJ
      have hc : m.cellOf s = c := by
        dsimp [s]
        exact reg_cell m e r0 hr0 i c
      rw [hc] at hsJ
      exact hsJ

/-- Every listed cell is boundary-rooted. -/
def BoundaryRootedCells (k : Nat) (roots cells : List Nat) : Prop :=
  ∀ c ∈ cells, RootedAtBoundary m e r0 k roots c

/-- Replay of a complete boundary-rooted forest. -/
theorem boundaryRootedCells_snap_replay
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (roots cells : List Nat) {i j : Nat}
    (hsupport : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (hroots : ∀ r ∈ roots, reg m e r0 j r = reg m e r0 i r)
    (hroot : BoundaryRootedCells m e r0 i roots cells) :
    snap m e r0 cells j = snap m e r0 cells i := by
  unfold snap
  apply List.map_congr_left
  intro c hc
  exact rootedAtBoundary_replay m e r0 hr0 hsupport hroots
    (hroot c hc)

/-- Ranked orientation toward an externally encoded root set. -/
def RankedTowardBoundary (k : Nat) (roots cells : List Nat)
    (rank : Nat → Nat) (c : Nat) : Prop :=
  c ∈ roots ∨
  (¬ Full m e r0 k (reg m e r0 k c) ∧
   m.cellOf (m.bar (reg m e r0 k c)) ∈ cells ∧
   rank (m.cellOf (m.bar (reg m e r0 k c))) < rank c)

/-- A decreasing rank manufactures all boundary-root certificates. -/
theorem boundaryRootedCells_of_rank
    (k : Nat) (roots cells : List Nat) (rank : Nat → Nat)
    (htoward : ∀ c ∈ cells,
      RankedTowardBoundary m e r0 k roots cells rank c) :
    BoundaryRootedCells m e r0 k roots cells := by
  intro c hc
  have hmain : ∀ n c, rank c ≤ n → c ∈ cells →
      RootedAtBoundary m e r0 k roots c := by
    intro n
    induction n with
    | zero =>
        intro c hrank hc
        rcases htoward c hc with hroot | ⟨hnfull, hmem, hlt⟩
        · exact RootedAtBoundary.root c hroot
        · omega
    | succ n ih =>
        intro c hrank hc
        rcases htoward c hc with hroot | ⟨hnfull, hmem, hlt⟩
        · exact RootedAtBoundary.root c hroot
        · apply RootedAtBoundary.step c hnfull
          apply ih
          · omega
          · exact hmem
  exact hmain (rank c) c (Nat.le_refl _) hc

/-- Recency rank provides a boundary-root orientation whenever every non-root
selected edge is non-full and non-lobed. -/
theorem rankedTowardBoundary_of_recency
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (k : Nat) (roots cells : List Nat)
    (lw : PositiveLastWriteMap m e k cells)
    (htarget : ∀ c ∈ cells,
      m.cellOf (m.bar (reg m e r0 k c)) ∈ cells)
    (hnlobe : ∀ c ∈ cells, c ∉ roots →
      m.cellOf (m.bar (reg m e r0 k c)) ≠ c)
    (hnfull : ∀ c ∈ cells, c ∉ roots →
      ¬ Full m e r0 k (reg m e r0 k c)) :
    ∀ c ∈ cells,
      RankedTowardBoundary m e r0 k roots cells
        (recencyRank m e k lw) c := by
  intro c hc
  by_cases hroot : c ∈ roots
  · exact Or.inl hroot
  · right
    refine ⟨hnfull c hc hroot, htarget c hc, ?_⟩
    obtain ⟨l, hcl, hlk, hltarget⟩ :=
      later_target_write_of_nonfull m e r0 hrun hr0
        (lw.positive c hc) (lw.spec c hc)
        (hnfull c hc hroot) (hnlobe c hc hroot)
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
