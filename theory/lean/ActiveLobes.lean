import StarIndependent

/-!
# Active lobe cells before the Gray tail

A cell is active on an interval when its register takes two different values
there.  If an active lobe cell has an occupied lobe in its mouth partner too,
`changing_partner_lobes_absorb` forces a four-slot Gray tail during that
interval.  Consequently, before the first such tail the active lobe cells are
`star`-independent and occupy at most half of any star-closed cell universe.

This is the dynamical input required by `three_quarter_star_pair_bound`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The standard four-slot absorbing tail rooted at time `k`. -/
def GrayTail (k : Nat) : Prop :=
  ∀ q, k ≤ q →
    e q = e k ∨
    e q = m.bar (e k) ∨
    e q = reg m e r0 k (m.star (m.cellOf (e k))) ∨
    e q = m.bar (reg m e r0 k (m.star (m.cellOf (e k))))

/-- A register takes at least two different values on the closed interval
`[i,j]`. -/
def VariesOnInterval (i j c : Nat) : Prop :=
  ∃ p q, i ≤ p ∧ p ≤ j ∧ i ≤ q ∧ q ≤ j ∧
    reg m e r0 p c ≠ reg m e r0 q c

/-- If star-paired occupied lobes vary on an interval, a Gray tail starts
inside that interval. -/
theorem varying_partner_lobes_absorb
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j s t : Nat} (_hij : i ≤ j)
    (htCell : m.cellOf t = m.star (m.cellOf s))
    (hsLobe : LobeSlot m s) (htLobe : LobeSlot m t)
    (hsOcc : ∀ k, i ≤ k → k ≤ j → Occupied m e r0 k s)
    (htOcc : ∀ k, i ≤ k → k ≤ j → Occupied m e r0 k t)
    (hvar : VariesOnInterval m e r0 i j (m.cellOf s)) :
    ∃ k, i < k ∧ k ≤ j ∧ GrayTail m e r0 k := by
  rcases hvar with ⟨p, q, hip, hpj, hiq, hqj, hpqne⟩
  by_cases hpq : p ≤ q
  · obtain ⟨k, hpk, hkq, htail⟩ :=
      changing_partner_lobes_absorb m e r0 hrun hr0 hpq htCell
        hsLobe htLobe
        (fun l hpl hlq => hsOcc l (Nat.le_trans hip hpl)
          (Nat.le_trans hlq hqj))
        (fun l hpl hlq => htOcc l (Nat.le_trans hip hpl)
          (Nat.le_trans hlq hqj))
        hpqne.symm
    exact ⟨k, by omega, by omega, htail⟩
  · have hqp : q ≤ p := by omega
    obtain ⟨k, hqk, hkp, htail⟩ :=
      changing_partner_lobes_absorb m e r0 hrun hr0 hqp htCell
        hsLobe htLobe
        (fun l hql hlp => hsOcc l (Nat.le_trans hiq hql)
          (Nat.le_trans hlp hpj))
        (fun l hql hlp => htOcc l (Nat.le_trans hiq hql)
          (Nat.le_trans hlp hpj))
        hpqne
    exact ⟨k, by omega, by omega, htail⟩

/-- Before any Gray tail begins, active occupied-lobe cells cannot contain a
mouth-partner pair. -/
theorem active_lobes_star_independent
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j : Nat} (hij : i ≤ j)
    (active : List Nat)
    (hvar : ∀ c ∈ active, VariesOnInterval m e r0 i j c)
    (hlobe : ∀ c ∈ active,
      ∃ s, m.cellOf s = c ∧ LobeSlot m s ∧
        ∀ k, i ≤ k → k ≤ j → Occupied m e r0 k s)
    (hnoGray : ∀ k, i < k → k ≤ j → ¬ GrayTail m e r0 k) :
    StarIndependent m active := by
  intro c hc hstar
  obtain ⟨s, hsCell, hsLobe, hsOcc⟩ := hlobe c hc
  obtain ⟨t, htCell0, htLobe, htOcc⟩ := hlobe (m.star c) hstar
  have htCell : m.cellOf t = m.star (m.cellOf s) := by
    calc
      m.cellOf t = m.star c := htCell0
      _ = m.star (m.cellOf s) := by rw [hsCell]
  obtain ⟨k, hik, hkj, htail⟩ :=
    varying_partner_lobes_absorb m e r0 hrun hr0 hij htCell
      hsLobe htLobe hsOcc htOcc (by
        simpa [hsCell] using hvar c hc)
  exact (hnoGray k hik hkj) htail

/-- Quantitative form: before the Gray tail, active lobe cells occupy at most
half of a star-closed cell universe. -/
theorem active_lobes_half
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j : Nat} (hij : i ≤ j)
    (cells active : List Nat)
    (hnd : active.Nodup)
    (hsub : ∀ c ∈ active, c ∈ cells)
    (hclosed : StarClosed m cells)
    (hvar : ∀ c ∈ active, VariesOnInterval m e r0 i j c)
    (hlobe : ∀ c ∈ active,
      ∃ s, m.cellOf s = c ∧ LobeSlot m s ∧
        ∀ k, i ≤ k → k ≤ j → Occupied m e r0 k s)
    (hnoGray : ∀ k, i < k → k ≤ j → ¬ GrayTail m e r0 k) :
    2 * active.length ≤ cells.length := by
  exact star_independent_length m cells active hnd hsub hclosed
    (active_lobes_star_independent m e r0 hrun hr0 hij active
      hvar hlobe hnoGray)

end Echo
