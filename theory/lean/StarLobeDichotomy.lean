import RootRank

/-!
# Persistent lobes: half density or immediate absorption

A lobe support edge has both jump endpoints in one cell.  If that edge remains
occupied throughout a support epoch, the cell's register is always one of its
two lobe slots.  Consequently, when a cell and its mouth partner both carry
persistent lobe edges, entering either cell satisfies the hypotheses of the
already proved `absorb_entries` theorem and traps the future walk in four
slots.

This gives the exact dynamical dichotomy needed by `RootRank`'s counting
lemma: before the Gray trap, persistent active lobe cells are star-separated
and therefore occupy at most half of the finite cell universe.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A lobe cell witnessed by an actual lobe entry during `[lo, hi]`, whose
jump edge stays occupied throughout that interval. -/
def PersistentLobeWitness (lo hi c : Nat) : Prop :=
  ∃ a k,
    m.cellOf a = c ∧
    m.cellOf (m.bar a) = c ∧
    lo ≤ k ∧ k ≤ hi ∧
    e k = a ∧
    ∀ t, lo ≤ t → t ≤ hi → Occupied m e r0 t a

/-- Occupancy of a lobe edge says exactly that the cell register stores one of
its two endpoints. -/
theorem reg_eq_endpoint_of_occupied_lobe
    {k a c : Nat}
    (ha : m.cellOf a = c)
    (hbar : m.cellOf (m.bar a) = c)
    (hocc : Occupied m e r0 k a) :
    reg m e r0 k c = a ∨ reg m e r0 k c = m.bar a := by
  rcases hocc with h | h
  · left
    unfold Confirmed at h
    simpa [ha] using h
  · right
    unfold Confirmed at h
    simpa [hbar] using h

/-- Two occupied mouth-partner lobes absorb as soon as the first one is
entered. -/
theorem occupied_partner_lobes_absorb
    (hrun : IsRun m e r0)
    {k a b : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hstar : m.star (m.cellOf a) = m.cellOf b)
    (he : e k = a)
    (hocc : Occupied m e r0 k b) :
    ∀ j, k ≤ j →
      e j = a ∨ e j = m.bar a ∨
      e j = b ∨ e j = m.bar b := by
  have hreg : reg m e r0 k (m.cellOf b) = b ∨
      reg m e r0 k (m.cellOf b) = m.bar b :=
    reg_eq_endpoint_of_occupied_lobe m e r0 rfl hb hocc
  exact absorb_entries m e r0 hrun ha hb hstar he hreg

/-- Persistent lobe witnesses in star-paired cells produce an absorbing
four-slot tail, at the visit time supplied by the first witness. -/
theorem persistent_star_pair_absorbs
    (hrun : IsRun m e r0)
    {lo hi c : Nat}
    (hc : PersistentLobeWitness m e r0 lo hi c)
    (hs : PersistentLobeWitness m e r0 lo hi (m.star c)) :
    ∃ k a b,
      lo ≤ k ∧ k ≤ hi ∧
      ∀ j, k ≤ j →
        e j = a ∨ e j = m.bar a ∨
        e j = b ∨ e j = m.bar b := by
  rcases hc with ⟨a, k, hac, habarc, hlo, hhi, he, _⟩
  rcases hs with ⟨b, kb, hbc, hbbarc, _, _, _, hpersist⟩
  have ha : m.cellOf (m.bar a) = m.cellOf a :=
    habarc.trans hac.symm
  have hb : m.cellOf (m.bar b) = m.cellOf b :=
    hbbarc.trans hbc.symm
  have hstar : m.star (m.cellOf a) = m.cellOf b := by
    rw [hac, hbc]
  have hocc : Occupied m e r0 k b := hpersist k hlo hhi
  exact ⟨k, a, b, hlo, hhi,
    occupied_partner_lobes_absorb m e r0 hrun ha hb hstar he hocc⟩

/-- **Persistent-lobe dichotomy.**  A duplicate-free list of persistent lobe
cells is star-separated, or some star-paired members already generate a
four-slot absorbing tail. -/
theorem persistent_lobes_separated_or_absorb
    (hrun : IsRun m e r0)
    (lo hi : Nat) (active : List Nat)
    (hnd : active.Nodup)
    (hwit : ∀ c ∈ active,
      PersistentLobeWitness m e r0 lo hi c) :
    StarSeparated m active ∨
    ∃ c k a b,
      c ∈ active ∧ m.star c ∈ active ∧
      lo ≤ k ∧ k ≤ hi ∧
      ∀ j, k ≤ j →
        e j = a ∨ e j = m.bar a ∨
        e j = b ∨ e j = m.bar b := by
  by_cases hsep : ∀ c ∈ active, m.star c ∉ active
  · exact Or.inl ⟨hnd, hsep⟩
  · apply Or.inr
    have hpair : ∃ c, c ∈ active ∧ m.star c ∈ active := by
      apply Classical.byContradiction
      intro hnone
      apply hsep
      intro c hc hsc
      apply hnone
      exact ⟨c, hc, hsc⟩
    rcases hpair with ⟨c, hc, hsc⟩
    rcases persistent_star_pair_absorbs m e r0 hrun
      (hwit c hc) (hwit (m.star c) hsc) with
      ⟨k, a, b, hlo, hhi, htail⟩
    exact ⟨c, k, a, b, hc, hsc, hlo, hhi, htail⟩

/-- Quantitative form: either active persistent lobes occupy at most half the
chosen cell universe, or the run has already entered a four-slot tail. -/
theorem persistent_lobes_half_or_absorb
    (hrun : IsRun m e r0)
    (lo hi : Nat) (active cells : List Nat)
    (hnd : active.Nodup)
    (hcells : cells.Nodup)
    (hcover : ∀ c ∈ active,
      c ∈ cells ∧ m.star c ∈ cells)
    (hwit : ∀ c ∈ active,
      PersistentLobeWitness m e r0 lo hi c) :
    2 * active.length ≤ cells.length ∨
    ∃ c k a b,
      c ∈ active ∧ m.star c ∈ active ∧
      lo ≤ k ∧ k ≤ hi ∧
      ∀ j, k ≤ j →
        e j = a ∨ e j = m.bar a ∨
        e j = b ∨ e j = m.bar b := by
  rcases persistent_lobes_separated_or_absorb m e r0 hrun
      lo hi active hnd hwit with hsep | habs
  · exact Or.inl (starSeparated_count m active cells hsep hcells hcover)
  · exact Or.inr habs

end Echo
