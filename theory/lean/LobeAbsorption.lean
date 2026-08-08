import SupportSize

/-!
# Star-paired occupied lobes absorb on first visit

A lobe edge has both jump endpoints in one cell.  If it is occupied, that
cell's unique register must select one of its two endpoints.  Consequently,
if a cell and its mouth partner both have occupied lobe edges, the first visit
to either cell satisfies the hypotheses of `absorb_entries`: from then on all
entries lie in a four-slot Gray square.

This is the dynamical reason active lobe cells outside the absorbed tail can be
charged injectively to non-lobe partner cells.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A jump edge whose two endpoints lie in the same cell. -/
def LobeSlot (s : Nat) : Prop :=
  m.cellOf (m.bar s) = m.cellOf s

/-- Either endpoint represents the same lobe property. -/
theorem lobe_bar {s : Nat} :
    LobeSlot m (m.bar s) ↔ LobeSlot m s := by
  unfold LobeSlot
  rw [m.bar_invol]
  exact eq_comm

/-- Occupancy of a lobe forces its cell's register to be one of its two
endpoints. -/
theorem occupied_lobe_register {k s : Nat}
    (hlobe : LobeSlot m s)
    (hocc : Occupied m e r0 k s) :
    reg m e r0 k (m.cellOf s) = s ∨
    reg m e r0 k (m.cellOf s) = m.bar s := by
  rcases hocc with hs | hb
  · exact Or.inl hs
  · unfold Confirmed at hb
    rw [hlobe] at hb
    exact Or.inr hb

/-- If the current entry's cell carries an occupied lobe, the entry itself is
one of that lobe's endpoints and is therefore a lobe slot. -/
theorem entry_is_lobe_of_occupied {k s : Nat}
    (hcell : m.cellOf (e k) = m.cellOf s)
    (hlobe : LobeSlot m s)
    (hocc : Occupied m e r0 k s) :
    LobeSlot m (e k) := by
  have hr := occupied_lobe_register m e r0 hlobe hocc
  have hw : reg m e r0 k (m.cellOf s) = e k := by
    rw [← hcell]
    exact reg_write m e r0 rfl
  rcases hr with hr | hr
  · have he : e k = s := hw.symm.trans hr
    rw [he]
    exact hlobe
  · have he : e k = m.bar s := hw.symm.trans hr
    rw [he]
    exact (lobe_bar m).mpr hlobe

/-- A register selecting an occupied partner lobe is itself a lobe slot. -/
theorem partner_register_is_lobe {k c t : Nat}
    (hcell : m.cellOf t = m.star c)
    (hlobe : LobeSlot m t)
    (hocc : Occupied m e r0 k t) :
    LobeSlot m (reg m e r0 k (m.star c)) := by
  have hr := occupied_lobe_register m e r0 hlobe hocc
  rw [hcell] at hr
  rcases hr with hr | hr
  · rw [hr]
    exact hlobe
  · rw [hr]
    exact (lobe_bar m).mpr hlobe

/-- **Occupied star-paired lobes are an immediate trap on visit.** -/
theorem occupied_partner_lobes_absorb
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {k s t : Nat}
    (hsCell : m.cellOf (e k) = m.cellOf s)
    (htCell : m.cellOf t = m.star (m.cellOf s))
    (hsLobe : LobeSlot m s) (htLobe : LobeSlot m t)
    (hsOcc : Occupied m e r0 k s)
    (htOcc : Occupied m e r0 k t) :
    ∀ j, k ≤ j →
      e j = e k ∨
      e j = m.bar (e k) ∨
      e j = reg m e r0 k (m.star (m.cellOf (e k))) ∨
      e j = m.bar (reg m e r0 k (m.star (m.cellOf (e k)))) := by
  let a := e k
  let b := reg m e r0 k (m.star (m.cellOf (e k)))
  have ha : m.cellOf (m.bar a) = m.cellOf a :=
    entry_is_lobe_of_occupied m e r0 hsCell hsLobe hsOcc
  have htCell' : m.cellOf t = m.star (m.cellOf (e k)) := by
    rw [hsCell]
    exact htCell
  have hb : m.cellOf (m.bar b) = m.cellOf b := by
    exact partner_register_is_lobe m e r0 htCell' htLobe htOcc
  have hAB : m.star (m.cellOf a) = m.cellOf b := by
    dsimp [a, b]
    exact (reg_cell m e r0 hr0 k _).symm
  have hreg : reg m e r0 k (m.cellOf b) = b := by
    dsimp [b]
    rw [reg_cell m e r0 hr0 k]
  exact absorb_entries m e r0 hrun ha hb hAB rfl (Or.inl hreg)

/-- Register change over an interval forces an intervening entry into that
cell. -/
theorem reg_change_has_write {i j c : Nat}
    (hij : i ≤ j)
    (hchg : reg m e r0 j c ≠ reg m e r0 i c) :
    ∃ l, i < l ∧ l ≤ j ∧ m.cellOf (e l) = c := by
  apply Classical.byContradiction
  intro hnone
  have hno : ∀ l, i < l → l ≤ j → m.cellOf (e l) ≠ c := by
    intro l hl1 hl2 heq
    apply hnone
    exact ⟨l, hl1, hl2, heq⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = i+d := ⟨j-i, by omega⟩
  exact hchg (reg_stable m e r0 d hno)

/-- If both star-paired lobe edges remain occupied through an interval and one
register changes, absorption occurs at an intervening visit. -/
theorem changing_partner_lobes_absorb
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j s t : Nat} (hij : i ≤ j)
    (htCell : m.cellOf t = m.star (m.cellOf s))
    (hsLobe : LobeSlot m s) (htLobe : LobeSlot m t)
    (hsOcc : ∀ k, i ≤ k → k ≤ j → Occupied m e r0 k s)
    (htOcc : ∀ k, i ≤ k → k ≤ j → Occupied m e r0 k t)
    (hchg : reg m e r0 j (m.cellOf s) ≠
      reg m e r0 i (m.cellOf s)) :
    ∃ k, i < k ∧ k ≤ j ∧
      (∀ q, k ≤ q →
        e q = e k ∨
        e q = m.bar (e k) ∨
        e q = reg m e r0 k (m.star (m.cellOf (e k))) ∨
        e q = m.bar (reg m e r0 k (m.star (m.cellOf (e k))))) := by
  obtain ⟨k, hik, hkj, hkcell⟩ :=
    reg_change_has_write m e r0 hij hchg
  refine ⟨k, hik, hkj, ?_⟩
  exact occupied_partner_lobes_absorb m e r0 hrun hr0
    hkcell htCell hsLobe htLobe
    (hsOcc k (Nat.le_of_lt hik) hkj)
    (htOcc k (Nat.le_of_lt hik) hkj)

end Echo
