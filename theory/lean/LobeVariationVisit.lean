import LobeToggle
import ActiveLobes

/-!
# Variation of a persistent lobe forces a partner-cell visit

A register which differs at two times must change at some adjacent step between
them.  For a persistent occupied lobe, `occupied_lobe_change_has_partner_predecessor`
then identifies the preceding entry cell as the lobe's mouth partner.

This turns interval-level activity into an actual visit witness, needed for
early-visit/trapping arguments on loaded support components.
-/

namespace Echo

private theorem exists_adjacent_change_gap
    {α : Type} (f : Nat → α) :
    ∀ d p, f p ≠ f (p+d+1) →
      ∃ k, p ≤ k ∧ k < p+d+1 ∧ f (k+1) ≠ f k := by
  intro d
  induction d with
  | zero =>
      intro p hne
      exact ⟨p, Nat.le_refl _, by omega, hne.symm⟩
  | succ d ih =>
      intro p hne
      by_cases hfirst : f (p+1) = f p
      · have htail : f (p+1) ≠ f ((p+1)+d+1) := by
          intro h
          apply hne
          calc
            f p = f (p+1) := hfirst.symm
            _ = f ((p+1)+d+1) := h
            _ = f (p+(d+1)+1) := by congr 1 <;> omega
        obtain ⟨k, hkLo, hkHi, hkNe⟩ := ih (p+1) htail
        refine ⟨k, by omega, ?_, hkNe⟩
        omega
      · exact ⟨p, Nat.le_refl _, by omega, hfirst⟩

/-- A discrete function which differs at two times changes at an adjacent
step in between. -/
theorem exists_adjacent_change
    {α : Type} (f : Nat → α)
    {p q : Nat} (hpq : p < q) (hne : f p ≠ f q) :
    ∃ k, p ≤ k ∧ k < q ∧ f (k+1) ≠ f k := by
  obtain ⟨d, hq⟩ : ∃ d, q = p+d+1 :=
    ⟨q-p-1, by omega⟩
  have hgap : f p ≠ f (p+d+1) := by
    rw [← hq]
    exact hne
  obtain ⟨k, hkLo, hkHi, hkNe⟩ :=
    exists_adjacent_change_gap f d p hgap
  exact ⟨k, hkLo, by omega, hkNe⟩

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Any interval variation contains an adjacent register change. -/
theorem varies_has_adjacent_change
    {I J c : Nat}
    (hvar : VariesOnInterval m e r0 I J c) :
    ∃ k, I ≤ k ∧ k < J ∧
      reg m e r0 (k+1) c ≠ reg m e r0 k c := by
  rcases hvar with ⟨p, q, hpI, hpJ, hqI, hqJ, hpq⟩
  by_cases hpqOrder : p < q
  · obtain ⟨k, hpk, hkq, hkNe⟩ :=
      exists_adjacent_change (fun t => reg m e r0 t c)
        hpqOrder hpq
    exact ⟨k, by omega, by omega, hkNe⟩
  · have hqpOrder : q < p := by
      by_cases heq : p = q
      · exact False.elim (hpq (heq ▸ rfl))
      · omega
    obtain ⟨k, hqk, hkp, hkNe⟩ :=
      exists_adjacent_change (fun t => reg m e r0 t c)
        hqpOrder hpq.symm
    exact ⟨k, by omega, by omega, hkNe⟩

/-- **Persistent occupied-lobe activity produces a partner visit.** -/
theorem varying_occupied_lobe_has_partner_visit
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {I J a : Nat}
    (hlobe : m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, I ≤ k → k ≤ J → Occupied m e r0 k a)
    (hvar : VariesOnInterval m e r0 I J (m.cellOf a)) :
    ∃ k, I ≤ k ∧ k < J ∧
      m.cellOf (e k) = m.star (m.cellOf a) := by
  obtain ⟨k, hkI, hkJ, hkChange⟩ :=
    varies_has_adjacent_change m e r0 hvar
  have hoccNext : Occupied m e r0 (k+1) a :=
    hocc (k+1) (by omega) (by omega)
  exact ⟨k, hkI, hkJ,
    occupied_lobe_change_has_partner_predecessor
      m e r0 hrun hr0 hlobe hoccNext hkChange⟩

end Echo
