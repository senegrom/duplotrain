import LinearBound

/-!
# Alternation structure for the echo machine

This file starts the structural part missing from the linear accounting bound.
The first theorem is unconditional: if two ascents of the same cell have
different successors, then the partner cell must have been ascended in the
interval between them. Thus steering variation cannot be generated locally;
it has to be fed by the mouth partner.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

theorem successor_change_has_partner_between
    (hrun : IsRun m e r0) {i j : Nat}
    (hcell : m.cellOf (e i) = m.cellOf (e j))
    (hij : i ≤ j)
    (hne : e (j+1) ≠ e (i+1)) :
    ∃ l, i < l ∧ l ≤ j ∧
      m.cellOf (e l) = m.star (m.cellOf (e i)) := by
  apply Classical.byContradiction
  intro hnone
  have hno : ∀ l, i < l → l ≤ j →
      m.cellOf (e l) ≠ m.star (m.cellOf (e i)) := by
    intro l hil hlj heq
    apply hnone
    exact ⟨l, hil, hlj, heq⟩
  exact hne (succ_repeat m e r0 hrun hcell hij hno)

/-- The cell immediately before a delivered entry is determined by that
entry alone. This is the predecessor form of `witness`. -/
theorem predecessor_cell
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c) (k : Nat) :
    m.cellOf (e k) = m.star (m.cellOf (m.bar (e (k+1)))) := by
  have hw := (witness m e r0 hrun hr0 k).1
  have hs := congrArg m.star hw
  rw [m.star_invol] at hs
  exact hs.symm

theorem equal_entry_equal_predecessor
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j : Nat} (heq : e (i+1) = e (j+1)) :
    m.cellOf (e i) = m.cellOf (e j) := by
  rw [predecessor_cell m e r0 hrun hr0 i,
    predecessor_cell m e r0 hrun hr0 j, heq]

def AlternationStep (k : Nat) : Prop :=
  ProductiveStep m e r0 k ∧ ¬ FirstStep m e k

theorem alternation_has_previous {k : Nat}
    (halt : AlternationStep m e r0 k) :
    ∃ j, j ≤ k ∧
      m.cellOf (e j) = m.cellOf (e (k+1)) ∧
      (∀ i, j < i → i ≤ k →
        m.cellOf (e i) ≠ m.cellOf (e (k+1))) ∧
      e (k+1) ≠ e j := by
  rcases productive_first_or_alternation m e r0 k halt.1 with hfirst | hprev
  · exact absurd hfirst halt.2
  · exact hprev

private theorem nodup_map_of_injective_on
    {f : Nat → Nat} {l : List Nat}
    (hinj : ∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y)
    (hnd : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x t ih =>
      simp only [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
        have hxy := hinj x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih
          (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb)) hnd.2

private theorem nodup_subset_length_nat {l S : List Nat}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) : l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x t ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ t, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      have hlen : (S.erase x).length = S.length - 1 := List.length_erase_of_mem hx
      rw [hlen] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- If alternations can be injected into cells, the accounting theorem gives
an explicit `2 * #cells + 1` bound. -/
theorem linear_two_per_cell_bound
    (cells : List Nat) (hcells : ∀ k, m.cellOf (e k) ∈ cells)
    (K : Nat) (alts : List Nat)
    (halts : alts.Nodup)
    (hcover : ∀ i, i < K → ProductiveStep m e r0 i →
      FirstStep m e i ∨ i ∈ alts)
    (hcharge : ∀ i, i ∈ alts → ∀ j, j ∈ alts →
      m.cellOf (e (i+1)) = m.cellOf (e (j+1)) → i = j)
    (ks : List Nat) (hks : ∀ k ∈ ks, k ≤ K)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 2 * cells.length + 1 := by
  have hmapnd : (alts.map (fun i => m.cellOf (e (i+1)))).Nodup :=
    nodup_map_of_injective_on hcharge halts
  have hmapsub : ∀ c ∈ alts.map (fun i => m.cellOf (e (i+1))), c ∈ cells := by
    intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact hcells (i+1)
  have haltslen : alts.length ≤ cells.length := by
    have hle := nodup_subset_length_nat hmapnd hmapsub
    simpa only [List.length_map] using hle
  have hlin := linear_accounting_bound m e r0 cells hcells K alts
    hcover ks hks hnd
  omega

end Echo
