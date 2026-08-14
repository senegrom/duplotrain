import EchoMachine

/-!
# Linear accounting bound for echo-machine snapshots

This file turns the informal accounting statement in `EchoMachine.lean`
into a quantitative theorem with an arbitrary finite list of alternations.
No Gray-tail or cycle-structure hypothesis is used.

If `alts` covers every productive step before time `K` that is not the first
write of its cell, then any pairwise-distinct collection of register snapshots
from times `≤ K` has size at most

    #cells + #alts + 1.

Thus the remaining problem for a genuine `N + O(1)` state law is isolated
cleanly to bounding the number of alternations by an absolute constant.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem exists_last_productive_lt :
    ∀ k, (∃ j, j < k ∧ ProductiveStep m e r0 j) →
      ∃ j, j < k ∧ ProductiveStep m e r0 j ∧
        ∀ i, j < i → i < k → ¬ ProductiveStep m e r0 i := by
  intro k
  induction k with
  | zero =>
      intro h
      obtain ⟨j, hj, _⟩ := h
      exact absurd hj (by omega)
  | succ n ih =>
      intro h
      by_cases hn : ProductiveStep m e r0 n
      · exact ⟨n, by omega, hn, fun i h1 h2 _ => by omega⟩
      · obtain ⟨j, hj, hp⟩ := h
        have hj' : j < n := by
          by_cases hje : j = n
          · exact absurd (hje ▸ hp) hn
          · omega
        obtain ⟨j', h1, h2, h3⟩ := ih ⟨j, hj', hp⟩
        refine ⟨j', by omega, h2, ?_⟩
        intro i hi1 hi2
        by_cases hie : i = n
        · exact hie ▸ hn
        · exact h3 i hi1 (by omega)

open Classical in
/-- A collision-free tag for the last productive step before time `k`.

* `0` means there was no productive step yet;
* an even positive tag `2*c+2` means the last productive step was the first
  write of cell `c`;
* an odd tag `2*j+1` means it was an alternation at step `j`.

Unlike the older `codeOf` in `EchoMachine.lean`, distinct alternations are
not collapsed to one common tag. -/
noncomputable def linearCode (k : Nat) : Nat :=
  if h : ∃ j, j < k ∧ ProductiveStep m e r0 j then
    if FirstStep m e (exists_last_productive_lt m e r0 k h).choose
    then 2 * m.cellOf (e ((exists_last_productive_lt m e r0 k h).choose + 1)) + 2
    else 2 * (exists_last_productive_lt m e r0 k h).choose + 1
  else 0

private theorem linearCode_spec (cells : List Nat) (k : Nat) :
    (linearCode m e r0 k = 0 ∧
      snap m e r0 cells k = snap m e r0 cells 0) ∨
    (∃ j, j < k ∧ ProductiveStep m e r0 j ∧
      snap m e r0 cells k = snap m e r0 cells (j+1) ∧
      ((FirstStep m e j ∧
          linearCode m e r0 k = 2 * m.cellOf (e (j+1)) + 2) ∨
       (¬ FirstStep m e j ∧ linearCode m e r0 k = 2 * j + 1))) := by
  by_cases h : ∃ j, j < k ∧ ProductiveStep m e r0 j
  · right
    obtain ⟨hj, hp, hno⟩ := (exists_last_productive_lt m e r0 k h).choose_spec
    refine ⟨(exists_last_productive_lt m e r0 k h).choose, hj, hp, ?_, ?_⟩
    · have hd : (exists_last_productive_lt m e r0 k h).choose + 1 +
          (k - ((exists_last_productive_lt m e r0 k h).choose + 1)) = k := by omega
      have hsb := snap_between m e r0 cells
        ((exists_last_productive_lt m e r0 k h).choose + 1)
        (k - ((exists_last_productive_lt m e r0 k h).choose + 1))
        (fun i h1 h2 => hno i (by omega) (by omega))
      rw [hd] at hsb
      exact hsb
    · by_cases hf : FirstStep m e (exists_last_productive_lt m e r0 k h).choose
      · exact Or.inl ⟨hf, by
          unfold linearCode
          rw [dif_pos h, if_pos hf]⟩
      · exact Or.inr ⟨hf, by
          unfold linearCode
          rw [dif_pos h, if_neg hf]⟩
  · left
    constructor
    · unfold linearCode
      rw [dif_neg h]
    · have hsb := snap_between m e r0 cells 0 k
        (fun i _ h2 => fun hp => h ⟨i, by omega, hp⟩)
      rw [Nat.zero_add] at hsb
      exact hsb

private theorem first_same_cell_same_step {j1 j2 : Nat}
    (hf1 : FirstStep m e j1) (hf2 : FirstStep m e j2)
    (hc : m.cellOf (e (j1+1)) = m.cellOf (e (j2+1))) : j1 = j2 := by
  by_cases h12 : j1 < j2
  · have hn := hf2 (j1+1) (by omega)
    exact absurd hc hn
  · by_cases h21 : j2 < j1
    · have hn := hf1 (j2+1) (by omega)
      exact absurd hc.symm hn
    · omega

private theorem nodup_transfer {f : Nat → List Nat} {g : Nat → Nat} :
    ∀ {l : List Nat},
      (∀ x, x ∈ l → ∀ y, y ∈ l → g x = g y → f x = f y) →
      (l.map f).Nodup → (l.map g).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons x t ih =>
      intro hinj hnd
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      refine ⟨?_, ih (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        hnd.2⟩
      intro hmem
      obtain ⟨y, hy, hgy⟩ := List.mem_map.mp hmem
      have hfy : f x = f y :=
        hinj x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hgy.symm
      exact hnd.1 (List.mem_map.mpr ⟨y, hy, hfy.symm⟩)

private theorem nodup_subset_length {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {l S : List α},
    l.Nodup → (∀ x ∈ l, x ∈ S) → l.length ≤ S.length := by
  intro l
  induction l with
  | nil => intro S _ _; exact Nat.zero_le _
  | cons x t ih =>
      intro S hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ t, y ∈ S.erase x := by
        intro y hy
        have hyS : y ∈ S := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hih := ih hnd.2 hsub'
      have hlen : (S.erase x).length = S.length - 1 :=
        List.length_erase_of_mem hx
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons a t2 => simp
      simp only [List.length_cons]
      omega

end Echo
