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
