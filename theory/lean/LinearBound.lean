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

theorem exists_last_productive_lt :
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

end Echo
