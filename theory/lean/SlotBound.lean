import AlternationBound

/-!
# Slot accounting

A sharper accounting than `LinearBound`: tag each snapshot by the arrival slot
of its last productive transition. If a productive slot cannot recur without
replaying the snapshot produced by its previous productive occurrence, then
pairwise-distinct snapshots inject into `{initial} ∪ slots`, giving the linear
bound `#slots + 1`.

The only non-bookkeeping hypothesis below is `ProductiveSlotReplay`. It is the
precise pointer-reversal / nesting lemma left to prove.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem exists_last_prod_lt :
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
noncomputable def slotCode (k : Nat) : Nat :=
  if h : ∃ j, j < k ∧ ProductiveStep m e r0 j then
    e ((exists_last_prod_lt m e r0 k h).choose + 1) + 1
  else 0

private theorem slotCode_spec (cells : List Nat) (k : Nat) :
    (slotCode m e r0 k = 0 ∧
      snap m e r0 cells k = snap m e r0 cells 0) ∨
    (∃ j, j < k ∧ ProductiveStep m e r0 j ∧
      slotCode m e r0 k = e (j+1) + 1 ∧
      snap m e r0 cells k = snap m e r0 cells (j+1)) := by
  by_cases h : ∃ j, j < k ∧ ProductiveStep m e r0 j
  · right
    obtain ⟨hj, hp, hno⟩ := (exists_last_prod_lt m e r0 k h).choose_spec
    refine ⟨(exists_last_prod_lt m e r0 k h).choose, hj, hp, ?_, ?_⟩
    · unfold slotCode
      rw [dif_pos h]
    · have hd : (exists_last_prod_lt m e r0 k h).choose + 1 +
          (k - ((exists_last_prod_lt m e r0 k h).choose + 1)) = k := by omega
      have hsb := snap_between m e r0 cells
        ((exists_last_prod_lt m e r0 k h).choose + 1)
        (k - ((exists_last_prod_lt m e r0 k h).choose + 1))
        (fun i h1 h2 => hno i (by omega) (by omega))
      rw [hd] at hsb
      exact hsb
  · left
    constructor
    · unfold slotCode; rw [dif_neg h]
    · have hsb := snap_between m e r0 cells 0 k
        (fun i _ h2 => fun hp => h ⟨i, by omega, hp⟩)
      rw [Nat.zero_add] at hsb
      exact hsb

/-- The structural replay property needed by slot accounting. -/
def ProductiveSlotReplay (cells : List Nat) : Prop :=
  ∀ i j, ProductiveStep m e r0 i → ProductiveStep m e r0 j →
    e (i+1) = e (j+1) →
    snap m e r0 cells (i+1) = snap m e r0 cells (j+1)

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
      have hlen : (S.erase x).length = S.length - 1 :=
        List.length_erase_of_mem hx
      rw [hlen] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

end Echo
