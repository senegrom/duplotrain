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

private theorem slotCode_eq_snap_eq (cells : List Nat)
    (hreplay : ProductiveSlotReplay m e r0 cells)
    {k1 k2 : Nat} (hc : slotCode m e r0 k1 = slotCode m e r0 k2) :
    snap m e r0 cells k1 = snap m e r0 cells k2 := by
  rcases slotCode_spec m e r0 cells k1 with ⟨c1, s1⟩ |
      ⟨j1, _, hp1, c1, s1⟩
  · rcases slotCode_spec m e r0 cells k2 with ⟨c2, s2⟩ |
        ⟨j2, _, hp2, c2, s2⟩
    · rw [s1, s2]
    · rw [c1, c2] at hc
      omega
  · rcases slotCode_spec m e r0 cells k2 with ⟨c2, s2⟩ |
        ⟨j2, _, hp2, c2, s2⟩
    · rw [c1, c2] at hc
      omega
    · have he : e (j1+1) = e (j2+1) := by
        rw [c1, c2] at hc
        omega
      rw [s1, s2]
      exact hreplay j1 j2 hp1 hp2 he

private theorem nodup_transfer_slot
    {f : Nat → List Nat} {g : Nat → Nat} {l : List Nat}
    (hinj : ∀ x, x ∈ l → ∀ y, y ∈ l → g x = g y → f x = f y)
    (hnd : (l.map f).Nodup) : (l.map g).Nodup := by
  induction l with
  | nil => simp
  | cons x t ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hm
        obtain ⟨y, hy, hgy⟩ := List.mem_map.mp hm
        have hfy := hinj x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hgy.symm
        exact hnd.1 (List.mem_map.mpr ⟨y, hy, hfy.symm⟩)
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
      have hlen : (S.erase x).length = S.length - 1 :=
        List.length_erase_of_mem hx
      rw [hlen] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- **Slot-linear bound.** Under the single replay lemma, any pairwise-
distinct family of snapshots whose productive arrivals lie in `slots` has
size at most `slots.length + 1`. -/
theorem slot_linear_bound
    (cells slots : List Nat) (hslots : ∀ k, e k ∈ slots)
    (hreplay : ProductiveSlotReplay m e r0 cells)
    (ks : List Nat)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ slots.length + 1 := by
  have hcodes : (ks.map (slotCode m e r0)).Nodup :=
    nodup_transfer_slot
      (fun x _ y _ hc => slotCode_eq_snap_eq m e r0 cells hreplay hc)
      hnd
  have hmem : ∀ v ∈ ks.map (slotCode m e r0),
      v ∈ 0 :: slots.map (fun s => s + 1) := by
    intro v hv
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
    rcases slotCode_spec m e r0 cells k with ⟨hc0, _⟩ |
        ⟨j, _, _, hc, _⟩
    · rw [hc0]; exact List.mem_cons_self
    · rw [hc]
      exact List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨e (j+1), hslots (j+1), rfl⟩)
  have hle := nodup_subset_length_nat hcodes hmem
  rw [List.length_map] at hle
  simp only [List.length_cons, List.length_map] at hle
  exact hle

end Echo
