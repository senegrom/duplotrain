import TokenState

/-!
# Per-cell heat is non-increasing

Tokens cannot migrate between cells: a productive arrival consumes a token in
the cell it writes and can only re-emit the previous register of that same
cell.  Consequently each cell's token count is individually non-increasing.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem nodup_filter_local (p : Nat → Bool) :
    ∀ {l : List Nat}, l.Nodup → (l.filter p).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x t ih =>
      intro h
      rw [List.nodup_cons] at h
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hm => h.1 ((List.mem_filter.mp hm).1), ih h.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih h.2

private theorem nodup_subset_length_local {l S : List Nat}
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

/-- **Local heat never grows.** -/
theorem cellTokens_nonincreasing
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) (hnd : slots.Nodup)
    (hslots : ∀ j, e j ∈ slots) (C k : Nat) :
    (cellTokens m e r0 slots C (k+1)).length
      ≤ (cellTokens m e r0 slots C k).length := by
  by_cases hp : ProductiveStep m e r0 k
  · by_cases hC : m.cellOf (e (k+1)) = C
    · have harr : e (k+1) ∈ cellTokens m e r0 slots C k := by
        rw [cellTokens, List.mem_filter]
        exact ⟨hslots (k+1), decide_eq_true
          ⟨arrival_token m e r0 hrun hr0 k hp, hC⟩⟩
      have hsub : ∀ s ∈ cellTokens m e r0 slots C (k+1),
          s ∈ reg m e r0 k C ::
            (cellTokens m e r0 slots C k).erase (e (k+1)) := by
        intro s hs
        rw [cellTokens, List.mem_filter] at hs
        obtain ⟨hT, hsC⟩ := of_decide_eq_true hs.2
        rcases token_step m e r0 hrun hr0 k s hT with hv | ⟨hTk, hne⟩
        · have hold : reg m e r0 k (m.cellOf (e (k+1))) = reg m e r0 k C := by
            rw [hC]
          rw [hv, hold]
          exact List.mem_cons_self
        · refine List.mem_cons_of_mem _ ?_
          rw [List.mem_erase_of_ne hne, cellTokens, List.mem_filter]
          exact ⟨hs.1, decide_eq_true ⟨hTk, hsC⟩⟩
      have hnd1 : (cellTokens m e r0 slots C (k+1)).Nodup :=
        nodup_filter_local _ hnd
      have hle := nodup_subset_length_local hnd1 hsub
      rw [List.length_cons, List.length_erase_of_mem harr] at hle
      have hpos : 0 < (cellTokens m e r0 slots C k).length := by
        cases ht : cellTokens m e r0 slots C k with
        | nil => rw [ht] at harr; cases harr
        | cons _ _ => simp
      omega
    · have hsub : ∀ s ∈ cellTokens m e r0 slots C (k+1),
          s ∈ cellTokens m e r0 slots C k := by
        intro s hs
        rw [cellTokens, List.mem_filter] at hs
        obtain ⟨hT, hsC⟩ := of_decide_eq_true hs.2
        rcases token_step m e r0 hrun hr0 k s hT with hv | ⟨hTk, _⟩
        · have hscell : m.cellOf s = m.cellOf (e (k+1)) := by
            rw [hv]
            exact reg_cell m e r0 hr0 k _
          exact absurd (hscell.symm.trans hsC) hC
        · rw [cellTokens, List.mem_filter]
          exact ⟨hs.1, decide_eq_true ⟨hTk, hsC⟩⟩
      exact nodup_subset_length_local
        (nodup_filter_local _ hnd) hsub
  · have heq : e (k+1) = reg m e r0 k (m.cellOf (e (k+1))) := by
      by_cases hq : e (k+1) = reg m e r0 k (m.cellOf (e (k+1)))
      · exact hq
      · exact absurd hq hp
    rw [cellTokens_stall m e r0 heq slots C]
    exact Nat.le_refl _

/-- Local token counts are antitone over arbitrary time intervals. -/
theorem cellTokens_antitone
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) (hnd : slots.Nodup)
    (hslots : ∀ j, e j ∈ slots)
    {i j C : Nat} (hij : i ≤ j) :
    (cellTokens m e r0 slots C j).length
      ≤ (cellTokens m e r0 slots C i).length := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j-i, by omega⟩
  clear hij
  induction d with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      have hstep := cellTokens_nonincreasing m e r0 hrun hr0 slots hnd
        hslots C (i+n)
      exact Nat.le_trans (by simpa [Nat.add_assoc] using hstep) ih

end Echo
