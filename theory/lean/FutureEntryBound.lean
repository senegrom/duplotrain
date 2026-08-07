import PairBound

/-!
# The future entry alphabet

The pedigree theorem in `EchoMachine.lean` says that after a base time `K`,
every register value is either its value at `K` or a token alive at `K`.
Taking `bar`, every future train entry therefore belongs to a fixed alphabet:

* the entry at the base time;
* one `bar` of a base register for each cell;
* one `bar` for each live token.

Since there are at most as many tokens as cells, this alphabet has size at
most `2 * #cells + 1`.  This is unconditional and collapses the apparently
unbounded slot universe to a linear one.

Consequently, any phase in which consecutive entry pairs do not repeat has
quadratic length.  The remaining dynamical problem for a polynomial state
bound is now a bounded-multiplicity theorem for consecutive pairs.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A fixed alphabet containing every entry at or after time `K`. -/
def futureEntryAlphabet (cells slots : List Nat) (K : Nat) : List Nat :=
  e K ::
    (cells.map (fun C => m.bar (reg m e r0 K C)) ++
      (tokenEnds m e r0 slots K).map m.bar)

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

private theorem nodup_subset_length_pair {l S : List (List Nat)}
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

private theorem pairRect_length (xs ys : List Nat) :
    (xs.flatMap (fun a => ys.map (fun b => [a, b]))).length
      = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons _ t ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

private theorem pairUniverse_length_local (xs : List Nat) :
    (pairUniverse xs).length = xs.length * xs.length := by
  exact pairRect_length xs xs

/-- The exact length of the future-entry alphabet (duplicates are harmless). -/
theorem futureEntryAlphabet_length (cells slots : List Nat) (K : Nat) :
    (futureEntryAlphabet m e r0 cells slots K).length =
      cells.length + (tokenEnds m e r0 slots K).length + 1 := by
  unfold futureEntryAlphabet
  simp only [List.length_cons, List.length_append, List.length_map]

/-- Every arrival after the base time belongs to the fixed future alphabet. -/
theorem future_arrival_mem
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    {K j : Nat} (hKj : K ≤ j) :
    e (j+1) ∈ futureEntryAlphabet m e r0 cells slots K := by
  let C := m.star (m.cellOf (e j))
  have hstep : e (j+1) = m.bar (reg m e r0 j C) := by
    simpa [C] using hrun j
  rcases future_register_le m e r0 hrun hr0 (K := K) (C := C) hKj with
      hbase | htok
  · rw [hstep, hbase]
    unfold futureEntryAlphabet
    exact List.mem_cons_of_mem _
      (List.mem_append_left _
        (List.mem_map.mpr ⟨C, hcells j, rfl⟩))
  · rw [hstep]
    unfold futureEntryAlphabet
    refine List.mem_cons_of_mem _ (List.mem_append_right _ ?_)
    apply List.mem_map.mpr
    refine ⟨reg m e r0 j C, ?_, rfl⟩
    rw [tokenEnds, List.mem_filter]
    exact ⟨hregslots j C, decide_eq_true htok⟩

/-- Every entry at or after the base time belongs to the fixed alphabet. -/
theorem future_entry_mem
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    {K j : Nat} (hKj : K ≤ j) :
    e j ∈ futureEntryAlphabet m e r0 cells slots K := by
  by_cases hj : j = K
  · subst j
    exact List.mem_cons_self
  · obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
    exact future_arrival_mem m e r0 hrun hr0 cells slots hcells hregslots
      (K := K) (j := q) (by omega)

/-- Duplicate-free future entries are linearly bounded by base registers plus
live tokens. -/
theorem future_entries_count
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    (K : Nat) (ks : List Nat) (hks : ∀ k ∈ ks, K ≤ k)
    (hnd : (ks.map e).Nodup) :
    ks.length ≤ cells.length + (tokenEnds m e r0 slots K).length + 1 := by
  have hsub : ∀ v ∈ ks.map e,
      v ∈ futureEntryAlphabet m e r0 cells slots K := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    exact future_entry_mem m e r0 hrun hr0 cells slots hcells hregslots
      (hks k hk)
  have hle := nodup_subset_length_nat hnd hsub
  rw [List.length_map, futureEntryAlphabet_length] at hle
  exact hle

/-- Using the token ceiling, at most `2 * #cells + 1` different entries can
occur after any chosen base time. -/
theorem future_entries_le_two_cells
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hslotsnd : slots.Nodup)
    (hallcells : ∀ s, m.cellOf s ∈ cells)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    (K : Nat) (ks : List Nat) (hks : ∀ k ∈ ks, K ≤ k)
    (hnd : (ks.map e).Nodup) :
    ks.length ≤ 2 * cells.length + 1 := by
  have hcount := future_entries_count m e r0 hrun hr0 cells slots hcells
    hregslots K ks hks hnd
  have htok := tokens_le_cells m e r0 slots hslotsnd cells hallcells K
  omega

/-- If consecutive pairs in a future phase are duplicate-free, the phase has
quadratic length in the future alphabet. -/
theorem future_pair_nodup_bound
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    (K : Nat) (ks : List Nat) (hks : ∀ k ∈ ks, K ≤ k)
    (hnd : (ks.map (pairTag e)).Nodup) :
    ks.length ≤
      (futureEntryAlphabet m e r0 cells slots K).length *
      (futureEntryAlphabet m e r0 cells slots K).length := by
  let A := futureEntryAlphabet m e r0 cells slots K
  have hsub : ∀ p ∈ ks.map (pairTag e), p ∈ pairUniverse A := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    unfold pairTag pairUniverse
    apply List.mem_flatMap.mpr
    refine ⟨e k, future_entry_mem m e r0 hrun hr0 cells slots hcells
      hregslots (hks k hk), ?_⟩
    exact List.mem_map.mpr ⟨e (k+1),
      future_entry_mem m e r0 hrun hr0 cells slots hcells hregslots
        (by have := hks k hk; omega), rfl⟩
  have hle := nodup_subset_length_pair hnd hsub
  rw [List.length_map, pairUniverse_length_local] at hle
  exact hle

/-- With the token ceiling, a pair-duplicate-free future phase has length at
most `(2 * #cells + 1)^2`. -/
theorem future_pair_nodup_le_cells_sq
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hslotsnd : slots.Nodup)
    (hallcells : ∀ s, m.cellOf s ∈ cells)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    (K : Nat) (ks : List Nat) (hks : ∀ k ∈ ks, K ≤ k)
    (hnd : (ks.map (pairTag e)).Nodup) :
    ks.length ≤ (2 * cells.length + 1) * (2 * cells.length + 1) := by
  have hp := future_pair_nodup_bound m e r0 hrun hr0 cells slots hcells
    hregslots K ks hks hnd
  have htok := tokens_le_cells m e r0 slots hslotsnd cells hallcells K
  have hA : (futureEntryAlphabet m e r0 cells slots K).length
      ≤ 2 * cells.length + 1 := by
    rw [futureEntryAlphabet_length]
    omega
  exact Nat.le_trans hp (Nat.mul_le_mul hA hA)

end Echo
