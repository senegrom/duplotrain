import EchoConfiguration
import FiniteFrameSwitchCorollary
import BlockEpochAggregation

/-!
# Counting finite echo configurations

A register snapshot does not determine the next move unless the current entry
is also known.  The correct finite configuration is therefore

    (current entry, register snapshot).

Partition a duplicate-free configuration list by its current entry.  Inside
one entry fibre, duplicate-free configurations are exactly duplicate-free
register snapshots, so the unconditional strict-base snapshot theorem applies.
Summing over a finite entry universe costs only one further polynomial factor.
-/

namespace Echo

/-- Number of sampled times whose current entry is `q`. -/
def entryFibreSize (e : Nat → Nat) (q : Nat) (ks : List Nat) : Nat :=
  (ks.filter (fun k => e k = q)).length

/-- Sizes of all entry fibres indexed by a finite entry universe. -/
def entryFibreSizes (entries : List Nat)
    (e : Nat → Nat) (ks : List Nat) : List Nat :=
  entries.map (fun q => entryFibreSize e q ks)

private theorem entryFibreSize_cons
    (e : Nat → Nat) (q k : Nat) (ks : List Nat) :
    entryFibreSize e q (k :: ks) =
      (if e k = q then 1 else 0) + entryFibreSize e q ks := by
  by_cases h : e k = q <;>
    simp [entryFibreSize, h, Nat.add_comm]

private theorem entry_indicator_zero (v : Nat) :
    ∀ xs : List Nat,
      v ∉ xs →
      (xs.map (fun q => if v = q then 1 else 0)).sum = 0 := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons q rest ih =>
      intro hnot
      have hvq : v ≠ q := by
        intro h
        exact hnot (h ▸ List.mem_cons_self)
      have hvrest : v ∉ rest := by
        intro hv
        exact hnot (List.mem_cons_of_mem _ hv)
      simp [hvq, ih hvrest]

private theorem entry_indicator_one (v : Nat) :
    ∀ xs : List Nat,
      xs.Nodup → v ∈ xs →
      (xs.map (fun q => if v = q then 1 else 0)).sum = 1 := by
  intro xs
  induction xs with
  | nil =>
      intro _ hv
      cases hv
  | cons q rest ih =>
      intro hnd hv
      have hnd' := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hv with hvq | hvrest
      · subst q
        have hzero := entry_indicator_zero v rest hnd'.1
        simp [hzero]
      · have hvq : v ≠ q := by
          intro h
          apply hnd'.1
          exact h.symm ▸ hvrest
        have hone := ih hnd'.2 hvrest
        simp [hvq, hone]

private theorem sum_map_add_nat {α : Type}
    (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

/-- Entry fibres partition a sampled list exactly when the entry universe is
Nodup and covers every sampled entry. -/
theorem entryFibreSizes_sum
    (entries : List Nat) (e : Nat → Nat) :
    ∀ ks : List Nat,
      entries.Nodup →
      (∀ k ∈ ks, e k ∈ entries) →
      (entryFibreSizes entries e ks).sum = ks.length := by
  intro ks
  induction ks with
  | nil =>
      intro _ _
      simp [entryFibreSizes, entryFibreSize]
  | cons k rest ih =>
      intro hnd hcover
      have hk : e k ∈ entries := hcover k List.mem_cons_self
      have hrest : ∀ j ∈ rest, e j ∈ entries := by
        intro j hj
        exact hcover j (List.mem_cons_of_mem _ hj)
      have hpoint :
          entryFibreSizes entries e (k :: rest) =
            entries.map (fun q =>
              (if e k = q then 1 else 0) +
                entryFibreSize e q rest) := by
        unfold entryFibreSizes
        apply List.map_congr_left
        intro q _
        exact entryFibreSize_cons e q k rest
      rw [hpoint, sum_map_add_nat]
      rw [entry_indicator_one (e k) entries hnd hk,
        ih hnd hrest]
      simp

/-- In a fixed-key fibre, duplicate-free `(key,value)` pairs give
duplicate-free values. -/
theorem filtered_value_nodup_of_pair_nodup
    {α β γ : Type} [DecidableEq γ]
    (xs : List α) (key : α → γ) (value : α → β) (q : γ)
    (hnd : (xs.map (fun x => (key x, value x))).Nodup) :
    ((xs.filter (fun x => key x = q)).map value).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hnd' := List.nodup_cons.mp hnd
      by_cases hx : key x = q
      · have hfilter :
            (x :: rest).filter (fun y => key y = q) =
              x :: rest.filter (fun y => key y = q) := by
          simp [hx]
        rw [hfilter, List.map_cons, List.nodup_cons]
        constructor
        · intro hm
          obtain ⟨y, hy, hval⟩ := List.mem_map.mp hm
          have hyFilter := List.mem_filter.mp hy
          have hyKey : key y = q :=
            of_decide_eq_true hyFilter.2
          apply hnd'.1
          apply List.mem_map.mpr
          refine ⟨y, hyFilter.1, ?_⟩
          apply Prod.ext
          · exact hyKey.trans hx.symm
          · exact hval.symm
        · exact ih hnd'.2
      · have hfilter :
            (x :: rest).filter (fun y => key y = q) =
              rest.filter (fun y => key y = q) := by
          simp [hx]
        rw [hfilter]
        exact ih hnd'.2

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A fixed-entry fibre of a duplicate-free finite configuration list has
duplicate-free register snapshots. -/
theorem entryFibre_snap_nodup
    (cells ks : List Nat) (q : Nat)
    (hcfg : (ks.map (configSnap m e r0 cells)).Nodup) :
    (((ks.filter (fun k => e k = q)).map
      (snap m e r0 cells))).Nodup := by
  have hpair :
      (ks.map (fun k =>
        (e k, snap m e r0 cells k))).Nodup := by
    simpa [configSnap] using hcfg
  exact filtered_value_nodup_of_pair_nodup ks e
    (snap m e r0 cells) q hpair

/-- **Finite configuration bound.**  Distinct configurations cost one
strict-bound snapshot fibre per possible current entry. -/
theorem finiteFrame_config_strict_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots entries ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2 * N)
    (hentriesNodup : entries.Nodup)
    (hentryCover : ∀ k ∈ ks, e k ∈ entries)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hcfg : (ks.map (configSnap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤
      blockCoreEighth entries.length *
        (blockCoreEighth (4*N + 2) * 2^(7*N+18)) := by
  let sizes := entryFibreSizes entries e ks
  have hsum : sizes.sum = ks.length := by
    dsimp [sizes]
    exact entryFibreSizes_sum entries e ks
      hentriesNodup hentryCover
  have heach : ∀ s ∈ sizes,
      blockCoreEighth s ≤
        blockCoreEighth (4*N + 2) * 2^(7*N+18) := by
    intro s hs
    dsimp [sizes, entryFibreSizes] at hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    let fibre := ks.filter (fun k => e k = q)
    have htime : ∀ k ∈ fibre,
        globalLo ≤ k ∧ k ≤ globalHi := by
      intro k hk
      have hkFilter : k ∈ ks.filter (fun j => e j = q) := by
        simpa only [fibre] using hk
      exact hks k (List.mem_filter.mp hkFilter).1
    have hndSnap :
        (fibre.map (snap m e r0 cells)).Nodup := by
      dsimp [fibre]
      exact entryFibre_snap_nodup m e r0 cells ks q hcfg
    have hbound := finiteFrame_atMost_N_strict_bound
      m e r0 hrun hr0 N globalLo globalHi
      cells slots fibre frame hcells hslots htime hndSnap
    simpa [entryFibreSize, fibre] using hbound
  have hagg := block_aggregate_eighth_bound sizes
    (blockCoreEighth (4*N + 2) * 2^(7*N+18)) heach
  have hlen : sizes.length = entries.length := by
    simp [sizes, entryFibreSizes]
  rw [hsum, hlen] at hagg
  exact hagg

/-- With at most `2*N` physical entries, the finite configuration count is
still strict-base exponential, with only a quadratic polynomial factor. -/
theorem finiteFrame_config_atMost_N_strict_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots entries ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2 * N)
    (hentriesNodup : entries.Nodup)
    (hentriesLength : entries.length ≤ 2 * N)
    (hentryCover : ∀ k ∈ ks, e k ∈ entries)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hcfg : (ks.map (configSnap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤
      blockCoreEighth (2*N) *
        (blockCoreEighth (4*N + 2) * 2^(7*N+18)) := by
  have hbase := finiteFrame_config_strict_bound
    m e r0 hrun hr0 N globalLo globalHi
    cells slots entries ks frame hcells hslots
    hentriesNodup hentryCover hks hcfg
  have hfactor := blockCoreEighth_mono hentriesLength
  exact Nat.le_trans hbase
    (Nat.mul_le_mul_right
      (blockCoreEighth (4*N + 2) * 2^(7*N+18)) hfactor)

end Echo
