import CanonicalPreTailGlobalBound
import GrayTailCount

/-!
# Canonical global bound including the absorbed tail

Let `k0` be the first certified lobe-pair absorption time.  Times before `k0`
are bounded by the canonical support-weight theorem; times at or after `k0`
have at most four complete register snapshots by `absorbed_snapshot_count`.
The two filtered lists partition the original list.

The resulting one-run finite-list bound is

    T^8 ≤ (2 * (slots.length + 1))^8 * 2^(7*N + 18).

Thus the Gray tail changes only the polynomial prefactor, not the strict
exponential base.
-/

namespace Echo

private theorem filter_lt_ge_length (cut : Nat) : ∀ xs : List Nat,
    (xs.filter (fun k => k < cut)).length +
      (xs.filter (fun k => cut ≤ k)).length = xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      by_cases h : x < cut
      · have hn : ¬ cut ≤ x := by omega
        simp [h, hn]
        omega
      · have hge : cut ≤ x := by omega
        simp [h, hge]
        omega

/-- Four snapshots satisfy the universal exponential factor used by the strict
bound, even for zero represented cells. -/
theorem four_snapshots_eighth_le (N : Nat) :
    blockCoreEighth 4 ≤ 2^(7*N+18) := by
  have hbase : blockCoreEighth 4 ≤ 2^18 := by decide
  exact Nat.le_trans hbase
    (Nat.pow_le_pow_right (by omega) (by omega))

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Canonical global strict-base bound with an absorbed Gray tail.** -/
theorem canonical_global_with_absorbed_tail_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup)
    {a b k0 : Nat}
    (hk0Hi : k0 ≤ globalHi)
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hAB : m.star (m.cellOf a) = m.cellOf b)
    (hstart : e k0 = a)
    (hreg : reg m e r0 k0 (m.cellOf b) = b ∨
      reg m e r0 k0 (m.cellOf b) = m.bar b)
    (hnoBefore : ∀ k, globalLo ≤ k → k < k0 →
      ¬ StandaloneFourTailFrom m e r0 k) :
    blockCoreEighth ks.length ≤
      blockCoreEighth (2 * (slots.length + 1)) *
        2^(7*cells.length+18) := by
  let X := 2^(7*cells.length+18)
  let pre := ks.filter (fun k => k < k0)
  let tail := ks.filter (fun k => k0 ≤ k)
  have hsplit : pre.length + tail.length = ks.length := by
    dsimp [pre, tail]
    exact filter_lt_ge_length k0 ks
  have hndPre : (pre.map (snap m e r0 cells)).Nodup := by
    dsimp [pre]
    exact map_filter_nodup (snap m e r0 cells)
      (fun k => k < k0) hnd
  have hndTail : (tail.map (snap m e r0 cells)).Nodup := by
    dsimp [tail]
    exact map_filter_nodup (snap m e r0 cells)
      (fun k => k0 ≤ k) hnd
  have htailTimes : ∀ k ∈ tail, k0 ≤ k := by
    intro k hk
    have hk' : k ∈ ks.filter (fun j => decide (k0 ≤ j)) := hk
    exact of_decide_eq_true (List.mem_filter.mp hk').2
  have htailCount : tail.length ≤ 4 :=
    absorbed_snapshot_count m e r0 hrun
      ha hb hAB hstart hreg cells tail htailTimes hndTail
  have htailEight : blockCoreEighth tail.length ≤ X := by
    have hm := blockCoreEighth_mono htailCount
    exact Nat.le_trans hm (by
      dsimp [X]
      exact four_snapshots_eighth_le cells.length)
  by_cases hpreNontrivial : globalLo < k0
  · let preHi := k0 - 1
    have hglobalPreHi : globalLo ≤ preHi := by
      dsimp [preHi]
      omega
    have hpreHiGlobal : preHi ≤ globalHi := by
      dsimp [preHi]
      omega
    let preFrame := restrictCompleteFiniteEpochFrame m e r0
      frame (Nat.le_refl globalLo) hpreHiGlobal
    have hpreTimes : ∀ k ∈ pre,
        globalLo ≤ k ∧ k ≤ preHi := by
      intro k hk
      have hk' : k ∈ ks.filter (fun j => decide (j < k0)) := hk
      have hkData := List.mem_filter.mp hk'
      have hklt : k < k0 := of_decide_eq_true hkData.2
      have hkGlobal := hks k hkData.1
      constructor
      · exact hkGlobal.1
      · dsimp [preHi]
        omega
    have hnoPre : StandaloneNoFourTailIn m e r0
        globalLo preHi := by
      intro k hkLo hkHi htail
      exact hnoBefore k hkLo (by
        dsimp [preHi] at hkHi
        omega) htail
    have hpreEight : blockCoreEighth pre.length ≤
        blockCoreEighth (slots.length + 1) * X := by
      dsimp [X]
      exact canonical_preTail_global_bound m e r0
        hrun hr0 globalLo preHi cells slots pre
        preFrame hpreTimes hnoPre hndPre
    have hone : 1 ≤ blockCoreEighth (slots.length + 1) := by
      have hm := blockCoreEighth_mono
        (show 1 ≤ slots.length + 1 by omega)
      simpa [blockCoreEighth, fourth] using hm
    have htailLarge : blockCoreEighth tail.length ≤
        blockCoreEighth (slots.length + 1) * X := by
      apply Nat.le_trans htailEight
      have hm := Nat.mul_le_mul_right X hone
      simpa [Nat.mul_comm] using hm
    have hagg := block_aggregate_eighth_bound
      [pre.length, tail.length]
      (blockCoreEighth (slots.length + 1) * X) (by
        intro s hs
        rcases List.mem_cons.mp hs with hs1 | hs2
        · rw [hs1]
          exact hpreEight
        · rcases List.mem_cons.mp hs2 with hs3 | hs4
          · rw [hs3]
            exact htailLarge
          · cases hs4)
    have hsum : [pre.length, tail.length].sum = ks.length := by
      simpa using hsplit
    rw [hsum] at hagg
    rw [show blockCoreEighth (2 * (slots.length + 1)) =
        blockCoreEighth 2 * blockCoreEighth (slots.length + 1) by
          exact blockCoreEighth_mul 2 (slots.length + 1)]
    simpa [Nat.mul_assoc] using hagg
  · have hk0Lo : k0 ≤ globalLo := by omega
    have hallTail : ∀ k ∈ ks, k0 ≤ k := by
      intro k hk
      exact Nat.le_trans hk0Lo (hks k hk).1
    have hallCount : ks.length ≤ 4 :=
      absorbed_snapshot_count m e r0 hrun
        ha hb hAB hstart hreg cells ks hallTail hnd
    have hallEight : blockCoreEighth ks.length ≤ X := by
      have hm := blockCoreEighth_mono hallCount
      exact Nat.le_trans hm (by
        dsimp [X]
        exact four_snapshots_eighth_le cells.length)
    apply Nat.le_trans hallEight
    have hone : 1 ≤ blockCoreEighth
        (2 * (slots.length + 1)) := by
      have hm := blockCoreEighth_mono
        (show 1 ≤ 2 * (slots.length + 1) by omega)
      simpa [blockCoreEighth, fourth] using hm
    have hmul := Nat.mul_le_mul_right X hone
    simpa [Nat.mul_comm, X] using hmul

end Echo
