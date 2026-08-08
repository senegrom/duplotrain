import BlockEpochAggregation

/-!
# Global numerical form, including the absorbing tail

At most `N+1` pre-tail support epochs plus one Gray-square tail of size at most
four give

    total^8 ≤ (N+2)^8 * 2^(7N+18).

All remaining work is structural: produce the epoch partition and instantiate
the fixed-epoch theorem on each block.
-/

namespace Echo

/-- A tail of at most four states fits the uniform strict-epoch envelope. -/
theorem four_tail_eighth_bound (N t : Nat) (ht : t ≤ 4) :
    blockCoreEighth t ≤ 2^(7*N+18) := by
  have hmono := blockCoreEighth_mono ht
  have hfour : blockCoreEighth 4 ≤ 2^18 := by decide
  have hexp : 18 ≤ 7*N+18 := by omega
  exact Nat.le_trans hmono
    (Nat.le_trans hfour
      (Nat.pow_le_pow_right (by omega) hexp))

/-- Append the absorbing tail to a pre-tail epoch-size list. -/
theorem global_bound_with_four_tail
    (N tail : Nat) (sizes : List Nat)
    (hlen : sizes.length ≤ N+1)
    (hepoch : ∀ s ∈ sizes,
      blockCoreEighth s ≤ 2^(7*N+18))
    (htail : tail ≤ 4) :
    blockCoreEighth (sizes.sum + tail) ≤
      blockCoreEighth (N+2) * 2^(7*N+18) := by
  let pieces := sizes ++ [tail]
  have hpLen : pieces.length ≤ N+2 := by
    simp [pieces]
    omega
  have hpBound : ∀ s ∈ pieces,
      blockCoreEighth s ≤ 2^(7*N+18) := by
    intro s hs
    simp only [pieces, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    rcases hs with hs | hs
    · exact hepoch s hs
    · rw [hs]
      exact four_tail_eighth_bound N tail htail
  have hagg := block_aggregate_eighth_bound_of_length
    pieces (N+2) (2^(7*N+18)) hpLen hpBound
  have hsum : pieces.sum = sizes.sum + tail := by
    simp [pieces]
  simpa [hsum] using hagg

end Echo
