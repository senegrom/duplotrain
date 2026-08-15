import EndpointEpochExtraction
import SelfPivotStrictShrink
import BlockSparseBoundCore
import SupportMove
import ManufacturedPairNovelty

/-!
# Global amortization of train-curve growth and self epochs

This file records the unconditional part of the finite-curve amortization
argument directly over `Wiring` and `stepN`.

Every productive non-self pivot strictly enlarges the represented train
curve.  A productive self-pivot can only shrink it, while a nonproductive
step preserves its size.  Summing these one-step facts gives an exact global
potential inequality: the number of non-self productive pivots is bounded by
the final curve size plus the total amount ever discarded by self-pivots.
Since every represented curve has at most `3 * N` ports, this is

`non-self pivots <= 3 * N + total drop mass`.

The second result is the local dichotomy needed for a future global charge.
After any strict self-shrink, every finite live continuation is either a
self-only continuation (and hence exposes at most four tongue vectors), or
contains a later non-self pivot which strictly regrows the carrier.  The
strict shrink also supplies a concrete discarded port.

What is deliberately *not* asserted here is that the discarded ports chosen
at different shrink events are globally distinct.  The nested-restoration
library proves injectivity once the raw events have been compiled into one
strictly nested first-restoration family; constructing that family, or proving
that failure to construct it enters a permanent four-state tail, remains the
global bridge.
-/

namespace GeneralN

/-! ## Event lists and drop mass -/


theorem stepN_shift_eq
    {w : Wiring} {shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle) :
    stepN w d middle = stepN w (shift + d) start := by
  rw [stepN_add, hreach]
  rfl

theorem restrictedTonguesAt_shift_eq
    {w : Wiring} {N shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : ∃ finish, stepN w d middle = some finish) :
    restrictedTonguesAt w N middle d =
      restrictedTonguesAt w N start (shift + d) := by
  obtain ⟨finish, hfinish⟩ := hlive
  have hglobal : stepN w (shift + d) start = some finish := by
    rw [← stepN_shift_eq hreach]
    exact hfinish
  simp [restrictedTonguesAt, tonguesAt, hfinish, hglobal]


theorem RawProductiveAt.shift_iff
    {w : Wiring} {N shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : ∃ finish, stepN w (d + 1) middle = some finish) :
    RawProductiveAt w N middle d ↔
      RawProductiveAt w N start (shift + d) := by
  obtain ⟨finish, hfinish⟩ := hlive
  obtain ⟨current, hcurrent⟩ :=
    stepN_prefix_some (d := d) (K := d + 1)
      (by omega) hfinish
  have hnextLive : ∃ finish, stepN w (d + 1) middle = some finish :=
    ⟨finish, hfinish⟩
  have hcurrentLive : ∃ current, stepN w d middle = some current :=
    ⟨current, hcurrent⟩
  unfold RawProductiveAt
  have hnext : shift + (d + 1) = (shift + d) + 1 := by omega
  rw [restrictedTonguesAt_shift_eq hreach hnextLive,
    restrictedTonguesAt_shift_eq hreach hcurrentLive,
    stepN_shift_eq hreach, hnext]

theorem RawCurveSelfAt.shift_iff
    {w : Wiring} {shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : ∃ finish, stepN w d middle = some finish) :
    RawCurveSelfAt w middle d ↔
      RawCurveSelfAt w start (shift + d) := by
  obtain ⟨finish, hfinish⟩ := hlive
  have hglobal : stepN w (shift + d) start = some finish := by
    rw [← stepN_shift_eq hreach]
    exact hfinish
  unfold RawCurveSelfAt
  simp [hfinish, hglobal]

/-! ## Canonical self-epoch fibres -/


structure RawPermanentSelfTail
    (w : Wiring) (N : Nat) (start : Nat × Tongues) : Prop where
  live : ∀ k, (stepN w k start).isSome
  self : ∀ k, RawProductiveAt w N start k →
    RawCurveSelfAt w start k

/-- A permanent self tail exposes at most four distinct visible tongue
vectors, even when the observation times are unbounded and sparse. -/
theorem RawPermanentSelfTail.distinct_snapshots_le_four
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (T : RawPermanentSelfTail w N start)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 4 := by
  let K := maxRawTime times
  apply rawSelfEpoch_distinct_le_four
    (K := K) hN start
  · intro k _hk
    exact T.live k
  · intro k _hk hprod
    exact T.self k hprod
  · intro k hk
    exact le_maxRawTime_of_mem hk
  · exact hnd

end GeneralN
