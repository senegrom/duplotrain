import BoundaryOverlapTailCount

/-!
# Raw counting for a history-covered journey and a short suffix

These lemmas deliberately expose every semantic hypothesis.  The first says
that once a raw `stepN` run is dead at a horizon, all live sample times lie
strictly before that horizon.  The remaining lemmas compose an explicitly
history-covered prefix with such a suffix.  If the boundary vector is already
in the prefix history, it is counted only once.

No manufactured-reflector certificate is hidden in this file: callers supply
the reachability equation, the pointwise history cover, and (when available)
the boundary-membership proof directly.
-/

namespace GeneralN

/-- Pairwise-distinct sampled values force the sample times themselves to be
pairwise distinct. -/
theorem sample_times_nodup_of_map_nodup
    {α : Type} [BEq α] [LawfulBEq α]
    (f : Nat → α) :
    ∀ {times : List Nat}, (times.map f).Nodup → times.Nodup := by
  intro times
  induction times with
  | nil => intro _; simp
  | cons k rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hk
        apply hnd.1
        exact List.mem_map.mpr ⟨k, hk, rfl⟩
      · exact ih hnd.2

/-- Death is permanent: if a partial run is off-track at `L`, it is off-track
at every later time. -/
theorem stepN_none_of_none_at_le
    {w : Wiring} {start : Nat × Tongues} {L k : Nat}
    (hdead : stepN w L start = none) (hLk : L ≤ k) :
    stepN w k start = none := by
  have hk : k = L + (k - L) := by omega
  rw [hk, stepN_add, hdead]
  simp

/-- If the train is off-track at time `L`, a list of live sample times whose
restricted tongue vectors are pairwise distinct has length at most `L`.

The conclusion is positional, not dynamical: every live sample lies in the
finite interval `[0,L)`, and vector-nodup implies time-nodup. -/
theorem dead_horizon_live_distinct_le
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    (hdead : stepN w L start = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ L := by
  have htimesNodup : times.Nodup :=
    sample_times_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  have hlt : ∀ k ∈ times, k < L := by
    intro k hk
    by_cases hsmall : k < L
    · exact hsmall
    · have hLk : L ≤ k := by omega
      have hnone := stepN_none_of_none_at_le hdead hLk
      have hkLive := hlive k hk
      simp [hnone] at hkLive
  exact nodup_nat_lt_length htimesNodup hlt

/-- A history-covered journey followed by a suffix dead at `horizon` exposes
at most `history.length + horizon` distinct restricted tongue vectors.

This version does not assume that the journey's endpoint vector was already
listed in `history`; it adjoins that boundary explicitly. -/
theorem history_covered_journey_then_dead_suffix_distinct_le
    {w : Wiring} {N lead horizon : Nat}
    {start endpoint : Nat × Tongues}
    (hreach : stepN w lead start = some endpoint)
    (history : List (List Bool))
    (hprefixCover : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ history)
    (hdead : stepN w horizon endpoint = none)
    (hhorizon : 0 < horizon)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ history.length + horizon := by
  let boundary := VectorCount.restrict N endpoint.2
  let augmented := boundary :: history
  have hprefixAugmented : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ augmented := by
    intro d hd
    exact List.mem_cons_of_mem _ (hprefixCover d hd)
  have hboundary : VectorCount.restrict N endpoint.2 ∈ augmented := by
    simp [augmented, boundary]
  have htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes, (stepN w k endpoint).isSome) →
      (tailTimes.map (restrictedTonguesAt w N endpoint)).Nodup →
      tailTimes.length ≤ horizon := by
    intro tailTimes htailLive htailNodup
    exact dead_horizon_live_distinct_le hdead tailTimes
      htailLive htailNodup
  have hcount := boundary_history_then_direct_tail_distinct_le
    hreach augmented hprefixAugmented hboundary htail hhorizon
      times hlive hnd
  simp only [augmented, List.length_cons] at hcount
  omega

/-- Boundary-aware form of the preceding theorem.  When the endpoint vector
already belongs to `history`, the common boundary is counted only once. -/
theorem boundary_history_covered_journey_then_dead_suffix_distinct_le
    {w : Wiring} {N lead horizon : Nat}
    {start endpoint : Nat × Tongues}
    (hreach : stepN w lead start = some endpoint)
    (history : List (List Bool))
    (hprefixCover : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ history)
    (hboundary : VectorCount.restrict N endpoint.2 ∈ history)
    (hdead : stepN w horizon endpoint = none)
    (hhorizon : 0 < horizon)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ history.length + horizon - 1 := by
  have htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes, (stepN w k endpoint).isSome) →
      (tailTimes.map (restrictedTonguesAt w N endpoint)).Nodup →
      tailTimes.length ≤ horizon := by
    intro tailTimes htailLive htailNodup
    exact dead_horizon_live_distinct_le hdead tailTimes
      htailLive htailNodup
  exact boundary_history_then_direct_tail_distinct_le
    hreach history hprefixCover hboundary htail hhorizon
      times hlive hnd

/-- `N+2` history vectors followed by death at `N+1` steps give the raw
two-stage bound `2*N+3`, without assuming boundary overlap. -/
theorem short_suffix_after_history_distinct_le_two_mul_add_three
    {w : Wiring} {N lead : Nat}
    {start endpoint : Nat × Tongues}
    (hreach : stepN w lead start = some endpoint)
    (history : List (List Bool))
    (hprefixCover : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ history)
    (hhistory : history.length ≤ N + 2)
    (hdead : stepN w (N + 1) endpoint = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 3 := by
  have hcount := history_covered_journey_then_dead_suffix_distinct_le
    hreach history hprefixCover hdead (by omega) times hlive hnd
  omega

/-- With the journey endpoint already represented in its `N+2` history, the
same short suffix costs one fewer vector: at most `2*N+2` in total. -/
theorem short_suffix_after_boundary_history_distinct_le_two_mul_add_two
    {w : Wiring} {N lead : Nat}
    {start endpoint : Nat × Tongues}
    (hreach : stepN w lead start = some endpoint)
    (history : List (List Bool))
    (hprefixCover : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ history)
    (hboundary : VectorCount.restrict N endpoint.2 ∈ history)
    (hhistory : history.length ≤ N + 2)
    (hdead : stepN w (N + 1) endpoint = none)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 2 * N + 2 := by
  have hcount :=
    boundary_history_covered_journey_then_dead_suffix_distinct_le
      hreach history hprefixCover hboundary hdead (by omega)
        times hlive hnd
  omega

end GeneralN
