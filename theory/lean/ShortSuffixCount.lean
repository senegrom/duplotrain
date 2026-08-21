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
    {α : Type} (f : Nat → α) :
    ∀ {times : List Nat}, (times.map f).Nodup → times.Nodup := by
  intro times hnd
  exact List.Pairwise.of_map f
    (fun _ _ hne hEq => hne (congrArg f hEq)) hnd

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

end GeneralN
