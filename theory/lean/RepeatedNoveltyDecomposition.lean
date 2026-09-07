import TrackEndpointMatching
import ManufacturedPairNovelty

/-!
# Recovering vectors around the last productive write

A quiet interval preserves the restricted vector. Each productive step flips
its writer's bit, so undoing the last such flip recovers the vector immediately
before that write. These facts work over raw `Wiring` and `stepN`.
-/

namespace GeneralN


/-- An interval without productive steps preserves the restricted vector. -/
theorem restrictedTonguesAt_eq_of_quiet_interval
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hquiet : ∀ j, first ≤ j → j < first + span →
      ¬ RawProductiveAt w N start j) :
    restrictedTonguesAt w N start (first + span) =
      restrictedTonguesAt w N start first := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have hprefix : ∃ middle,
          stepN w (first + n) start = some middle :=
        stepN_prefix_some (by omega) hfinish
      obtain ⟨middle, hmiddle⟩ := hprefix
      have hprev := ih hmiddle
        (fun j hfirst hj => hquiet j hfirst (by omega))
      have hlive : (stepN w (first + n + 1) start).isSome := by
        have harith : first + (n+1) = first + n + 1 := by omega
        rw [← harith, hfinish]
        simp
      have hstep : restrictedTonguesAt w N start (first + n + 1) =
          restrictedTonguesAt w N start (first + n) :=
        Classical.byContradiction fun hne =>
          hquiet (first+n) (by omega) (by omega) ⟨hlive, hne⟩
      have harith : first + (n+1) = first+n+1 := by omega
      rw [harith]
      exact hstep.trans hprev

/-- Restriction commutes with flipping a represented coordinate, even when
the two full tongue functions may differ outside the first `N` switches. -/
theorem restrict_flipAt_congr
    {N C : Nat} {u v : Tongues}
    (h : VectorCount.restrict N u = VectorCount.restrict N v) :
    VectorCount.restrict N (flipAt u C) =
      VectorCount.restrict N (flipAt v C) := by
  unfold VectorCount.restrict
  apply List.map_congr_left
  intro j hj
  have hjN : j < N := List.mem_range.mp hj
  have huv : u j = v j := restrict_eq_apply h hjN
  unfold flipAt
  by_cases hjC : j = C
  · subst j
    simp [huv]
  · simp [hjC, huv]

/-- A productive raw step flips exactly the represented bit named by its
writer. -/
theorem rawProductiveAt_restricted_flip
    {w : Wiring} {N : Nat}
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    restrictedTonguesAt w N start (k+1) =
      VectorCount.restrict N
        (flipAt (tonguesAt w start k) (rawWriterAt w start k)) := by
  obtain ⟨cur, next, hcur, hnext, _hstep, _hexit, hflip⟩ :=
    rawProductiveAt_is_endpoint_pivot hprod
  simp [restrictedTonguesAt, tonguesAt, hcur, hnext, hflip]

/-- Undoing the last productive write recovers the vector just before it. -/
theorem last_productive_recovers
    {w : Wiring} {N t limit : Nat} {start finish : Nat × Tongues}
    (hfinish : stepN w limit start = some finish)
    (ht : t < limit) (hprod : RawProductiveAt w N start t)
    (hquiet : ∀ j, t < j → j < limit → ¬ RawProductiveAt w N start j) :
    VectorCount.restrict N (flipAt finish.2 (rawWriterAt w start t)) =
      restrictedTonguesAt w N start t := by
  have hsum : t + 1 + (limit - (t + 1)) = limit := by omega
  have hstable := restrictedTonguesAt_eq_of_quiet_interval
    (first := t + 1) (span := limit - (t + 1))
    (by simpa only [hsum] using hfinish)
    (fun j hj hbound => hquiet j (by omega) (by omega))
  have hend : VectorCount.restrict N finish.2 = restrictedTonguesAt w N start (t + 1) := by
    simpa [hsum, restrictedTonguesAt, tonguesAt, hfinish] using hstable
  simpa only [flipAt_flipAt, restrictedTonguesAt] using restrict_flipAt_congr
    (C := rawWriterAt w start t) (hend.trans (rawProductiveAt_restricted_flip hprod))

end GeneralN
