import TrackFiniteAlternation
import ManufacturedPairNovelty

/-!
# Recovering vectors around the last productive write

A productive step exits by its writer's stem and flips exactly the writer's
tongue, and a quiet interval preserves the restricted vector. Undoing the last
productive flip therefore recovers the vector immediately before that write.
These facts work over raw `Wiring` and `stepN`.
-/

namespace GeneralN

/-- Restricted-vector productivity is a genuine change of the entered
switch's own tongue. -/
theorem rawProductiveAt_changes_writer
    {w : Wiring} {N : Nat}
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next ∧
      next.2 (cur.1/3) ≠ cur.2 (cur.1/3) := by
  obtain ⟨cur, next, hcur, hnext, hstep⟩ := live_successor_configs hprod.1
  refine ⟨cur, next, hcur, hnext, hstep, ?_⟩
  intro hsame
  have heq : next.2 = cur.2 := by
    funext j
    by_cases hj : j = cur.1 / 3
    · simpa [hj] using hsame
    · rw [(step_some_parts hstep).2]
      exact arrive_preserves_other rfl hj
  exact hprod.2 (by simp [restrictedTonguesAt, tonguesAt, hcur, hnext, heq])

theorem rawProductiveAt_is_endpoint_pivot
    {w : Wiring} {N : Nat}
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next ∧
      exitPort cur = 3 * rawWriterAt w start k ∧
      next.2 = flipAt cur.2 (rawWriterAt w start k) := by
  obtain ⟨cur, next, hcur, hnext, hstep, hchanged⟩ :=
    rawProductiveAt_changes_writer hprod
  have hparts := step_some_parts hstep
  have harrive : arrive cur.2 cur.1 = (exitPort cur, next.2) := by
    apply Prod.ext
    · rfl
    · exact hparts.2.symm
  obtain ⟨_hbranch, hexit, _hpin⟩ :=
    changed_arrival_is_trailing harrive hchanged
  refine ⟨cur, next, hcur, hnext, hstep, ?_, ?_⟩
  · simpa [rawWriterAt, rawEntryAt, hcur] using hexit
  · simpa [rawWriterAt, rawEntryAt, hcur] using changed_arrival_eq_flipAt harrive hchanged

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
      rw [← Nat.add_assoc] at hfinish
      obtain ⟨middle, hmiddle⟩ := stepN_prefix_some (d := first + n) (by omega) hfinish
      have hstep : restrictedTonguesAt w N start (first + n + 1) =
          restrictedTonguesAt w N start (first + n) := by
        apply Classical.byContradiction
        intro hne
        exact hquiet (first + n) (by omega) (by omega) ⟨by rw [hfinish]; rfl, hne⟩
      exact hstep.trans (ih hmiddle (fun j hj hbound => hquiet j hj (by omega)))

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
  obtain ⟨cur, next, hcur, hnext, _, _, hflip⟩ := rawProductiveAt_is_endpoint_pivot hprod
  have hend : VectorCount.restrict N finish.2 =
      VectorCount.restrict N (flipAt (tonguesAt w start t) (rawWriterAt w start t)) := by
    simpa [hsum, restrictedTonguesAt, tonguesAt, hfinish, hcur, hnext, hflip] using hstable
  unfold restrictedTonguesAt VectorCount.restrict at hend ⊢
  apply List.map_congr_left
  intro j hj
  have hj' := congrArg (fun xs : List Bool => xs[j]?) hend
  simp [List.getElem?_map, List.getElem?_range (List.mem_range.mp hj)] at hj'
  simp only [flipAt] at hj' ⊢
  split <;> simp_all

end GeneralN
