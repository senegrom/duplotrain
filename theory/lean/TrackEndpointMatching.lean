import TrackFiniteAlternation

/-!
# Endpoint/matching semantics of a productive lazy-point pass

For a tongue state `u`, switch `C` selects one internal edge between its
stem and `selectedBranch u C`.

The central theorem `rawProductiveAt_is_endpoint_pivot` proves directly from
`Wiring`/`stepN` that every productive event counted by
`TrackFiniteAlternation` exits by the writer's stem and flips exactly the
writer's tongue.

This is the rigorous bridge from tongue-vector accounting to the
matching/endpoint walk. No periodicity, geometry, or finite-`N` enumeration
is used.
-/

namespace GeneralN

/-- Equality of restricted vectors gives equality at every represented
switch coordinate. -/
theorem restrict_eq_apply
    {N C : Nat} {u v : Tongues}
    (h : VectorCount.restrict N u = VectorCount.restrict N v)
    (hC : C < N) : u C = v C := by
  have hget := congrArg (fun xs : List Bool => xs[C]?) h
  simpa [VectorCount.restrict, List.getElem?_map,
    List.getElem?_range hC] using hget


/-- Any successful successor time exposes the corresponding one-step raw
transition. -/
theorem live_successor_configs
    {w : Wiring} {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next := by
  obtain ⟨next, hnext⟩ := Option.isSome_iff_exists.mp hlive
  have h := hnext
  rw [stepN_add] at h
  cases hcur : stepN w k start with
  | none => simp [hcur] at h
  | some cur => exact ⟨cur, next, rfl, hnext, by simpa [hcur, stepN] using h⟩

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
  obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
    live_successor_configs hprod.1
  have hparts := step_some_parts hstep
  have harrived : next.2 = (arrive cur.2 cur.1).2 := by
    simpa [arrivedTongues] using hparts.2
  have hchanged : next.2 (cur.1/3) ≠ cur.2 (cur.1/3) := by
    intro hsame
    apply hprod.2
    have hrestrict : VectorCount.restrict N next.2 =
        VectorCount.restrict N cur.2 := by
      unfold VectorCount.restrict
      apply List.map_congr_left
      intro j hj
      by_cases hjWriter : j = cur.1/3
      · simpa [hjWriter] using hsame
      · rw [harrived]
        exact arrive_preserves_other rfl hjWriter
    simpa [restrictedTonguesAt, tonguesAt, hcur, hnext] using hrestrict
  exact ⟨cur, next, hcur, hnext, hstep, hchanged⟩


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

end GeneralN
