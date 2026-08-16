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

/-- Branch currently joined to the stem by the selected internal edge. -/
def selectedBranch (u : Tongues) (C : Nat) : Nat :=
  branchPort C (u C)


private theorem productive_step_configs
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next := by
  cases hnext : stepN w (k+1) start with
  | none =>
      have hlive := hprod.1
      simp [hnext] at hlive
  | some next =>
      have hsplit := stepN_add w k 1 start
      rw [hnext] at hsplit
      cases hcur : stepN w k start with
      | none => simp [hcur] at hsplit
      | some cur =>
          rw [hcur] at hsplit
          have hone : stepN w 1 cur = some next := by
            simpa using hsplit.symm
          have hstep : step w cur = some next := by
            simpa [stepN] using hone
          exact ⟨cur, next, rfl, rfl, hstep⟩

/-- Any successful successor time exposes the corresponding one-step raw
transition. -/
theorem live_successor_configs
    {w : Wiring} {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k+1) start).isSome) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next := by
  cases hnext : stepN w (k+1) start with
  | none => simp [hnext] at hlive
  | some next =>
      have hsplit := stepN_add w k 1 start
      rw [hnext] at hsplit
      cases hcur : stepN w k start with
      | none => simp [hcur] at hsplit
      | some cur =>
          rw [hcur] at hsplit
          have hone : stepN w 1 cur = some next := by
            simpa using hsplit.symm
          have hstep : step w cur = some next := by
            simpa [stepN] using hone
          exact ⟨cur, next, rfl, rfl, hstep⟩

/-- If one represented tongue changes across a successful raw step, that
step is productive and its writer is exactly that switch. -/
theorem raw_tongue_change_is_productive_writer
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start : Nat × Tongues} {k : Nat}
    {cur next : Nat × Tongues}
    (hcur : stepN w k start = some cur)
    (hnext : stepN w (k+1) start = some next)
    (hstep : step w cur = some next)
    (hchange : next.2 C ≠ cur.2 C) :
    RawProductiveAt w N start k ∧ rawWriterAt w start k = C := by
  have hparts := step_some_parts hstep
  have harrived : next.2 = (arrive cur.2 cur.1).2 := by
    simpa [arrivedTongues] using hparts.2
  have hwriter : cur.1/3 = C := by
    apply Classical.byContradiction
    intro hne
    apply hchange
    rw [harrived]
    exact arrive_preserves_other rfl (Ne.symm hne)
  have hvectorChange : restrictedTonguesAt w N start (k+1) ≠
      restrictedTonguesAt w N start k := by
    intro hEq
    have hfull : VectorCount.restrict N next.2 =
        VectorCount.restrict N cur.2 := by
      simpa [restrictedTonguesAt, tonguesAt, hcur, hnext] using hEq
    have hbit := restrict_eq_apply hfull hC
    exact hchange hbit
  constructor
  · exact ⟨by simp [hnext], hvectorChange⟩
  · simp [rawWriterAt, rawEntryAt, hcur, hwriter]

/-- Restricted-vector productivity is a genuine change of the entered
switch's own tongue. -/
theorem rawProductiveAt_changes_writer
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ cur next,
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next ∧
      next.2 (cur.1/3) ≠ cur.2 (cur.1/3) := by
  obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
    productive_step_configs hprod
  have hparts := step_some_parts hstep
  have hwriterLt : cur.1/3 < N := by
    have hraw : rawWriterAt w start k = cur.1/3 := by
      simp [rawWriterAt, rawEntryAt, hcur]
    rw [← hraw]
    exact rawProductiveAt_writer_lt hN hprod
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
      have hjN : j < N := List.mem_range.mp hj
      by_cases hjWriter : j = cur.1/3
      · simpa [hjWriter] using hsame
      · rw [harrived]
        exact arrive_preserves_other rfl hjWriter
    simpa [restrictedTonguesAt, tonguesAt, hcur, hnext] using hrestrict
  exact ⟨cur, next, hcur, hnext, hstep, hchanged⟩


theorem rawProductiveAt_is_endpoint_pivot
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ cur next C,
      C = rawWriterAt w start k ∧
      stepN w k start = some cur ∧
      stepN w (k+1) start = some next ∧
      step w cur = some next ∧
      exitPort cur = 3*C ∧
      next.2 = flipAt cur.2 C := by
  obtain ⟨cur, next, hcur, hnext, hstep, hchanged⟩ :=
    rawProductiveAt_changes_writer hN hprod
  let C := cur.1/3
  have hC : C = rawWriterAt w start k := by
    simp [C, rawWriterAt, rawEntryAt, hcur]
  have hparts := step_some_parts hstep
  have harrive : arrive cur.2 cur.1 = (exitPort cur, next.2) := by
    apply Prod.ext
    · rfl
    · exact hparts.2.symm
  obtain ⟨_hbranch, hexit, _hpin⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hflip : next.2 = flipAt cur.2 C := by
    exact changed_arrival_eq_flipAt harrive hchanged
  refine ⟨cur, next, C, hC, hcur, hnext, hstep, ?_, hflip⟩
  simpa [C] using hexit

end GeneralN
