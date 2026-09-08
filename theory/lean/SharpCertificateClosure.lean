import ManufacturedPairNovelty

/-!
# Productive steps, histories and time shifts

A productive step changes the restricted tongue vector; its writer is the
switch entered at that step. Such a step exits by the writer's stem and flips
exactly the writer's tongue, a quiet interval preserves the restricted vector,
and undoing the last productive flip recovers the vector before it. Recording
every productive post-vector covers any live prefix, and live time shifts
preserve restricted vectors. In a switch-simple trace the writer labels are
injective, supplying the finite coordinate count separately.
-/

namespace GeneralN

/-- The entry port at raw time `k`; the default is irrelevant whenever the
run is live at that time. -/
def rawEntryAt (w : Wiring) (start : Nat × Tongues) (k : Nat) : Nat :=
  ((stepN w k start).getD start).1

/-- The switch written by a productive raw step at time `k`. -/
def rawWriterAt (w : Wiring) (start : Nat × Tongues) (k : Nat) : Nat :=
  rawEntryAt w start k / 3

/-- A live raw step changes the visible `N`-switch tongue vector. -/
def RawProductiveAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  (stepN w (k+1) start).isSome ∧
  restrictedTonguesAt w N start (k+1) ≠
    restrictedTonguesAt w N start k

instance (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    Decidable (RawProductiveAt w N start k) := by
  unfold RawProductiveAt; infer_instance

def rawProductiveTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat :=
  (List.range K).filter
    (fun k => decide (RawProductiveAt w N start k))

theorem mem_rawProductiveTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawProductiveTimes w N start K ↔
      k < K ∧ RawProductiveAt w N start k := by
  simp [rawProductiveTimes]

theorem rawProductiveAt_writer_lt
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    rawWriterAt w start k < N := by
  obtain ⟨cur, next, hcur, _, hstep⟩ := live_successor_configs hprod.1
  have hbound := (hN _ _ (step_some_parts hstep).1).1
  have hswitch := arrive_exit_switch cur.2 cur.1
  have hlt : cur.1 / 3 < N := by
    dsimp [exitPort] at hbound
    omega
  simpa [rawWriterAt, rawEntryAt, hcur] using hlt

def rawProductiveHistory
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List (List Bool) :=
  restrictedTonguesAt w N start 0 ::
    (rawProductiveTimes w N start K).map
      (fun k => restrictedTonguesAt w N start (k+1))

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

/-- A historical prefix adds no cost to a novelty cover of its shifted tail. -/
theorem NoveltyCoverOn.prepend
    {w : Wiring} {N K budget : Nat} {start middle : Nat × Tongues}
    {times localTimes : List Nat} {history : List (List Bool)}
    (hlocal : NoveltyCoverOn w N middle localTimes history budget)
    (hreach : stepN w K start = some middle)
    (hprefix : ∀ k, k ≤ K → restrictedTonguesAt w N start k ∈ history)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hmem : ∀ k ∈ times, K < k → k - K ∈ localTimes) :
    NoveltyCoverOn w N start times history budget := by
  obtain ⟨fresh, hfresh, hcover⟩ := hlocal
  refine ⟨fresh, hfresh, ?_⟩
  intro k hk
  by_cases hle : k ≤ K
  · exact List.mem_append_left _ (hprefix k hle)
  · have ht : k = K + (k - K) := by omega
    rw [ht, restrictedTonguesAt_add_of_reaches (N := N) (d := k - K) hreach
      (stepN_suffix_some_of_reaches (d := k - K) hreach (by rw [← ht]; exact hlive k hk))]
    exact hcover _ (hmem k hk (by omega))

theorem PhysicalTrace.rawWriterAt_eq_passageSwitch_getElem
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    ∀ {k : Nat} (hk : k < passages.length),
      rawWriterAt w start k = passageSwitch passages[k] := by
  intro k hk
  induction htrace generalizing k with
  | nil => simp at hk
  | @cons p x q u v passages finish harrive hlink tail ih =>
      cases k with
      | zero =>
          simp [rawWriterAt, rawEntryAt, stepN, passageSwitch]
      | succ k =>
          have hkTail : k < passages.length := by simpa using hk
          obtain ⟨cfg, hcfg⟩ := stepN_prefix_some (Nat.le_of_lt hkTail) tail.sound
          simpa [rawWriterAt, rawEntryAt, stepN, step, harrive, hlink, hcfg] using ih hkTail

/-- A switch-simple trace visits each writer at most once. -/
theorem PhysicalTrace.rawWriterAt_injective
    {w : Wiring} {start finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) (hsimple : SwitchSimple passages)
    {i j : Nat} (hi : i < passages.length) (hj : j < passages.length)
    (heq : rawWriterAt w start i = rawWriterAt w start j) : i = j := by
  apply (List.getElem_inj (h₀ := by simpa using hi) (h₁ := by simpa using hj) hsimple).mp
  simpa [htrace.rawWriterAt_eq_passageSwitch_getElem hi,
    htrace.rawWriterAt_eq_passageSwitch_getElem hj] using heq

/-- The initial vector and post-vectors of productive steps cover every
live prefix, including repeated visits to a writer. -/
theorem restrictedTonguesAt_mem_rawProductiveHistory
    {w : Wiring} {N K : Nat} {start finish : Nat × Tongues}
    (hfinish : stepN w K start = some finish) :
    ∀ k, k ≤ K → restrictedTonguesAt w N start k ∈ rawProductiveHistory w N start K := by
  intro k
  induction k with
  | zero => intro _; simp [rawProductiveHistory]
  | succ k ih =>
      intro hk
      by_cases heq : restrictedTonguesAt w N start (k + 1) = restrictedTonguesAt w N start k
      · rw [heq]; exact ih (by omega)
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr
          ⟨k, mem_rawProductiveTimes_iff.mpr ⟨by omega,
            Option.isSome_iff_exists.mpr (stepN_prefix_some hk hfinish), heq⟩, rfl⟩)

end GeneralN
