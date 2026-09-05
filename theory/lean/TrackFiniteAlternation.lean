import TrackNoveltyCover

/-!
# The finite repeated-writer target

This file states the sharp finite-prefix interface directly over the raw
lazy-point dynamics. There is no periodic-tail premise.

A productive event is a live raw step whose restricted tongue vector changes.
Its writer is the switch entered at the start of that step. A writer is
`first` at its first productive event. A repeated-writer novelty is a later
productive event of the same switch whose resulting restricted tongue vector
has never occurred at any earlier raw time.

`restrictedTonguesAt_mem_finite_writer_cover` below shows that every
visited vector is the initial vector, the post-vector of a first productive
write, or a repeated-writer novelty, so a run's distinct vectors are
bounded by `1 + (first writers) + (repeated-writer novelties)`, with at
most `N` first writers.  Bounding the repeated-writer novelties is the
work of the rest of the development.
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

/-- This is the first productive occurrence of its writer. -/
def RawFirstWriterAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  RawProductiveAt w N start k ∧
  ∀ j, j < k → RawProductiveAt w N start j →
    rawWriterAt w start j ≠ rawWriterAt w start k

/-- The post-step vector at `k+1` has not appeared at any earlier raw time. -/
def RawNovelAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  restrictedTonguesAt w N start (k+1) ∉
    (List.range (k+1)).map (restrictedTonguesAt w N start)

/-- A novel productive event whose writer was already productive earlier. -/
def RawRepeatedWriterNovelAt (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  RawProductiveAt w N start k ∧
  ¬ RawFirstWriterAt w N start k ∧
  RawNovelAt w N start k

instance (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    Decidable (RawProductiveAt w N start k) := by
  unfold RawProductiveAt; infer_instance

instance (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    Decidable (RawFirstWriterAt w N start k) := by
  unfold RawFirstWriterAt; infer_instance

instance (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    Decidable (RawNovelAt w N start k) := by
  unfold RawNovelAt; infer_instance

instance (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    Decidable (RawRepeatedWriterNovelAt w N start k) := by
  unfold RawRepeatedWriterNovelAt; infer_instance

def rawFirstWriterTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat :=
  (List.range K).filter
    (fun k => decide (RawFirstWriterAt w N start k))

def rawRepeatedWriterNovelTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat :=
  (List.range K).filter
    (fun k => decide (RawRepeatedWriterNovelAt w N start k))


theorem mem_rawFirstWriterTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawFirstWriterTimes w N start K ↔
      k < K ∧ RawFirstWriterAt w N start k := by
  simp [rawFirstWriterTimes]

theorem mem_rawRepeatedWriterNovelTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawRepeatedWriterNovelTimes w N start K ↔
      k < K ∧ RawRepeatedWriterNovelAt w N start k := by
  simp [rawRepeatedWriterNovelTimes]

theorem nodup_filter_nat (p : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter p).Nodup := by grind
theorem rawNovelAt_productive
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (hnovel : RawNovelAt w N start k) :
    RawProductiveAt w N start k := by
  constructor
  · cases hnext : stepN w (k+1) start with
    | some next => simp
    | none =>
        exfalso
        apply hnovel
        apply List.mem_map.mpr
        refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
        calc
          restrictedTonguesAt w N start 0 =
              VectorCount.restrict N start.2 := by
            simp [restrictedTonguesAt, tonguesAt, stepN]
          _ = restrictedTonguesAt w N start (k+1) := by
            simp [restrictedTonguesAt, tonguesAt, hnext]
  · intro heq
    apply hnovel
    apply List.mem_map.mpr
    refine ⟨k, List.mem_range.mpr (by omega), ?_⟩
    exact heq.symm


theorem rawProductiveAt_writer_lt
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    rawWriterAt w start k < N := by
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
          have hparts := step_some_parts hstep
          have hexit : exitPort cur < 3*N :=
            (hN (exitPort cur) next.1 hparts.1).1
          have hswitch := arrive_exit_switch cur.2 cur.1
          unfold rawWriterAt rawEntryAt
          simp [hcur]
          unfold exitPort at hexit
          omega

/-- First productive writers are injective by their switch label. -/
theorem rawFirstWriterAt_injective
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {i j : Nat}
    (hi : RawFirstWriterAt w N start i)
    (hj : RawFirstWriterAt w N start j)
    (hwriter : rawWriterAt w start i = rawWriterAt w start j) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  · by_cases hlt : i < j
    · exact (hj.2 i hlt hi.1 hwriter).elim
    · have hgt : j < i := by omega
      exact (hi.2 j hgt hj.1 hwriter.symm).elim

def rawFirstWriterHistory
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List (List Bool) :=
  restrictedTonguesAt w N start 0 ::
    (rawFirstWriterTimes w N start K).map
      (fun k => restrictedTonguesAt w N start (k+1))

/-- Post-vectors of the repeated-writer novelties. -/
def rawRepeatedWriterFresh
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List (List Bool) :=
  (rawRepeatedWriterNovelTimes w N start K).map
    (fun k => restrictedTonguesAt w N start (k+1))


theorem restrictedTonguesAt_mem_finite_writer_cover
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    ∀ k, k ≤ K →
      restrictedTonguesAt w N start k ∈
        rawFirstWriterHistory w N start K ++
          rawRepeatedWriterFresh w N start K := by
  have main : ∀ bound k, k ≤ bound → bound ≤ K →
      restrictedTonguesAt w N start k ∈
        rawFirstWriterHistory w N start K ++
          rawRepeatedWriterFresh w N start K := by
    intro bound
    induction bound with
    | zero =>
        intro k hk _hK
        have hk0 : k = 0 := by omega
        subst k
        simp [rawFirstWriterHistory]
    | succ n ih =>
        intro k hk hboundK
        by_cases hkn : k ≤ n
        · exact ih k hkn (by omega)
        · have hkEq : k = n+1 := by omega
          subst k
          by_cases hnovel : RawNovelAt w N start n
          · have hprod := rawNovelAt_productive hnovel
            by_cases hfirst : RawFirstWriterAt w N start n
            · apply List.mem_append_left
              apply List.mem_cons_of_mem
              apply List.mem_map.mpr
              refine ⟨n, ?_, rfl⟩
              have hnK : n < K := by omega
              simp [rawFirstWriterTimes, hnK, hfirst]
            · apply List.mem_append_right
              apply List.mem_map.mpr
              refine ⟨n, ?_, rfl⟩
              have hnK : n < K := by omega
              have hrepeat : RawRepeatedWriterNovelAt w N start n :=
                ⟨hprod, hfirst, hnovel⟩
              simp [rawRepeatedWriterNovelTimes, hnK, hrepeat]
          · have hseen : restrictedTonguesAt w N start (n+1) ∈
                (List.range (n+1)).map
                  (restrictedTonguesAt w N start) := by
              exact Classical.not_not.mp hnovel
            obtain ⟨j, hj, hEq⟩ := List.mem_map.mp hseen
            have hjlt : j < n+1 := List.mem_range.mp hj
            rw [← hEq]
            exact ih j (by omega) (by omega)
  intro k hk
  exact main K k hk (Nat.le_refl _)

end GeneralN
