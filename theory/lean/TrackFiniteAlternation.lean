import TrackNoveltyCover

/-!
# Productive steps and first-writer histories

A productive step changes the restricted tongue vector. Its writer is the
switch entered at that step, and first productive writers have distinct
switch labels. On a switch-simple trace every productive step is a first
write, so these histories cover the whole trace.
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

instance (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    Decidable (RawProductiveAt w N start k) := by
  unfold RawProductiveAt; infer_instance

instance (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    Decidable (RawFirstWriterAt w N start k) := by
  unfold RawFirstWriterAt; infer_instance

def rawFirstWriterTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat :=
  (List.range K).filter
    (fun k => decide (RawFirstWriterAt w N start k))

theorem mem_rawFirstWriterTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawFirstWriterTimes w N start K ↔
      k < K ∧ RawFirstWriterAt w N start k := by
  simp [rawFirstWriterTimes]

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

/-- First productive writers are injective by their switch label. -/
theorem rawFirstWriterAt_injective
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {i j : Nat}
    (hi : RawFirstWriterAt w N start i)
    (hj : RawFirstWriterAt w N start j)
    (hwriter : rawWriterAt w start i = rawWriterAt w start j) :
    i = j := by
  grind [RawFirstWriterAt]

def rawFirstWriterHistory
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List (List Bool) :=
  restrictedTonguesAt w N start 0 ::
    (rawFirstWriterTimes w N start K).map
      (fun k => restrictedTonguesAt w N start (k+1))

end GeneralN
