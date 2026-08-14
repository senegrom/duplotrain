import ConcreteTreeRetrace
import ConcreteEchoStep

/-!
# Concrete ascent traces and interval last-writer preservation

A concrete ascent trace records one landed trailing cascade per abstract time.
Facing movement between cascades changes no tongue, so the next boundary tongue
is exactly the result of the current canonical overwrite word.

For indices `j < … ≤ k`, the boundary after ascent `k` is the result of the
canonical actions strictly after `j` applied to the boundary after ascent `j`.
If none of those intervening ascents has `j`'s root, tree disjointness preserves
all pins laid at `j`; hence the old cascade still retraces at time `k`.
-/

namespace GeneralN

/-- A landed trailing-cascade sequence. -/
structure ConcreteAscentTrace (w : Wiring) where
  entry : Nat → Nat
  boundary : Nat → Tongues
  tail : Nat → List Nat
  landing : Nat → Nat
  descent : ∀ k,
    Descent w (boundary k) (entry k) (tail k) (landing k)
      (boundary (k + 1))
  freeSlot : ∀ k, IsCanonicalEchoSlot w (entry k)
  properRoot : ∀ k, ProperMouthRoot w (entryRoot w (entry k))

/-- Entries strictly after `start`, for `count` consecutive ascent times. -/
def entriesAfter (entry : Nat → Nat) (start : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 =>
      entriesAfter entry start count ++ [entry (start + count + 1)]

/-- Sequential execution respects list concatenation. -/
theorem runEntryActions_append
    (w : Wiring) (xs ys : List Nat) (t : Tongues) :
    runEntryActions w (xs ++ ys) t =
      runEntryActions w ys (runEntryActions w xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.cons_append, runEntryActions]
      exact ih (pinList (entryAction w x) t)

/-- Appending one ascent applies exactly its canonical action last. -/
theorem runEntryActions_append_singleton
    (w : Wiring) (xs : List Nat) (q : Nat) (t : Tongues) :
    runEntryActions w (xs ++ [q]) t =
      pinList (entryAction w q) (runEntryActions w xs t) := by
  rw [runEntryActions_append]
  rfl

/-- Membership in `entriesAfter` gives the corresponding strict time
interval. -/
theorem mem_entriesAfter
    (entry : Nat → Nat) (start : Nat) :
    ∀ {count q}, q ∈ entriesAfter entry start count →
      ∃ i, start < i ∧ i ≤ start + count ∧ q = entry i := by
  intro count
  induction count with
  | zero =>
      intro q hq
      cases hq
  | succ n ih =>
      intro q hq
      unfold entriesAfter at hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨i, hiLo, hiHi, rfl⟩ := ih hq
        exact ⟨i, hiLo, by omega, rfl⟩
      · have hqeq : q = entry (start + n + 1) := by
          simpa using hq
        exact ⟨start + n + 1, by omega, by omega, hqeq⟩

/-- Every interval entry is a realised canonical free slot. -/
theorem entriesAfter_realised
    {w : Wiring} (trace : ConcreteAscentTrace w)
    (start count : Nat) :
    ∀ q ∈ entriesAfter trace.entry start count,
      IsDescentEntry w q := by
  intro q hq
  obtain ⟨i, hiLo, hiHi, rfl⟩ :=
    mem_entriesAfter trace.entry start hq
  exact (trace.freeSlot i).1

/-- One trace step is its canonical overwrite action. -/
theorem trace_boundary_succ
    {w : Wiring} (trace : ConcreteAscentTrace w) (k : Nat) :
    trace.boundary (k + 1) =
      pinList (entryAction w (trace.entry k)) (trace.boundary k) := by
  exact descent_result_eq_entryAction (trace.descent k)

/-- The boundary after an interval is the accumulated list of its canonical
entry actions. -/
theorem trace_boundary_after
    {w : Wiring} (trace : ConcreteAscentTrace w) (start : Nat) :
    ∀ count,
      trace.boundary (start + count + 1) =
        runEntryActions w (entriesAfter trace.entry start count)
          (trace.boundary (start + 1)) := by
  intro count
  induction count with
  | zero =>
      simp [entriesAfter, runEntryActions]
  | succ n ih =>
      have hstep := trace_boundary_succ trace (start + n + 1)
      have hindex : start + (n + 1) + 1 =
          (start + n + 1) + 1 := by omega
      rw [hindex, hstep]
      rw [ih]
      show pinList (entryAction w (trace.entry (start + n + 1)))
          (runEntryActions w (entriesAfter trace.entry start n)
            (trace.boundary (start + 1))) =
        runEntryActions w
          (entriesAfter trace.entry start n ++
            [trace.entry (start + n + 1)])
          (trace.boundary (start + 1))
      rw [runEntryActions_append_singleton]

/-- If the interval contains no ascent of `start`'s root, it preserves all
pins laid by the ascent at `start`. -/
theorem trace_last_writer_agrees
    {w : Wiring} (trace : ConcreteAscentTrace w)
    (start count : Nat)
    (hno : ∀ i, start < i → i ≤ start + count →
      entryRoot w (trace.entry start) ≠
        entryRoot w (trace.entry i)) :
    Agrees (trace.boundary (start + count + 1))
      (entryAction w (trace.entry start)) := by
  have hp : IsDescentEntry w (trace.entry start) :=
    (trace.freeSlot start).1
  have hentries : ∀ q ∈ entriesAfter trace.entry start count,
      IsDescentEntry w q :=
    entriesAfter_realised trace start count
  have hroots : ∀ q ∈ entriesAfter trace.entry start count,
      entryRoot w (trace.entry start) ≠ entryRoot w q := by
    intro q hq
    obtain ⟨i, hiLo, hiHi, rfl⟩ :=
      mem_entriesAfter trace.entry start hq
    exact hno i hiLo hiHi
  rw [trace_boundary_after]
  apply runEntryActions_preserves_agrees hp
    (entriesAfter trace.entry start count) hentries hroots
  have hself := entryAction_self_agrees hp (trace.boundary start)
  rw [trace_boundary_succ trace start]
  exact hself

/-- **Trace-level last-writer retrace.**  If ascent `current = start+count`
lands at the root last written at `start`, and no intervening ascent has that
root, facing from the current landing exits at the jump partner of the old
entry. -/
theorem trace_last_writer_retrace
    {w : Wiring} (trace : ConcreteAscentTrace w)
    (start count : Nat)
    (hno : ∀ i, start < i → i ≤ start + count →
      entryRoot w (trace.entry start) ≠
        entryRoot w (trace.entry i))
    (hlands : trace.landing (start + count) / 3 =
      entryRoot w (trace.entry start)) :
    stepN w (entryAction w (trace.entry start)).length
      (trace.landing (start + count),
        trace.boundary (start + count + 1)) =
      some (wireBar w (trace.entry start),
        trace.boundary (start + count + 1)) := by
  let f := trace.entry start
  have hd := trace.descent start
  have hentry := canonicalEchoSlot_reverse_link
    (trace.freeSlot start)
  have hagree := trace_last_writer_agrees trace start count hno
  have hret := retrace hd (wireBar w f) hentry
    (trace.boundary (start + count + 1)) (by
      simpa [f, entryAction_eq_of_descent hd] using hagree)
  have hstartRoot :
      3 * (lastOf f (trace.tail start) / 3) =
        3 * entryRoot w f := by
    rw [entryRoot_eq_of_descent hd]
    rfl
  have hlandingStem := descent_landing_stem
    (trace.descent (start + count))
  have hlandingEq : trace.landing (start + count) =
      3 * entryRoot w f := by
    have hstem := stem_eq_three_mul_div hlandingStem
    rw [hlands] at hstem
    dsimp [f]
    omega
  rw [entryAction_eq_of_descent hd,
    hlandingEq, ← hstartRoot]
  exact hret

end GeneralN
