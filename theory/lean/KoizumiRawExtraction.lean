import TrackCurveGrowth
import KoizumiCurveInvariant

/-!
# Extracting Koizumi curve growth from a raw train step

The curve lemmas in `TrackCurveGrowth` are stated for an abstract endpoint
pivot, while the user-facing dynamics is `Wiring.stepN`.  This file closes
that local interface without adding any recurrence or periodicity premise.

Every productive raw step enters the currently unmatched branch of one
switch and flips exactly that switch.  Consequently there are only two
possibilities:

* the entered endpoint was already connected to the switch stem (a
  self-pivot); or
* the old train curve is pointwise contained in the new train curve and the
  switch stem is a genuinely new point of it.

The second alternative is the strict curve-growth move used in Koizumi's
train-free-curve descent.  What remains global is to select and maintain the
complementary train-free subcurve through intervening self-pivots.
-/

namespace GeneralN

/-- Complete raw data for a productive endpoint pivot, together with the
selected-matching surgery certified by `flipAt_is_curve_endpoint_pivot`. -/
structure RawKoizumiPivot
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) where
  before : Nat × Tongues
  after : Nat × Tongues
  writer : Nat
  writer_eq : writer = rawWriterAt w start k
  before_at : stepN w k start = some before
  after_at : stepN w (k + 1) start = some after
  physical_step : step w before = some after
  entered_endpoint : before.1 = unmatchedBranch before.2 writer
  exited_stem : exitPort before = 3 * writer
  state_flip : after.2 = flipAt before.2 writer
  matching_pivot : CurveEndpointPivot before.2 writer

/-- A productive raw event exposes exactly Koizumi's endpoint pivot. -/
theorem rawProductiveAt_koizumiPivot
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    Nonempty (RawKoizumiPivot w N start k) := by
  obtain ⟨before, after, C, hC, hbefore, hafter, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  exact ⟨{
    before := before
    after := after
    writer := C
    writer_eq := hC
    before_at := hbefore
    after_at := hafter
    physical_step := hstep
    entered_endpoint := hentry
    exited_stem := hexit
    state_flip := hflip
    matching_pivot := flipAt_is_curve_endpoint_pivot before.2 C
  }⟩

/-- **Raw Koizumi dichotomy.**

At every productive raw step, either the old endpoint and stem were already
on one selected curve, or the pivot is strict growth of the train curve:
all points reachable from the entered endpoint before the step remain
reachable afterwards, while the stem becomes reachable for the first time.
-/
theorem rawProductiveAt_self_or_strict_curve_growth
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    ∃ before after C,
      C = rawWriterAt w start k ∧
      stepN w k start = some before ∧
      stepN w (k + 1) start = some after ∧
      step w before = some after ∧
      before.1 = unmatchedBranch before.2 C ∧
      after.2 = flipAt before.2 C ∧
      (CurveReach w before.2 before.1 (3 * C) ∨
        ((∀ p, CurveReach w before.2 before.1 p →
            CurveReach w after.2 before.1 p) ∧
         CurveReach w after.2 before.1 (3 * C) ∧
         ¬ CurveReach w before.2 before.1 (3 * C))) := by
  obtain ⟨P⟩ := rawProductiveAt_koizumiPivot hN hprod
  refine ⟨P.before, P.after, P.writer, P.writer_eq, P.before_at,
    P.after_at, P.physical_step, P.entered_endpoint, P.state_flip, ?_⟩
  by_cases hself : CurveReach w P.before.2 P.before.1 (3 * P.writer)
  · exact Or.inl hself
  · right
    have houtside : ¬ CurveReach w P.before.2
        (unmatchedBranch P.before.2 P.writer) (3 * P.writer) := by
      simpa [P.entered_endpoint] using hself
    obtain ⟨hpreserve, hstem, hold⟩ :=
      unmatched_pivot_strict_curve_growth P.before.2 P.writer houtside
    constructor
    · intro p hp
      rw [P.state_flip, P.entered_endpoint]
      apply hpreserve p
      simpa [P.entered_endpoint] using hp
    · constructor
      · rw [P.state_flip, P.entered_endpoint]
        simpa [P.entered_endpoint] using hstem
      · exact hself

end GeneralN
