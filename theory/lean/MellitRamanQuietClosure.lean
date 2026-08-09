import MellitRamanBABAAssembly
import MinimalBABAQuietDogbone

/-!
# Closing the quiet-dogbone subcase of the Mellit/Raman residue

`MinimalBABAQuietDogbone` is a finite-segment theorem: if the three gaps of
one raw BABA are quiet, every represented vector from `prior` through
`third+1` is one of four Gray corners.  It does not assert an infinite tail.

Accordingly, a bare `RamanQuietForeignResidue` is not itself contradictory:
that residue says neither that all three outer BABA gaps are quiet nor that
the five selected closes lie in the segment.  This file eliminates the exact
subcase supported by the theorem and replaces the bare Raman alternative by
two explicit failures of its premises: a selected close escapes the segment,
or an outer BABA gap contains another productive event.
-/

namespace GeneralN

/-- One of the five selected tail closes lies outside the finite BABA
segment covered by the quiet-dogbone theorem. -/
def SelectedTailEscapesBABA
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (prior third : Nat) : Prop :=
  ∃ t,
    t ∈ [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1] ∧
    (t < prior ∨ third + 1 < t)

/-- At least one of the three open intervals between the four BABA endpoints
contains another raw productive event. -/
def BABAGapHasProductive
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (_B : RawBABAInterlacement
      w N start prior second reroute third) : Prop :=
  ∃ k,
    ((prior < k ∧ k < second) ∨
      (second < k ∧ k < reroute) ∨
      (reroute < k ∧ k < third)) ∧
    RawProductiveAt w N start k

/-- The exact quiet, placed BABA subcase is impossible in the canonical raw
six-event obstruction: `quiet_segment_four_novelty_cover` is literally the
cover forbidden by `no_tail_four_cover`. -/
theorem RawOverlappingFiveWindowReduction.quiet_baba_selected_tail_false
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (hquietPriorSecond : ∀ k, prior < k → k < second →
      ¬ RawProductiveAt w N start k)
    (hquietSecondReroute : ∀ k, second < k → k < reroute →
      ¬ RawProductiveAt w N start k)
    (hquietRerouteThird : ∀ k, reroute < k → k < third →
      ¬ RawProductiveAt w N start k)
    (htimes : ∀ t ∈
        [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1],
      prior ≤ t ∧ t ≤ third + 1) : False := by
  let times :=
    [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1]
  let history := rawFirstWriterHistory w N start (C.z5 + 1) ++
    [restrictedTonguesAt w N start (C.z0 + 1)]
  have hcover : FourNoveltyCover w N start times history :=
    B.quiet_segment_four_novelty_cover hN
      hquietPriorSecond hquietSecondReroute hquietRerouteThird
      times history (by simpa [times] using htimes)
  exact C.toSixEventReduction.no_tail_four_cover hN (by
    simpa [FourNoveltyCover, times, history,
      RawOverlappingFiveWindowReduction.toSixEventReduction]
      using hcover)

/-- **The bare Raman quiet residue is sharpened.**

If no selected close escapes and no BABA gap is productive, the previous
theorem gives the forbidden four-cover.  Therefore every surviving Raman
quiet residue comes with one of those two concrete obstructions. -/
theorem RawOverlappingFiveWindowReduction.raman_quiet_refines
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (hquiet : RamanQuietForeignResidue B) :
    (RamanQuietForeignResidue B ∧
      SelectedTailEscapesBABA C prior third) ∨
    (RamanQuietForeignResidue B ∧ BABAGapHasProductive B) := by
  by_cases hescape : SelectedTailEscapesBABA C prior third
  · exact Or.inl ⟨hquiet, hescape⟩
  by_cases hactive : BABAGapHasProductive B
  · exact Or.inr ⟨hquiet, hactive⟩
  have hquietPriorSecond : ∀ k, prior < k → k < second →
      ¬ RawProductiveAt w N start k := by
    intro k hprior hsecond hprod
    apply hactive
    exact ⟨k, Or.inl ⟨hprior, hsecond⟩, hprod⟩
  have hquietSecondReroute : ∀ k, second < k → k < reroute →
      ¬ RawProductiveAt w N start k := by
    intro k hsecond hreroute hprod
    apply hactive
    exact ⟨k, Or.inr (Or.inl ⟨hsecond, hreroute⟩), hprod⟩
  have hquietRerouteThird : ∀ k, reroute < k → k < third →
      ¬ RawProductiveAt w N start k := by
    intro k hreroute hthird hprod
    apply hactive
    exact ⟨k, Or.inr (Or.inr ⟨hreroute, hthird⟩), hprod⟩
  have htimes : ∀ t ∈
      [C.z1 + 1, C.z2 + 1, C.z3 + 1, C.z4 + 1, C.z5 + 1],
      prior ≤ t ∧ t ≤ third + 1 := by
    intro t ht
    have hout : ¬ (t < prior ∨ third + 1 < t) := by
      intro hbad
      exact hescape ⟨t, ht, hbad⟩
    omega
  exact (C.quiet_baba_selected_tail_false hN B
    hquietPriorSecond hquietSecondReroute hquietRerouteThird
    htimes).elim

/-- The refined top-level outcome after consuming the quiet-dogbone cover.
There is no unqualified `quietForeign` constructor left. -/
inductive MellitRamanAfterQuietOutcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    (B : RawBABAInterlacement
      w N start prior second reroute third) : Prop
  | cycle (h : MellitReachedSimpleCycle w start)
  | latePair (h : Nonempty (MellitLatePairResidue C))
  | earlyPureCrossing (h : Nonempty (MellitEarlyPureCrossingResidue C))
  | interiorLobe (k : Nat) (h : RawReachedDirectLobeAt w start k)
  | firstWriterCharge (k : Nat)
      (hsecond : second < k) (hreroute : k < reroute)
      (hfirst : RawFirstWriterAt w N start k)
  | quietEscapes
      (hquiet : RamanQuietForeignResidue B)
      (hescape : SelectedTailEscapesBABA C prior third)
  | quietGapProductive
      (hquiet : RamanQuietForeignResidue B)
      (hactive : BABAGapHasProductive B)

/-- Consume `mellit_raman_outcome` and eliminate its bare quiet alternative
with the finite quiet-dogbone four-cover. -/
theorem RawBABAOverlapMinimal.mellit_raman_after_quiet_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B) :
    MellitRamanAfterQuietOutcome C B := by
  rcases hmin.mellit_raman_outcome hN C with
    hcycle | hlate | hearly | ⟨k, hlobe⟩ |
      ⟨k, hsecond, hreroute, hfirst⟩ | hquiet
  · exact .cycle hcycle
  · exact .latePair hlate
  · exact .earlyPureCrossing hearly
  · exact .interiorLobe k hlobe
  · exact .firstWriterCharge k hsecond hreroute hfirst
  · rcases C.raman_quiet_refines hN B hquiet with
      ⟨hquiet, hescape⟩ | ⟨hquiet, hactive⟩
    · exact .quietEscapes hquiet hescape
    · exact .quietGapProductive hquiet hactive

end GeneralN
