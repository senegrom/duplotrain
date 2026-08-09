import RamanOuterGapStrictDescent

/-!
# Assembling the strict Mellit/Raman residue descent

This module consumes `MellitRamanAfterGapOutcome` and replaces both remaining
quiet constructors by the unconditional time-sensitive reductions proved in
`RamanInnerReplaySelectedTail` and `RamanOuterGapStrictDescent`.

The theorem is still a reduction, not the final six-event contradiction.  Its
point is that no opaque `quietInnerReplay` or `quietOuterGap` survives:
inner replay closes are non-selected and paid/strictly earlier, while outer
gaps are late, paid, replayed, or carry a strict selected-close descent.
-/

namespace GeneralN

/-- The Mellit/Raman outcome with both quiet residues replaced by exact
history or strict-time descent data. -/
inductive MellitRamanStrictDescentOutcome
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
  | quietOuterDescent
      (hquiet : RamanQuietForeignResidue B)
      (houtcome : RamanOuterGapStrictOutcome C B)
  | quietInnerDescent
      (hquiet : RamanQuietForeignResidue B)
      (R : RamanQuietInnerReplay B)
      (hnotSelected : ¬ RawSixSelectedTime C R.closing)
      (hdisposition : RamanInnerReplayDisposition C R)

/-- **Unconditional assembled Raman descent.**  Starting from an
overlap-minimal BABA, the old post-gap theorem's last two constructors are
replaced by their strict raw-time classifications. -/
theorem RawBABAOverlapMinimal.mellit_raman_strict_descent_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B) :
    MellitRamanStrictDescentOutcome C B := by
  rcases hmin.mellit_raman_after_gap_outcome hN C with
    hcycle | hlate | hearly | ⟨k, hlobe⟩ |
      ⟨k, hsecond, hreroute, hfirst⟩ |
      ⟨hquiet, hescape⟩ | ⟨hquiet, houter⟩ |
      ⟨hquiet, hreplay⟩
  · exact .cycle hcycle
  · exact .latePair hlate
  · exact .earlyPureCrossing hearly
  · exact .interiorLobe k hlobe
  · exact .firstWriterCharge k hsecond hreroute hfirst
  · exact .quietEscapes hquiet hescape
  · exact .quietOuterDescent hquiet
      (hmin.outer_gap_strict_outcome hN C houter)
  · obtain ⟨R⟩ := hreplay
    exact .quietInnerDescent hquiet R
      (R.close_not_selected C) (R.selected_tail_disposition C)

end GeneralN
