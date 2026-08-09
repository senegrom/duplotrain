import MellitRamanQuietClosure

/-!
# Refining the productive-gap Raman residue

MellitRamanQuietClosure leaves two honest alternatives after consuming the
fully quiet, correctly placed BABA: a selected tail close escapes the finite
BABA segment, or some BABA gap contains another productive event.

The second alternative can be sharpened without any continuation
certificate.  In the no-interior-frame Raman branch, a productive event in
the central overlap is necessarily a globally first writer: a repeated
writer would either open an interior frame or create a strictly smaller
BABA.  In the least-frame branch, the sparse foreign frame is an actual raw
last-writer frame; its quiet interior makes its closing post-vector an exact
historical replay, hence the close is not novel.

Thus the undifferentiated productive-gap residue reduces to exactly three
raw, time-anchored outcomes:

* a globally first productive writer in the overlap;
* a productive event in one of the two outer BABA wings; or
* a least-closing quiet inner frame with an explicit replay equation.

The selected-tail escape and the outer-wing routing remain open.  No sparse
overwrite sequence is treated as an Echo.IsRun.
-/

namespace GeneralN

/-- A productive event in one of the two outer, non-overlap BABA gaps. -/
def BABAOuterGapHasProductive
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (_B : RawBABAInterlacement
      w N start prior second reroute third) : Prop :=
  ∃ k,
    ((prior < k ∧ k < second) ∨
      (reroute < k ∧ k < third)) ∧
    RawProductiveAt w N start k

/-- If no last-writer frame opens in the central overlap of an
overlap-minimal BABA, every productive event there is a globally first
writer.

For a non-first writer, let left be its previous productive occurrence.
If left is in the overlap, that is the forbidden interior frame.  If
left = second, it contradicts the right BABA frame.  If left < second,
the frame left < k crossed with the right frame is a strictly smaller
BABA. -/
theorem RawBABAOverlapMinimal.no_frame_central_productive_first
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third k : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hnoFrame : ∀ opening closing,
      second < opening →
      opening < reroute →
      RawLastWriterFrame w N start opening closing →
      False)
    (hsecond : second < k)
    (hreroute : k < reroute)
    (hprod : RawProductiveAt w N start k) :
    RawFirstWriterAt w N start k := by
  by_cases hfirst : RawFirstWriterAt w N start k
  · exact hfirst
  · obtain ⟨left, G⟩ :=
      last_writer_frame_of_productive_not_first hprod hfirst
    by_cases hleftLe : left ≤ second
    · by_cases hleftEq : left = second
      · subst left
        have hkThird : k < third :=
          Nat.lt_trans hreroute B.reroute_lt_third
        have hne := B.rightFrame.no_same_writer_between k
          hsecond hkThird hprod
        exact (hne
          (G.same_writer.symm.trans
            B.rightFrame.same_writer)).elim
      · have hleftLt : left < second := by omega
        have hkThird : k < third :=
          Nat.lt_trans hreroute B.reroute_lt_third
        have hdiff :
            rawWriterAt w start k ≠
              rawWriterAt w start third :=
          B.rightFrame.no_same_writer_between k
            hsecond hkThird hprod
        let C : RawBABAInterlacement
            w N start left second k third := {
          prior_lt_second := hleftLt
          second_lt_reroute := hsecond
          reroute_lt_third := hkThird
          leftFrame := G
          rightFrame := B.rightFrame
          different_writers := hdiff
        }
        have hsmaller : C.overlap < B.overlap := by
          change k - second < reroute - second
          omega
        exact (hmin left second k third C hsmaller).elim
    · have hsecondLeft : second < left := by omega
      have hleftReroute : left < reroute :=
        Nat.lt_trans G.order hreroute
      exact (hnoFrame left k hsecondLeft hleftReroute G).elim

/-- The complete least-frame branch of RamanQuietForeignResidue, enhanced
with its physical raw frame, exact replay equation, and resulting
non-novelty of the close. -/
structure RamanQuietInnerReplay
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third) : Type where
  opening : Nat
  closing : Nat
  second_lt_opening : second < opening
  opening_lt_reroute : opening < reroute
  opening_lt_closing : opening < closing
  closing_lt_reroute : closing < reroute
  foreign : Echo.ForeignRestorationFrame
    (rawOverwriteMachine w) (rawOverwriteEntry w N start)
    (rawOverwriteInitial start) opening closing
  rawFrame : RawLastWriterFrame w N start opening closing
  minimalClose : ∀ opening' closing',
    second < opening' →
    opening' < reroute →
    RawLastWriterFrame w N start opening' closing' →
    closing' < closing → False
  quiet : ∀ k, opening < k → k < closing →
    ¬ RawProductiveAt w N start k
  replay :
    restrictedTonguesAt w N start (closing + 1) =
      restrictedTonguesAt w N start opening
  close_not_novel : ¬ RawNovelAt w N start closing

/-- Exact refinement of the productive-gap alternative left by
raman_quiet_refines. -/
inductive RamanGapProductiveOutcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third) : Prop
  | firstWriterCharge (k : Nat)
      (hsecond : second < k) (hreroute : k < reroute)
      (hfirst : RawFirstWriterAt w N start k)
  | outerGap (h : BABAOuterGapHasProductive B)
  | innerReplay (h : Nonempty (RamanQuietInnerReplay B))

/-- A productive BABA gap in a surviving Raman quiet residue is either paid
by a globally first writer, lies in an outer wing, or belongs to the exact
least quiet frame whose close is a historical replay. -/
theorem RawBABAOverlapMinimal.raman_gap_productive_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hquiet : RamanQuietForeignResidue B)
    (hactive : BABAGapHasProductive B) :
    RamanGapProductiveOutcome B := by
  rcases hquiet with hnoFrame |
      ⟨opening, closing, hsecondOpening, hopenReroute,
        hopenClose, hcloseReroute, hforeign, hminimal, hquietOpen⟩
  · obtain ⟨k, hgap, hprod⟩ := hactive
    rcases hgap with hleft | hrest
    · exact .outerGap ⟨k, Or.inl hleft, hprod⟩
    · rcases hrest with hmiddle | hright
      · exact .firstWriterCharge k hmiddle.1 hmiddle.2
          (hmin.no_frame_central_productive_first
            hnoFrame hmiddle.1 hmiddle.2 hprod)
      · exact .outerGap ⟨k, Or.inr hright, hprod⟩
  · let F : RawLastWriterFrame w N start opening closing :=
      sparse_foreignRestoration_to_rawLastWriterFrame hN hforeign
    have hreplay :
        restrictedTonguesAt w N start (closing + 1) =
          restrictedTonguesAt w N start opening :=
      F.closes_vector_of_quiet hN hquietOpen
    have hnotNovel : ¬ RawNovelAt w N start closing := by
      intro hnovel
      apply hnovel
      apply List.mem_map.mpr
      exact ⟨opening, List.mem_range.mpr (by omega), hreplay.symm⟩
    exact .innerReplay ⟨{
      opening := opening
      closing := closing
      second_lt_opening := hsecondOpening
      opening_lt_reroute := hopenReroute
      opening_lt_closing := hopenClose
      closing_lt_reroute := hcloseReroute
      foreign := hforeign
      rawFrame := F
      minimalClose := hminimal
      quiet := hquietOpen
      replay := hreplay
      close_not_novel := hnotNovel
    }⟩

/-- The top-level Mellit/Raman outcome after replacing the coarse
productive-gap residue by the three exact alternatives above. -/
inductive MellitRamanAfterGapOutcome
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
  | quietOuterGap
      (hquiet : RamanQuietForeignResidue B)
      (houter : BABAOuterGapHasProductive B)
  | quietInnerReplay
      (hquiet : RamanQuietForeignResidue B)
      (hreplay : Nonempty (RamanQuietInnerReplay B))

/-- Consume mellit_raman_after_quiet_outcome and sharpen its remaining
productive-gap constructor. -/
theorem RawBABAOverlapMinimal.mellit_raman_after_gap_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B) :
    MellitRamanAfterGapOutcome C B := by
  rcases hmin.mellit_raman_after_quiet_outcome hN C with
    hcycle | hlate | hearly | ⟨k, hlobe⟩ |
      ⟨k, hsecond, hreroute, hfirst⟩ |
      ⟨hquiet, hescape⟩ | ⟨hquiet, hactive⟩
  · exact .cycle hcycle
  · exact .latePair hlate
  · exact .earlyPureCrossing hearly
  · exact .interiorLobe k hlobe
  · exact .firstWriterCharge k hsecond hreroute hfirst
  · exact .quietEscapes hquiet hescape
  · rcases hmin.raman_gap_productive_outcome hN hquiet hactive with
      ⟨k, hsecond, hreroute, hfirst⟩ | houter | hreplay
    · exact .firstWriterCharge k hsecond hreroute hfirst
    · exact .quietOuterGap hquiet houter
    · exact .quietInnerReplay hquiet hreplay

end GeneralN

