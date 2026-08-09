import RamanInnerReplaySelectedTail
import MellitRamanResidueDescent

/-!
# Strict descent for productive Raman outer gaps

A productive event in an outer BABA wing is not itself a terminal residue.
This file first classifies the last-writer frame symmetrically on the two
wings.  Overlap minimality excludes the central crossing orientation and
records every surviving crossing as non-decreasing in overlap.

For the canonical six-event argument we then use novelty, not geometry alone.
Every outer productive event is after the selected window, a first-writer
charge, an earlier-vector replay, or a selected repeated novelty.  In the last
case the selected event's last-writer frame has a strictly earlier productive
rerouter.  That rerouter is again either paid, replayed, or a strictly earlier
selected event.  Thus the selected branch has a genuine decreasing raw time;
there is no conditional recursion certificate.
-/

namespace GeneralN

/-- A selected canonical time carries its corresponding repeated-writer
novelty event. -/
theorem RawSixSelectedTime.rawRepeatedWriterNovelAt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {k : Nat} (h : RawSixSelectedTime C k) :
    RawRepeatedWriterNovelAt w N start k := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact C.event0
  · exact C.event1
  · exact C.event2
  · exact C.event3
  · exact C.event4
  · exact C.event5

/-- Every selected canonical time is at most `z5`. -/
theorem RawSixSelectedTime.le_z5
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {k : Nat} (h : RawSixSelectedTime C k) : k ≤ C.z5 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · have h01 := C.order01
    have h12 := C.order12
    have h23 := C.order23
    have h34 := C.order34
    have h45 := C.order45
    omega
  · have h12 := C.order12
    have h23 := C.order23
    have h34 := C.order34
    have h45 := C.order45
    omega
  · have h23 := C.order23
    have h34 := C.order34
    have h45 := C.order45
    omega
  · have h34 := C.order34
    have h45 := C.order45
    omega
  · have h45 := C.order45
    omega
  · exact Nat.le_refl _

/-- The post-vector of `k` occurred at a strictly earlier raw time. -/
def RamanEarlierVectorReplayAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Prop :=
  restrictedTonguesAt w N start (k + 1) ∈
    (List.range (k + 1)).map (restrictedTonguesAt w N start)

/-- Exhaustive contribution of a productive event relative to the selected
six-event window. -/
inductive RamanOuterProductiveDisposition
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (k : Nat) : Prop
  | afterSelectedTail (h : C.z5 < k)
  | firstWriter (h : RawFirstWriterAt w N start k)
  | earlierReplay (h : RamanEarlierVectorReplayAt w N start k)
  | selected (h : RawSixSelectedTime C k)

/-- A productive event is late, paid, replayed, or selected.  Before `z5`,
being neither first-writer nor replay is exactly repeated-writer novelty, so
the no-gap theorem identifies the event with one of `z0, ..., z5`. -/
theorem rawProductiveAt_outer_disposition
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {k : Nat} (hprod : RawProductiveAt w N start k) :
    RamanOuterProductiveDisposition C k := by
  classical
  by_cases hlate : C.z5 < k
  · exact .afterSelectedTail hlate
  by_cases hfirst : RawFirstWriterAt w N start k
  · exact .firstWriter hfirst
  by_cases hnovel : RawNovelAt w N start k
  · have Hk : RawRepeatedWriterNovelAt w N start k :=
      ⟨hprod, hfirst, hnovel⟩
    have hkZ5 : k ≤ C.z5 := by omega
    exact .selected (by
      simpa [RawSixSelectedTime] using
        C.repeated_novelty_at_most_z5 hkZ5 Hk)
  · exact .earlierReplay (by
      unfold RamanEarlierVectorReplayAt
      simpa [RawNovelAt] using (Classical.not_not.mp hnovel))

/-- Exact symmetric position of a non-first outer-gap last-writer frame.
A crossing which survives overlap minimality is retained together with the
new raw BABA and the proof that its overlap is not smaller. -/
inductive RamanOuterFramePosition
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (k left : Nat) : Prop
  | leftNested
      (hprior : prior < left) (hopen : left < k)
      (hclose : k < second)
  | leftCrossing
      (C : RawBABAInterlacement w N start left prior k reroute)
      (hnondecreasing : B.overlap ≤ C.overlap)
  | rightNested
      (hopen : reroute ≤ left) (hframe : left < k)
      (hclose : k < third)
  | rightCrossing
      (C : RawBABAInterlacement w N start left second k third)
      (hnondecreasing : B.overlap ≤ C.overlap)

/-- Overlap minimality classifies both outer wings.  On the right it rules
out exactly the forbidden opener `second < left < reroute`; the endpoint
cases `left = prior` and `left = second` contradict the defining last-writer
frames. -/
theorem RawBABAOverlapMinimal.outer_frame_position
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third k left : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hgap : BABAOuterGap prior second reroute third k)
    (F : RawLastWriterFrame w N start left k) :
    RamanOuterFramePosition B k left := by
  rcases hgap with hleftGap | hrightGap
  · have hkReroute : k < reroute :=
      Nat.lt_trans hleftGap.2 B.second_lt_reroute
    by_cases hleftPrior : left < prior
    · have hdiff : rawWriterAt w start k ≠
          rawWriterAt w start reroute :=
        B.leftFrame.no_same_writer_between k hleftGap.1
          hkReroute F.close_productive
      let C : RawBABAInterlacement
          w N start left prior k reroute := {
        prior_lt_second := hleftPrior
        second_lt_reroute := hleftGap.1
        reroute_lt_third := hkReroute
        leftFrame := F
        rightFrame := B.leftFrame
        different_writers := hdiff
      }
      have hnotSmaller : ¬ C.overlap < B.overlap := by
        intro hsmaller
        exact hmin left prior k reroute C hsmaller
      exact .leftCrossing C (Nat.le_of_not_gt hnotSmaller)
    · have hpriorLeft : prior ≤ left := Nat.le_of_not_gt hleftPrior
      by_cases heq : left = prior
      · subst left
        have hdiff : rawWriterAt w start k ≠
            rawWriterAt w start reroute :=
          B.leftFrame.no_same_writer_between k hleftGap.1
            hkReroute F.close_productive
        have heqWriter : rawWriterAt w start k =
            rawWriterAt w start reroute :=
          F.same_writer.symm.trans B.leftFrame.same_writer
        exact (hdiff heqWriter).elim
      · exact .leftNested (by omega) F.order hleftGap.2
  · have hsecondK : second < k :=
      Nat.lt_trans B.second_lt_reroute hrightGap.1
    by_cases hleftSecond : left < second
    · have hdiff : rawWriterAt w start k ≠
          rawWriterAt w start third :=
        B.rightFrame.no_same_writer_between k hsecondK
          hrightGap.2 F.close_productive
      let C : RawBABAInterlacement
          w N start left second k third := {
        prior_lt_second := hleftSecond
        second_lt_reroute := hsecondK
        reroute_lt_third := hrightGap.2
        leftFrame := F
        rightFrame := B.rightFrame
        different_writers := hdiff
      }
      have hnotSmaller : ¬ C.overlap < B.overlap := by
        intro hsmaller
        exact hmin left second k third C hsmaller
      exact .rightCrossing C (Nat.le_of_not_gt hnotSmaller)
    · have hsecondLeft : second ≤ left :=
        Nat.le_of_not_gt hleftSecond
      by_cases heq : left = second
      · subst left
        have hdiff : rawWriterAt w start k ≠
            rawWriterAt w start third :=
          B.rightFrame.no_same_writer_between k hsecondK
            hrightGap.2 F.close_productive
        have heqWriter : rawWriterAt w start k =
            rawWriterAt w start third :=
          F.same_writer.symm.trans B.rightFrame.same_writer
        exact (hdiff heqWriter).elim
      · have hsecondLeftStrict : second < left := by omega
        by_cases hleftReroute : left < reroute
        · exact (hmin.excludes_crossing_frame F hsecondLeftStrict
            hleftReroute hrightGap.1).elim
        · exact .rightNested (Nat.le_of_not_gt hleftReroute)
            F.order hrightGap.2

/-- Once a productive rerouter is known to occur strictly before a selected
close, its contribution is paid, replayed, or a strictly earlier selected
event. -/
inductive RamanEarlierProductiveDisposition
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (j : Nat) : Prop
  | firstWriter (h : RawFirstWriterAt w N start j)
  | earlierReplay (h : RamanEarlierVectorReplayAt w N start j)
  | earlierSelected (h : RawSixSelectedTime C j)

theorem rawProductiveAt_before_selected_disposition
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {j k : Nat} (hjProd : RawProductiveAt w N start j)
    (hjk : j < k) (hkSelected : RawSixSelectedTime C k) :
    RamanEarlierProductiveDisposition C j := by
  classical
  by_cases hfirst : RawFirstWriterAt w N start j
  · exact .firstWriter hfirst
  by_cases hnovel : RawNovelAt w N start j
  · have Hj : RawRepeatedWriterNovelAt w N start j :=
      ⟨hjProd, hfirst, hnovel⟩
    have hjZ5 : j ≤ C.z5 := by
      have hkZ5 := hkSelected.le_z5
      omega
    exact .earlierSelected (by
      simpa [RawSixSelectedTime] using
        C.repeated_novelty_at_most_z5 hjZ5 Hj)
  · exact .earlierReplay (by
      unfold RamanEarlierVectorReplayAt
      simpa [RawNovelAt] using (Classical.not_not.mp hnovel))

/-- A selected outer close descends inside its actual last-writer frame to a
strictly earlier productive rerouter.  The position field preserves the
complete symmetric frame geometry; the disposition field pays or recursively
selects that earlier event. -/
structure RamanSelectedOuterFrameDescent
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (k left : Nat) : Type where
  selected : RawSixSelectedTime C k
  gap : BABAOuterGap prior second reroute third k
  frame : RawLastWriterFrame w N start left k
  position : RamanOuterFramePosition B k left
  inner : Nat
  opening_lt_inner : left < inner
  inner_lt_close : inner < k
  productive : RawProductiveAt w N start inner
  different_writer : rawWriterAt w start inner ≠
    rawWriterAt w start k
  disposition : RamanEarlierProductiveDisposition C inner

/-- Construction of the strict selected-close descent. -/
theorem RawBABAOverlapMinimal.selected_outer_frame_strict_descent
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third k left : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hselected : RawSixSelectedTime C k)
    (hgap : BABAOuterGap prior second reroute third k)
    (F : RawLastWriterFrame w N start left k) :
    Nonempty (RamanSelectedOuterFrameDescent C B k left) := by
  have Hk : RawRepeatedWriterNovelAt w N start k :=
    hselected.rawRepeatedWriterNovelAt
  obtain ⟨j, hleftJ, hjK, hjProd, hjDiff⟩ :=
    Hk.has_interior_rerouter hN F
  exact ⟨{
    selected := hselected
    gap := hgap
    frame := F
    position := hmin.outer_frame_position hgap F
    inner := j
    opening_lt_inner := hleftJ
    inner_lt_close := hjK
    productive := hjProd
    different_writer := hjDiff
    disposition := rawProductiveAt_before_selected_disposition
      C hjProd hjK hselected
  }⟩

/-- Final exact refinement of an arbitrary productive outer gap.  The only
novel pre-`z5` branch is a selected close equipped with strict raw-time
descent. -/
inductive RamanOuterGapStrictOutcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    (B : RawBABAInterlacement
      w N start prior second reroute third) : Prop
  | afterSelectedTail (k : Nat)
      (hgap : BABAOuterGap prior second reroute third k)
      (hprod : RawProductiveAt w N start k)
      (hlate : C.z5 < k)
  | firstWriter (k : Nat)
      (hgap : BABAOuterGap prior second reroute third k)
      (hfirst : RawFirstWriterAt w N start k)
  | earlierReplay (k : Nat)
      (hgap : BABAOuterGap prior second reroute third k)
      (hreplay : RamanEarlierVectorReplayAt w N start k)
  | selectedDescent (k left : Nat)
      (h : Nonempty (RamanSelectedOuterFrameDescent C B k left))

/-- `quietOuterGap` is therefore not a terminal constructor: it is late,
paid, replayed, or carries a strict selected-close descent. -/
theorem RawBABAOverlapMinimal.outer_gap_strict_outcome
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B)
    (hactive : BABAOuterGapHasProductive B) :
    RamanOuterGapStrictOutcome C B := by
  obtain ⟨k, hgapRaw, hprod⟩ := hactive
  have hgap : BABAOuterGap prior second reroute third k := hgapRaw
  rcases rawProductiveAt_outer_disposition C hprod with
    hlate | hfirst | hreplay | hselected
  · exact .afterSelectedTail k hgap hprod hlate
  · exact .firstWriter k hgap hfirst
  · exact .earlierReplay k hgap hreplay
  · have Hk : RawRepeatedWriterNovelAt w N start k :=
      hselected.rawRepeatedWriterNovelAt
    obtain ⟨left, F⟩ := Hk.last_writer_frame
    exact .selectedDescent k left
      (hmin.selected_outer_frame_strict_descent
        hN C hselected hgap F)

end GeneralN
