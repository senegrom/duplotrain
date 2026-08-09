import RamanGapProductiveRefinement
import SelectedSupportContactClosure

/-!
# Strict descent for the Raman quiet inner replay

The least quiet frame left by `RamanGapProductiveRefinement` closes by
replaying its strictly earlier opening vector.  This file records the two
time-sensitive consequences needed by the canonical six-event argument:

* the quiet close is not any of the selected events `z0, ..., z5`; and
* if the close occurs by `z5`, its post-vector is either paid first-writer
  history or the post-vector of a strictly earlier selected event.

There is no eventual-tail or compatibility hypothesis here.
-/

namespace GeneralN

/-- A quiet inner replay cannot close at one of the canonical selected
repeated-writer novelties: every selected event is novel, while the replay
close is not. -/
theorem RamanQuietInnerReplay.close_not_selected
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (C : RawOverlappingFiveWindowReduction w N start)
    (R : RamanQuietInnerReplay B) :
    ¬ RawSixSelectedTime C R.closing := by
  intro hselected
  rcases hselected with h0 | h1 | h2 | h3 | h4 | h5
  · exact R.close_not_novel (by simpa [h0] using C.event0.2.2)
  · exact R.close_not_novel (by simpa [h1] using C.event1.2.2)
  · exact R.close_not_novel (by simpa [h2] using C.event2.2.2)
  · exact R.close_not_novel (by simpa [h3] using C.event3.2.2)
  · exact R.close_not_novel (by simpa [h4] using C.event4.2.2)
  · exact R.close_not_novel (by simpa [h5] using C.event5.2.2)

/-- If a quiet inner replay closes within the selected six-event window, its
post-vector is already paid first-writer history, or it is exactly the
post-vector of a strictly earlier selected event.  The strict inequality is
obtained by classifying the *opening* at horizon `opening`, then transporting
through the replay equality; classifying at `z5` would lose this descent. -/
theorem RamanQuietInnerReplay.close_post_paid_or_earlier_selected
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (C : RawOverlappingFiveWindowReduction w N start)
    (R : RamanQuietInnerReplay B)
    (hclose : R.closing ≤ C.z5) :
    restrictedTonguesAt w N start (R.closing + 1) ∈
        rawFirstWriterHistory w N start (C.z5 + 1) ∨
      ∃ k, RawSixSelectedTime C k ∧ k < R.closing ∧
        restrictedTonguesAt w N start (R.closing + 1) =
          restrictedTonguesAt w N start (k + 1) := by
  have hopenClose : R.opening < R.closing :=
    R.opening_lt_closing
  have hopenHorizon : R.opening ≤ C.z5 + 1 := by
    omega
  have hcovered := restrictedTonguesAt_mem_finite_writer_cover
    w N start R.opening R.opening (Nat.le_refl _)
  rcases List.mem_append.mp hcovered with hhistory | hrepeated
  · exact Or.inl (by
      rw [R.replay]
      exact rawFirstWriterHistory_mono hopenHorizon hhistory)
  · obtain ⟨k, hk, hvector⟩ := List.mem_map.mp hrepeated
    have hkData := mem_rawRepeatedWriterNovelTimes_iff.mp hk
    have hkOpening : k < R.opening := hkData.1
    have Hk : RawRepeatedWriterNovelAt w N start k := hkData.2
    have hkZ5 : k ≤ C.z5 := by
      omega
    refine Or.inr ⟨k, ?_, by omega, ?_⟩
    · simpa [RawSixSelectedTime] using
        C.repeated_novelty_at_most_z5 hkZ5 Hk
    · exact R.replay.trans hvector.symm

/-- Exact disposition of a quiet inner replay relative to the canonical
six-event window.  A close after `z5` cannot affect that selected tail; every
earlier close is paid or descends to a strictly earlier selected event. -/
inductive RamanInnerReplayDisposition
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (R : RamanQuietInnerReplay B) : Prop
  | afterSelectedTail (h : C.z5 < R.closing)
  | paidHistory
      (h : restrictedTonguesAt w N start (R.closing + 1) ∈
        rawFirstWriterHistory w N start (C.z5 + 1))
  | earlierSelected (k : Nat)
      (hselected : RawSixSelectedTime C k)
      (hearlier : k < R.closing)
      (hreplay : restrictedTonguesAt w N start (R.closing + 1) =
        restrictedTonguesAt w N start (k + 1))

/-- Unconditional strict-descent classification of the inner replay. -/
theorem RamanQuietInnerReplay.selected_tail_disposition
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (C : RawOverlappingFiveWindowReduction w N start)
    (R : RamanQuietInnerReplay B) :
    RamanInnerReplayDisposition C R := by
  by_cases hclose : R.closing ≤ C.z5
  · rcases R.close_post_paid_or_earlier_selected C hclose with
      hpaid | ⟨k, hselected, hearlier, hreplay⟩
    · exact .paidHistory hpaid
    · exact .earlierSelected k hselected hearlier hreplay
  · exact .afterSelectedTail (by omega)

end GeneralN
