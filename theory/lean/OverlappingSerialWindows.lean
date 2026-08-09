import OverlappingFiveWindowReduction
import GlobalSerialContinuation

/-!
# Two overlapping serial windows force a shared strict suffix descent

Suppose six chronological repeated-writer novelties give the two overlapping
five-event windows

* `z0,z1,z2,z3,z4`, and
* `z1,z2,z3,z4,z5`,

and both five-frame outcomes are serial.  Each window then produces an actual
completed caller return.  The two absolute return times are comparable.

This file records the useful unconditional consequence of that comparison.
After ordering the returns, one of the selected global framed novelties opens
after *both* returns.  It therefore rebases to a repeated-writer novelty in
both returned suffixes.  The later returned configuration is reached exactly
from the earlier one, and the shared closing time strictly decreases under
each positive return (strictly again between suffixes when the return times
differ).

This is a genuine well-founded descent extracted from the raw track dynamics.
It is not a four-state tail theorem and does not close `StateLaw` by itself.
-/

namespace GeneralN

/-- If two absolute times reach two configurations, the later configuration
is reached from the earlier one after exactly the difference of the times. -/
private theorem stepN_between_reached
    {w : Wiring} {start earlier later : Nat × Tongues}
    {i j : Nat}
    (hij : i ≤ j)
    (hi : stepN w i start = some earlier)
    (hj : stepN w j start = some later) :
    stepN w (j - i) earlier = some later := by
  have hsplit := stepN_add w i (j - i) start
  rw [hi] at hsplit
  simp only [Option.bind_some] at hsplit
  rw [Nat.add_sub_of_le hij, hj] at hsplit
  exact hsplit.symm

/-- Package a selected later frame as a framed novelty, so that it can be
rebased at either completed return. -/
private def selectedFramedNovelty
    {w : Wiring} {N firstClose : Nat} {start : Nat × Tongues}
    (S : RawSelectedLaterSerialFrame w N start firstClose) :
    RawFramedNovelty w N start where
  openTime := S.openTime
  rerouteTime := S.rerouteTime
  closeTime := S.closeTime
  event := S.event
  frame := S.frame

/-- Select the actual later serial frame while retaining which one of the
four canonical closing events it is.  The common openings in
`RawOverlappingFiveWindowReduction` make this usable in both windows. -/
private theorem select_indexed_later_frame
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (H1 : RawRepeatedWriterNovelAt w N start z1)
    (H2 : RawRepeatedWriterNovelAt w N start z2)
    (H3 : RawRepeatedWriterNovelAt w N start z3)
    (H4 : RawRepeatedWriterNovelAt w N start z4)
    {a1 q1 a2 q2 a3 q3 a4 q4 : Nat}
    (F1 : RawNovelClosingFrame w N start a1 q1 z1)
    (F2 : RawNovelClosingFrame w N start a2 q2 z2)
    (F3 : RawNovelClosingFrame w N start a3 q3 z3)
    (F4 : RawNovelClosingFrame w N start a4 q4 z4)
    (hserial : FiveFrameSerialBreak z0 a1 a2 a3 a4) :
    ∃ S : RawSelectedLaterSerialFrame w N start z0,
      S.closeTime = z1 ∨ S.closeTime = z2 ∨
        S.closeTime = z3 ∨ S.closeTime = z4 := by
  rcases hserial with h1 | h2 | h3 | h4
  · exact ⟨{
      openTime := a1
      rerouteTime := q1
      closeTime := z1
      after_first_close := h1
      event := H1
      frame := F1
    }, Or.inl rfl⟩
  · exact ⟨{
      openTime := a2
      rerouteTime := q2
      closeTime := z2
      after_first_close := h2
      event := H2
      frame := F2
    }, Or.inr (Or.inl rfl)⟩
  · exact ⟨{
      openTime := a3
      rerouteTime := q3
      closeTime := z3
      after_first_close := h3
      event := H3
      frame := F3
    }, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨{
      openTime := a4
      rerouteTime := q4
      closeTime := z4
      after_first_close := h4
      event := H4
      frame := F4
    }, Or.inr (Or.inr (Or.inr rfl))⟩

/-- Forget the aligned frame data while retaining the canonical first-six
event sequence and all five no-gap facts. -/
private def RawOverlappingFiveWindowReduction.consecutiveEvents
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) :
    RawConsecutiveSixEvents w N start where
  z0 := R.z0
  z1 := R.z1
  z2 := R.z2
  z3 := R.z3
  z4 := R.z4
  z5 := R.z5
  order01 := R.order01
  order12 := R.order12
  order23 := R.order23
  order34 := R.order34
  order45 := R.order45
  event0 := R.event0
  event1 := R.event1
  event2 := R.event2
  event3 := R.event3
  event4 := R.event4
  event5 := R.event5
  first0 := R.first0
  no_event01 := R.no_event01
  no_event12 := R.no_event12
  no_event23 := R.no_event23
  no_event34 := R.no_event34
  no_event45 := R.no_event45

/-- The parent no-gap theorem identifies every repeated-writer novelty through
`z5` as one of the canonical first six events.  In particular this applies
to every post-return repeated novelty that still lies in the alleged
six-event counterexample. -/
theorem RawOverlappingFiveWindowReduction.repeated_novelty_at_most_z5
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    {k : Nat}
    (hk : k ≤ R.z5)
    (Hk : RawRepeatedWriterNovelAt w N start k) :
    k = R.z0 ∨ k = R.z1 ∨ k = R.z2 ∨
      k = R.z3 ∨ k = R.z4 ∨ k = R.z5 := by
  have hlo : R.z0 ≤ k := by
    apply Classical.byContradiction
    intro hnot
    exact R.first0 k (by omega) Hk
  have hselected := R.consecutiveEvents.repeated_event_eq_selected Hk hlo hk
  simpa [RawOverlappingFiveWindowReduction.consecutiveEvents] using hselected

/-- A serial charge resolution rooted at the first repeated novelty cannot
take its recursive `step` branch: such a branch would exhibit an earlier
repeated novelty, contradicting `first0`. -/
theorem RawOverlappingFiveWindowReduction.first_serial_resolution_is_leaf
    {w : Wiring} {N horizon : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (S : RawSerialChargeResolution w N start horizon R.z0) :
    (∃ A : RawSerialReturnAccounting w N start horizon R.z0,
        RawFirstWriterAt w N start A.repeatTime ∧
        restrictedTonguesAt w N start A.returnTime ∈
          rawFirstWriterHistory w N start horizon) ∨
      (∃ A : RawSerialReturnAccounting w N start horizon R.z0,
        restrictedTonguesAt w N start A.returnTime ∈
          (List.range (A.repeatTime + 1)).map
            (restrictedTonguesAt w N start)) := by
  cases S with
  | first A writer paid =>
      exact Or.inl ⟨A, writer, paid⟩
  | replay A seen =>
      exact Or.inr ⟨A, seen⟩
  | step A earlier _tail =>
      exact (R.first0 A.repeatTime A.repeat_before_close earlier).elim

/-- The no-gap facts bound a serial charge resolution rooted at the second
repeated novelty to depth one.  A recursive branch can only land at the
first canonical event `z0`, whose own resolution is necessarily a leaf by
`first_serial_resolution_is_leaf`. -/
theorem RawOverlappingFiveWindowReduction.second_serial_resolution_depth_one
    {w : Wiring} {N horizon : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (S : RawSerialChargeResolution w N start horizon R.z1) :
    (∃ A : RawSerialReturnAccounting w N start horizon R.z1,
        RawFirstWriterAt w N start A.repeatTime ∧
        restrictedTonguesAt w N start A.returnTime ∈
          rawFirstWriterHistory w N start horizon) ∨
      (∃ A : RawSerialReturnAccounting w N start horizon R.z1,
        restrictedTonguesAt w N start A.returnTime ∈
          (List.range (A.repeatTime + 1)).map
            (restrictedTonguesAt w N start)) ∨
      (∃ A : RawSerialReturnAccounting w N start horizon R.z1,
        A.repeatTime = R.z0 ∧
        ((∃ A0 : RawSerialReturnAccounting w N start horizon R.z0,
            RawFirstWriterAt w N start A0.repeatTime ∧
            restrictedTonguesAt w N start A0.returnTime ∈
              rawFirstWriterHistory w N start horizon) ∨
          (∃ A0 : RawSerialReturnAccounting w N start horizon R.z0,
            restrictedTonguesAt w N start A0.returnTime ∈
              (List.range (A0.repeatTime + 1)).map
                (restrictedTonguesAt w N start)))) := by
  cases S with
  | first A writer paid =>
      exact Or.inl ⟨A, writer, paid⟩
  | replay A seen =>
      exact Or.inr (Or.inl ⟨A, seen⟩)
  | step A earlier tail =>
      have hrepeatLtZ1 : A.repeatTime < R.z1 :=
        A.repeat_before_close
      have h12 : R.z1 < R.z2 := R.order12
      have h23 : R.z2 < R.z3 := R.order23
      have h34 : R.z3 < R.z4 := R.order34
      have h45 : R.z4 < R.z5 := R.order45
      have hrepeatLeZ5 :=
        Nat.le_trans (Nat.le_of_lt hrepeatLtZ1)
          (Nat.le_trans (Nat.le_of_lt h12)
            (Nat.le_trans (Nat.le_of_lt h23)
              (Nat.le_trans (Nat.le_of_lt h34)
                (Nat.le_of_lt h45))))
      have hselected := R.repeated_novelty_at_most_z5
        (k := A.repeatTime) hrepeatLeZ5 earlier
      have heq : A.repeatTime = R.z0 := by
        rcases hselected with h0 | h1 | h2 | h3 | h4 | h5
        · exact h0
        · omega
        · omega
        · omega
        · omega
        · omega
      have tail0 :
          RawSerialChargeResolution w N start horizon R.z0 := by
        simpa [heq] using tail
      exact Or.inr (Or.inr
        ⟨A, heq, R.first_serial_resolution_is_leaf tail0⟩)

/-- Both serial windows produce actual finite charge resolutions.  Combined
with the two eliminators above, the head resolution is a leaf and the tail
resolution has at most the single canonical recursive close `z1 → z0`. -/
theorem RawOverlappingFiveWindowReduction.serial_serial_charge_resolutions
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start)
    (hhead : FiveFrameSerialBreak R.z0 R.a1 R.a2 R.a3 R.a4)
    (htail : FiveFrameSerialBreak R.z1 R.a2 R.a3 R.a4 R.a5) :
    Nonempty (RawSerialChargeResolution w N start (R.z5 + 1) R.z0) ∧
      Nonempty (RawSerialChargeResolution w N start (R.z5 + 1) R.z1) := by
  obtain ⟨SH, _hSHIndex⟩ := select_indexed_later_frame
    R.event1 R.event2 R.event3 R.event4
    R.frame1 R.frame2 R.frame3 R.frame4 hhead
  obtain ⟨ST, _hSTIndex⟩ := select_indexed_later_frame
    R.event2 R.event3 R.event4 R.event5
    R.frame2 R.frame3 R.frame4 R.frame5 htail
  have h01 : R.z0 < R.z1 := R.order01
  have h12 : R.z1 < R.z2 := R.order12
  have h23 : R.z2 < R.z3 := R.order23
  have h34 : R.z3 < R.z4 := R.order34
  have h45 : R.z4 < R.z5 := R.order45
  obtain ⟨headResolution⟩ := R.event0.resolve_serial_charge
    (horizon := R.z5 + 1) hN hentry (by omega)
      SH.event SH.frame SH.after_first_close
  obtain ⟨tailResolution⟩ := R.event1.resolve_serial_charge
    (horizon := R.z5 + 1) hN hentry (by omega)
      ST.event ST.frame ST.after_first_close
  exact ⟨⟨headResolution⟩, ⟨tailResolution⟩⟩

/-- **Unconditional serial/serial overlap descent.**

Both overlapping serial windows produce concrete completed returns `H` and
`T`.  If `H` returns first, the novelty selected by `T` survives in both
returned suffixes.  If `T` returns first, the novelty selected by `H` does.
In either branch:

* the later returned configuration is reached exactly from the earlier one;
* the same global framed novelty rebases in both suffixes;
* both local closing times are strictly smaller than the global close; and
* a strict separation of return times gives a second strict decrease.

The result has no continuation hypothesis, finite-`N` enumeration, or
certificate wrapper. -/
theorem RawOverlappingFiveWindowReduction.serial_serial_nested_descent
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start)
    (hhead : FiveFrameSerialBreak R.z0 R.a1 R.a2 R.a3 R.a4)
    (htail : FiveFrameSerialBreak R.z1 R.a2 R.a3 R.a4 R.a5) :
    ∃ H : RawGlobalSerialContinuation w N start R.z0,
      ∃ T : RawGlobalSerialContinuation w N start R.z1,
        ∃ SH : RawSelectedLaterSerialFrame w N start R.z0,
          ∃ ST : RawSelectedLaterSerialFrame w N start R.z1,
            (SH.closeTime = R.z1 ∨ SH.closeTime = R.z2 ∨
              SH.closeTime = R.z3 ∨ SH.closeTime = R.z4) ∧
            (ST.closeTime = R.z2 ∨ ST.closeTime = R.z3 ∨
              ST.closeTime = R.z4 ∨ ST.closeTime = R.z5) ∧
            ((H.returnTime ≤ T.returnTime ∧
              stepN w (T.returnTime - H.returnTime) H.returned =
                some T.returned ∧
              ∃ FH : RawFramedNovelty w N H.returned,
                ∃ FT : RawFramedNovelty w N T.returned,
                  FH.closeTime = ST.closeTime - H.returnTime ∧
                  FT.closeTime = ST.closeTime - T.returnTime ∧
                  FH.closeTime < ST.closeTime ∧
                  FT.closeTime < ST.closeTime ∧
                  FT.closeTime ≤ FH.closeTime ∧
                  (H.returnTime < T.returnTime →
                    FT.closeTime < FH.closeTime)) ∨
            (T.returnTime ≤ H.returnTime ∧
              stepN w (H.returnTime - T.returnTime) T.returned =
                some H.returned ∧
              ∃ FT : RawFramedNovelty w N T.returned,
                ∃ FH : RawFramedNovelty w N H.returned,
                  FT.closeTime = SH.closeTime - T.returnTime ∧
                  FH.closeTime = SH.closeTime - H.returnTime ∧
                  FT.closeTime < SH.closeTime ∧
                  FH.closeTime < SH.closeTime ∧
                  FH.closeTime ≤ FT.closeTime ∧
                  (T.returnTime < H.returnTime →
                    FH.closeTime < FT.closeTime))) := by
  obtain ⟨H⟩ := five_serial_novelties_supply_global_continuation
    hN hentry
      R.event0 R.event1 R.event2 R.event3 R.event4
      R.frame0 R.frame1 R.frame2 R.frame3 R.frame4 hhead
  obtain ⟨T⟩ := five_serial_novelties_supply_global_continuation
    hN hentry
      R.event1 R.event2 R.event3 R.event4 R.event5
      R.frame1 R.frame2 R.frame3 R.frame4 R.frame5 htail
  obtain ⟨SH, hSHIndex⟩ := select_indexed_later_frame
    R.event1 R.event2 R.event3 R.event4
    R.frame1 R.frame2 R.frame3 R.frame4 hhead
  obtain ⟨ST, hSTIndex⟩ := select_indexed_later_frame
    R.event2 R.event3 R.event4 R.event5
    R.frame2 R.frame3 R.frame4 R.frame5 htail
  refine ⟨H, T, SH, ST, hSHIndex, hSTIndex, ?_⟩
  by_cases hHT : H.returnTime ≤ T.returnTime
  · left
    have hHBeforeTailOpen : H.returnTime ≤ ST.openTime :=
      Nat.le_trans H.return_before_first_close
        (Nat.le_trans (Nat.le_of_lt R.order01)
          ST.after_first_close)
    have hTBeforeTailOpen : T.returnTime ≤ ST.openTime :=
      Nat.le_trans T.return_before_first_close ST.after_first_close
    let F := selectedFramedNovelty ST
    obtain ⟨FH, hcloseH, _hopenH⟩ :=
      F.rebase hHBeforeTailOpen H.reaches_return hN
    obtain ⟨FT, hcloseT, _hopenT⟩ :=
      F.rebase hTBeforeTailOpen T.reaches_return hN
    have htransition :
        stepN w (T.returnTime - H.returnTime) H.returned =
          some T.returned :=
      stepN_between_reached hHT H.reaches_return T.reaches_return
    have hHLeClose : H.returnTime ≤ ST.closeTime :=
      Nat.le_trans hHBeforeTailOpen
        (Nat.le_of_lt ST.frame.outer.order)
    have hTLeClose : T.returnTime ≤ ST.closeTime :=
      Nat.le_trans hTBeforeTailOpen
        (Nat.le_of_lt ST.frame.outer.order)
    have hcloseH' :
        FH.closeTime = ST.closeTime - H.returnTime := by
      simpa [F, selectedFramedNovelty] using hcloseH
    have hcloseT' :
        FT.closeTime = ST.closeTime - T.returnTime := by
      simpa [F, selectedFramedNovelty] using hcloseT
    have hHPositive : 0 < H.returnTime := H.return_positive
    have hTPositive : 0 < T.returnTime := T.return_positive
    refine ⟨hHT, htransition, FH, FT, hcloseH', hcloseT', ?_, ?_, ?_, ?_⟩
    · rw [hcloseH']
      omega
    · rw [hcloseT']
      omega
    · rw [hcloseT', hcloseH']
      omega
    · intro hstrict
      rw [hcloseT', hcloseH']
      omega
  · right
    have hTH : T.returnTime ≤ H.returnTime := by omega
    have hHBeforeHeadOpen : H.returnTime ≤ SH.openTime :=
      Nat.le_trans H.return_before_first_close SH.after_first_close
    have hTBeforeHeadOpen : T.returnTime ≤ SH.openTime :=
      Nat.le_trans hTH hHBeforeHeadOpen
    let F := selectedFramedNovelty SH
    obtain ⟨FT, hcloseT, _hopenT⟩ :=
      F.rebase hTBeforeHeadOpen T.reaches_return hN
    obtain ⟨FH, hcloseH, _hopenH⟩ :=
      F.rebase hHBeforeHeadOpen H.reaches_return hN
    have htransition :
        stepN w (H.returnTime - T.returnTime) T.returned =
          some H.returned :=
      stepN_between_reached hTH T.reaches_return H.reaches_return
    have hTLeClose : T.returnTime ≤ SH.closeTime :=
      Nat.le_trans hTBeforeHeadOpen
        (Nat.le_of_lt SH.frame.outer.order)
    have hHLeClose : H.returnTime ≤ SH.closeTime :=
      Nat.le_trans hHBeforeHeadOpen
        (Nat.le_of_lt SH.frame.outer.order)
    have hcloseT' :
        FT.closeTime = SH.closeTime - T.returnTime := by
      simpa [F, selectedFramedNovelty] using hcloseT
    have hcloseH' :
        FH.closeTime = SH.closeTime - H.returnTime := by
      simpa [F, selectedFramedNovelty] using hcloseH
    have hTPositive : 0 < T.returnTime := T.return_positive
    have hHPositive : 0 < H.returnTime := H.return_positive
    refine ⟨hTH, htransition, FT, FH, hcloseT', hcloseH', ?_, ?_, ?_, ?_⟩
    · rw [hcloseT']
      omega
    · rw [hcloseH']
      omega
    · rw [hcloseH', hcloseT']
      omega
    · intro hstrict
      rw [hcloseH', hcloseT']
      omega

end GeneralN
