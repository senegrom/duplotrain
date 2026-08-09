import SelectedTripleSharpClosure

/-!
# Transport-preserving recursion toward the Mellit/Raman top-level closure

The selected-frame strong induction finds an earlier first writer or replay,
but that fact alone does not identify the selected close vector. This module
retains the missing dynamical transport through the last rerouter. It also
records, directly against the canonical six-event history, that a selected
tail close is not paid merely because such an interior event exists.

These facts are stated over raw Wiring/stepN dynamics for general N.
-/

namespace GeneralN

/-- The represented state immediately before a framed close is the state
immediately after its last interior productive rerouter. -/
theorem RawLastRerouter.preclose_vector_eq_after
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {left reroute right : Nat}
    (R : RawLastRerouter w N start left reroute right)
    (F : RawLastWriterFrame w N start left right) :
    restrictedTonguesAt w N start right =
      restrictedTonguesAt w N start (reroute + 1) := by
  have hpostExists :=
    Option.isSome_iff_exists.mp F.close_productive.1
  cases hpostExists with
  | intro post hpost =>
    have hbeforeExists := stepN_prefix_some
      (d := right) (K := right + 1) (by omega) hpost
    cases hbeforeExists with
    | intro before hbefore =>
      let span := right - (reroute + 1)
      have hrr : reroute < right := R.inside_right
      have hsum : reroute + 1 + span = right := by
        dsimp [span]
        omega
      have hquiet : forall j,
          reroute + 1 <= j -> j < reroute + 1 + span ->
          Not (RawProductiveAt w N start j) := by
        intro j hjLeft hjRight
        apply R.quiet_after j <;> omega
      have hstable := restrictedTonguesAt_eq_of_quiet_interval
        (first := reroute + 1) (span := span) (finish := before)
        (by simpa [hsum] using hbefore) hquiet
      simpa [hsum] using hstable

/-- Exact vector transport through a selected frame: its close post-vector
is one flip of the vector immediately after the last rerouter. -/
theorem RawLastRerouter.close_post_transport
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    {left reroute right : Nat}
    (R : RawLastRerouter w N start left reroute right)
    (F : RawLastWriterFrame w N start left right) :
    restrictedTonguesAt w N start (right + 1) =
      VectorCount.restrict N
        (flipAt (tonguesAt w start (reroute + 1))
          (rawWriterAt w start right)) := by
  calc
    restrictedTonguesAt w N start (right + 1) =
        VectorCount.restrict N
          (flipAt (tonguesAt w start right)
            (rawWriterAt w start right)) :=
      rawProductiveAt_restricted_flip hN F.close_productive
    _ = VectorCount.restrict N
          (flipAt (tonguesAt w start (reroute + 1))
            (rawWriterAt w start right)) :=
      restrict_flipAt_congr (R.preclose_vector_eq_after F)

/-- Every selected close has a last rerouter and the exact one-flip transport
from that rerouter. This is the proof-relevant recursion datum that the
coarser SelectedFramePaidClosure does not retain. -/
theorem RawSixSelectedTime.last_rerouter_transport
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {close opening : Nat}
    (hselected : RawSixSelectedTime C close)
    (F : RawLastWriterFrame w N start opening close) :
    exists reroute,
      And (RawLastRerouter w N start opening reroute close)
        (And
          (Ne (rawWriterAt w start reroute) (rawWriterAt w start close))
          (restrictedTonguesAt w N start (close + 1) =
            VectorCount.restrict N
              (flipAt (tonguesAt w start (reroute + 1))
                (rawWriterAt w start close)))) := by
  have Hclose := hselected.rawRepeatedWriterNovelAt
  have htransport := Hclose.has_last_rerouter hN F
  cases htransport with
  | intro reroute hrest =>
    cases hrest with
    | intro R hdiff =>
      exact Exists.intro reroute
        (And.intro R
          (And.intro hdiff (R.close_post_transport hN F)))

/-- A canonical selected close is never hidden in first-writer history.
This remains true even when SelectedFramePaidClosure has found an interior
first writer or replay. -/
theorem RawSixSelectedTime.post_not_mem_first_history
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {close : Nat}
    (hselected : RawSixSelectedTime C close) :
    Not (List.Mem (restrictedTonguesAt w N start (close + 1))
      (rawFirstWriterHistory w N start (C.z5 + 1))) := by
  exact repeatedWriterPost_not_mem_firstHistory hN
    (mem_rawRepeatedWriterNovelTimes_iff.mpr
      (And.intro (by
        have hcloseZ5 := hselected.le_z5
        omega) hselected.rawRepeatedWriterNovelAt))

/-- Tail selected times, excluding event zero. -/
def RawSixTailSelectedTime
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (close : Nat) : Prop :=
  Or (close = C.z1) (Or (close = C.z2) (Or (close = C.z3)
    (Or (close = C.z4) (close = C.z5))))

/-- Every tail selected time is a canonical selected time. -/
theorem RawSixTailSelectedTime.selected
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {close : Nat}
    (htail : RawSixTailSelectedTime C close) :
    RawSixSelectedTime C close := by
  cases htail with
  | inl h1 =>
    subst close
    exact Or.inr (Or.inl rfl)
  | inr hrest1 =>
    cases hrest1 with
    | inl h2 =>
      subst close
      exact Or.inr (Or.inr (Or.inl rfl))
    | inr hrest2 =>
      cases hrest2 with
      | inl h3 =>
        subst close
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | inr hrest3 =>
        cases hrest3 with
        | inl h4 =>
          subst close
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        | inr h5 =>
          subst close
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- No tail selected close is paid by the exact history used by
noTailFourCover: not by first-writer history and not by event zero. -/
theorem RawSixTailSelectedTime.post_not_paid
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {close : Nat}
    (htail : RawSixTailSelectedTime C close) :
    Not (List.Mem (restrictedTonguesAt w N start (close + 1))
      (rawFirstWriterHistory w N start (C.z5 + 1) ++
        [restrictedTonguesAt w N start (C.z0 + 1)])) := by
  intro hmem
  have hsplit := List.mem_append.mp hmem
  cases hsplit with
  | inl hfirst =>
    exact htail.selected.post_not_mem_first_history hN hfirst
  | inr hzero =>
    have hzeroEq := List.mem_singleton.mp hzero
    have o01 : C.z0 < C.z1 := C.order01
    have o12 : C.z1 < C.z2 := C.order12
    have o23 : C.z2 < C.z3 := C.order23
    have o34 : C.z3 < C.z4 := C.order34
    have o45 : C.z4 < C.z5 := C.order45
    cases htail with
    | inl h1 =>
      subst close
      exact C.event1.2.2.post_ne_earlier (by omega) hzeroEq
    | inr hrest1 =>
      cases hrest1 with
      | inl h2 =>
        subst close
        exact C.event2.2.2.post_ne_earlier (by omega) hzeroEq
      | inr hrest2 =>
        cases hrest2 with
        | inl h3 =>
          subst close
          exact C.event3.2.2.post_ne_earlier (by omega) hzeroEq
        | inr hrest3 =>
          cases hrest3 with
          | inl h4 =>
            subst close
            exact C.event4.2.2.post_ne_earlier (by omega) hzeroEq
          | inr h5 =>
            subst close
            exact C.event5.2.2.post_ne_earlier (by omega) hzeroEq

/-- The coarser selected-frame result is not itself a payment of the close.
Any valid top-level recursion must additionally use the transport theorem
above (or stronger physical retrace data). -/
theorem SelectedFramePaidClosure.selected_tail_close_still_unpaid
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {close : Nat}
    (_paid : SelectedFramePaidClosure C close)
    (htail : RawSixTailSelectedTime C close) :
    Not (List.Mem (restrictedTonguesAt w N start (close + 1))
      (rawFirstWriterHistory w N start (C.z5 + 1) ++
        [restrictedTonguesAt w N start (C.z0 + 1)])) :=
  htail.post_not_paid hN

end GeneralN
