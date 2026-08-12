import FirstWriterRetraceFree
import OverlappingFiveWindowReduction
import SharpCertificateClosure
import SixEventReduction

/-!
# Sharp consequences of the raw six-event reduction

This file works only with the raw `Wiring`/`stepN` dynamics.  It records two
facts needed by a coefficient-one proof.

First, a completed retrace turned by a globally first writer really is free:
all of its positive-depth vectors are in `rawFirstWriterHistory`.  But this
does **not** make a later repeated-novel close historical.  Such a close is,
by its defining global novelty, different from the first-writer contact
vector.  Consequently the remaining sharp argument must force that close
into the bounded two-reflector tail; equality with the first-writer
post-vector is not an available accounting shortcut.

Second, in the serial branch selected by `RawSixEventReduction`, the exact
caller return occurs at a positive time and strictly decreases the local
time of a certified later repeated novelty.  The later last-writer frame and
its novelty both survive in the actually reached suffix configuration.  This
is an unconditional, well-founded reduction of the raw serial obstruction,
not a conditional repair certificate.
-/

namespace GeneralN

theorem repeated_novel_close_not_zero_first_writer_cover
    {w : Wiring} {N horizon close : Nat}
    {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (Hclose : RawRepeatedWriterNovelAt w N start close)
    (hcloseHorizon : close < horizon) :
    ¬ NoveltyCoverOn w N start [close + 1]
        (rawFirstWriterHistory w N start horizon) 0 := by
  intro hcover
  obtain ⟨fresh, hfreshLength, hmem⟩ := hcover
  have hfresh : fresh = [] := by
    cases fresh with
    | nil => rfl
    | cons head tail => simp at hfreshLength
  subst fresh
  have hhistory :
      restrictedTonguesAt w N start (close + 1) ∈
        rawFirstWriterHistory w N start horizon := by
    simpa using hmem (close + 1) (by simp)
  have hcloseMem :
      close ∈ rawRepeatedWriterNovelTimes w N start horizon :=
    mem_rawRepeatedWriterNovelTimes_iff.mpr
      ⟨hcloseHorizon, Hclose⟩
  exact repeatedWriterPost_not_mem_firstHistory
    hN hcloseMem hhistory

private theorem RawOverlappingFiveWindowReduction.prefix_through_second_mem
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    {time : Nat} (htime : time ≤ R.z1) :
    restrictedTonguesAt w N start time ∈
      rawFirstWriterHistory w N start (R.z5 + 1) ++
        [restrictedTonguesAt w N start (R.z0 + 1)] := by
  let C : RawConsecutiveSixEvents w N start := {
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
  }
  have o01 : R.z0 < R.z1 := R.order01
  have o12 : R.z1 < R.z2 := R.order12
  have o23 : R.z2 < R.z3 := R.order23
  have o34 : R.z3 < R.z4 := R.order34
  have o45 : R.z4 < R.z5 := R.order45
  have hcovered := restrictedTonguesAt_mem_finite_writer_cover
    w N start (R.z5 + 1) time (by omega)
  rcases List.mem_append.mp hcovered with hhistory | hrepeated
  · exact List.mem_append_left _ hhistory
  · obtain ⟨k, hk, hvector⟩ := List.mem_map.mp hrepeated
    have hkData := mem_rawRepeatedWriterNovelTimes_iff.mp hk
    have Hk : RawRepeatedWriterNovelAt w N start k := hkData.2
    by_cases hk0 : k = R.z0
    · subst k
      apply List.mem_append_right
      simp only [List.mem_singleton]
      exact hvector.symm
    · by_cases hkBefore0 : k < R.z0
      · exact (R.first0 k hkBefore0 Hk).elim
      · have hlo : C.z0 ≤ k := by
          dsimp [C]
          omega
        have hhi : k ≤ C.z5 := by
          dsimp [C]
          omega
        have hselected := C.repeated_event_eq_selected Hk hlo hhi
        dsimp [C] at hselected
        rcases hselected with h0 | h1 | h2 | h3 | h4 | h5
        · exact (hk0 (by simpa [C] using h0)).elim
        · subst k
          exact (Hk.2.2.post_ne_earlier (by omega) hvector).elim
        · subst k
          exact (Hk.2.2.post_ne_earlier (by omega) hvector).elim
        · subst k
          exact (Hk.2.2.post_ne_earlier (by omega) hvector).elim
        · subst k
          exact (Hk.2.2.post_ne_earlier (by omega) hvector).elim
        · subst k
          exact (Hk.2.2.post_ne_earlier (by omega) hvector).elim

/-- **The tail-serial escape has no unselected repeated-novel case.**

For the serial window `z1,...,z5`, take the first productive event after the
completed caller return.  If it is a first writer, or its post-vector is not
novel, that vector is already in first-writer history plus event zero.  In
the remaining case it is a repeated novelty; consecutiveness forces it to be
exactly `z0` or `z1`.  The crossing-caller theorem then exposes a strictly
earlier reroute, which is itself either a first writer or the close of a
strictly interlaced last-writer frame.

This consumes the actual selected-event outcome.  The only serial residual
is the displayed old-side interlacement; there is no arbitrary escape time
left in the conclusion. -/
theorem RawOverlappingFiveWindowReduction.tail_serial_escape_sharp_outcome
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start)
    (hserial : FiveFrameSerialBreak
      R.z1 R.a2 R.a3 R.a4 R.a5) :
    ∃ escape,
      escape ≤ R.z1 ∧
      RawProductiveAt w N start escape ∧
      (restrictedTonguesAt w N start (escape + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
        ((escape = R.z0 ∨ escape = R.z1) ∧
          ∃ left reroute,
            RawLastWriterFrame w N start left escape ∧
            left < reroute ∧
            reroute < escape ∧
            RawProductiveAt w N start reroute ∧
            rawWriterAt w start reroute ≠ rawWriterAt w start escape ∧
            (RawFirstWriterAt w N start reroute ∨
              ∃ prior,
                RawLastWriterFrame w N start prior reroute ∧
                prior < left))) := by
  obtain ⟨_g, _base, _oldEntry, _mouthState, q, old, settled,
      _edge, repeatTime, caller, _hbefore, _hcaller, _hsimple,
      _hgrooved, _hcallerLe, _hedge, hrepeat, _hopen,
      _hrepeatBeforeClose, hreturnBeforeClose, _hcontact,
      _hlocalReturn, hpointwise, _hcover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry
      R.event1 R.event2 R.event3 R.event4 R.event5
      R.frame1 R.frame2 R.frame3 R.frame4 R.frame5 hserial
  let span := caller.length + 1
  let returnTime := repeatTime + span
  have hpointwise' : ∀ d, d ≤ span →
      ∃ port, stepN w d (q, old) =
        some (port, if d = 0 then old else settled) := by
    simpa [span] using hpointwise
  obtain ⟨escape, hreturnEscape, hescapeClose, hproductive,
      hminimal, houtcome⟩ :=
    first_productive_escape_first_or_crosses_caller
      hrepeat hpointwise'
        (by rfl : returnTime = repeatTime + span)
        (by simpa [returnTime, span, Nat.add_assoc] using
          hreturnBeforeClose)
        R.event1.1
  refine ⟨escape, hescapeClose, hproductive, ?_⟩
  by_cases hfirst : RawFirstWriterAt w N start escape
  · left
    apply List.mem_append_left
    unfold rawFirstWriterHistory
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨escape, ?_, rfl⟩
    have hescapeHorizon : escape < R.z5 + 1 := by
      have o12 : R.z1 < R.z2 := R.order12
      have o23 : R.z2 < R.z3 := R.order23
      have o34 : R.z3 < R.z4 := R.order34
      have o45 : R.z4 < R.z5 := R.order45
      omega
    exact mem_rawFirstWriterTimes_iff.mpr
      ⟨hescapeHorizon, hfirst⟩
  · have hcross := Or.resolve_left houtcome hfirst
    obtain ⟨left, F, _hleftOld⟩ := hcross
    by_cases hnovel : RawNovelAt w N start escape
    · right
      have Hescape : RawRepeatedWriterNovelAt w N start escape :=
        ⟨hproductive, hfirst, hnovel⟩
      have hlow : R.z0 ≤ escape := by
        apply Classical.byContradiction
        intro hnot
        exact R.first0 escape (by omega) Hescape
      have hselected : escape = R.z0 ∨ escape = R.z1 := by
        by_cases h0 : escape = R.z0
        · exact Or.inl h0
        · by_cases hbefore1 : escape < R.z1
          · exact (R.no_event01 escape (by omega)
              hbefore1 Hescape).elim
          · exact Or.inr (by omega)
      obtain ⟨reroute, hleftReroute, hrerouteOld,
          hrerouteProductive, hdifferent, _hbetween,
          hrerouteOutcome⟩ :=
        crossing_caller_first_escape_fresh_or_interlaced
          hN Hescape F hrepeat hpointwise'
            (by rfl : returnTime = repeatTime + span) hminimal
      have hrerouteEscape : reroute < escape := by
        dsimp [returnTime, span] at hreturnEscape
        omega
      exact ⟨hselected, left, reroute, F, hleftReroute,
        hrerouteEscape, hrerouteProductive, hdifferent,
        hrerouteOutcome⟩
    · left
      have hseen :
          restrictedTonguesAt w N start (escape + 1) ∈
            (List.range (escape + 1)).map
              (restrictedTonguesAt w N start) := by
        simpa [RawNovelAt] using (Classical.not_not.mp hnovel)
      obtain ⟨j, hj, hvector⟩ := List.mem_map.mp hseen
      have hjLt : j < escape + 1 := List.mem_range.mp hj
      have hjHistory := R.prefix_through_second_mem
        (time := j) (by omega)
      rw [← hvector]
      exact hjHistory

theorem noveltyCoverOn_five_of_one_paid
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {t1 t2 t3 t4 t5 : Nat} {history : List (List Bool)}
    (hpaid :
      restrictedTonguesAt w N start t1 ∈ history ∨
      restrictedTonguesAt w N start t2 ∈ history ∨
      restrictedTonguesAt w N start t3 ∈ history ∨
      restrictedTonguesAt w N start t4 ∈ history ∨
      restrictedTonguesAt w N start t5 ∈ history) :
    NoveltyCoverOn w N start [t1, t2, t3, t4, t5] history 4 := by
  rcases hpaid with h1 | h2 | h3 | h4 | h5
  · refine ⟨[restrictedTonguesAt w N start t2,
        restrictedTonguesAt w N start t3,
        restrictedTonguesAt w N start t4,
        restrictedTonguesAt w N start t5], by simp, ?_⟩
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ h1
    all_goals apply List.mem_append_right <;> simp
  · refine ⟨[restrictedTonguesAt w N start t1,
        restrictedTonguesAt w N start t3,
        restrictedTonguesAt w N start t4,
        restrictedTonguesAt w N start t5], by simp, ?_⟩
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ h2
    all_goals apply List.mem_append_right <;> simp
  · refine ⟨[restrictedTonguesAt w N start t1,
        restrictedTonguesAt w N start t2,
        restrictedTonguesAt w N start t4,
        restrictedTonguesAt w N start t5], by simp, ?_⟩
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ h3
    all_goals apply List.mem_append_right <;> simp
  · refine ⟨[restrictedTonguesAt w N start t1,
        restrictedTonguesAt w N start t2,
        restrictedTonguesAt w N start t3,
        restrictedTonguesAt w N start t5], by simp, ?_⟩
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ h4
    · exact List.mem_append_right _ (by simp)
  · refine ⟨[restrictedTonguesAt w N start t1,
        restrictedTonguesAt w N start t2,
        restrictedTonguesAt w N start t3,
        restrictedTonguesAt w N start t4], by simp, ?_⟩
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ h5

/-- Specialization of `noveltyCoverOn_five_of_one_paid` to the five tail
closes of a raw six-event reduction.  A dynamical branch now has exactly one
accounting obligation: put any selected tail close into first-writer history
plus event zero. -/
theorem RawSixEventReduction.tail_cover_of_one_paid
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawSixEventReduction w N start)
    (hpaid :
      restrictedTonguesAt w N start (R.z1 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      restrictedTonguesAt w N start (R.z2 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      restrictedTonguesAt w N start (R.z3 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      restrictedTonguesAt w N start (R.z4 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      restrictedTonguesAt w N start (R.z5 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)]) :
    NoveltyCoverOn w N start
      [R.z1 + 1, R.z2 + 1, R.z3 + 1, R.z4 + 1, R.z5 + 1]
      (rawFirstWriterHistory w N start (R.z5 + 1) ++
        [restrictedTonguesAt w N start (R.z0 + 1)]) 4 := by
  exact noveltyCoverOn_five_of_one_paid hpaid

/-- **A four-vector cover of the five tail closes would close the six-event
counter immediately.**  None of the five post-vectors can be paid for by
`rawFirstWriterHistory`, and none can equal event zero's post-vector.  The
five vectors are pairwise distinct.  Therefore the desired tail cover is
not merely bookkeeping: constructing it is exactly the missing dynamical
contradiction. -/
theorem RawSixEventReduction.no_tail_four_cover
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (R : RawSixEventReduction w N start) :
    ¬ NoveltyCoverOn w N start
        [R.z1 + 1, R.z2 + 1, R.z3 + 1, R.z4 + 1, R.z5 + 1]
        (rawFirstWriterHistory w N start (R.z5 + 1) ++
          [restrictedTonguesAt w N start (R.z0 + 1)]) 4 := by
  let times :=
    [R.z1 + 1, R.z2 + 1, R.z3 + 1, R.z4 + 1, R.z5 + 1]
  let firstHistory := rawFirstWriterHistory w N start (R.z5 + 1)
  let eventZero := restrictedTonguesAt w N start (R.z0 + 1)
  intro hcover
  have o01 : R.z0 < R.z1 := R.order01
  have o12 : R.z1 < R.z2 := R.order12
  have o23 : R.z2 < R.z3 := R.order23
  have o34 : R.z3 < R.z4 := R.order34
  have o45 : R.z4 < R.z5 := R.order45
  have o02 : R.z0 < R.z2 := Nat.lt_trans o01 o12
  have o03 : R.z0 < R.z3 := Nat.lt_trans o02 o23
  have o04 : R.z0 < R.z4 := Nat.lt_trans o03 o34
  have o05 : R.z0 < R.z5 := Nat.lt_trans o04 o45
  have o13 : R.z1 < R.z3 := Nat.lt_trans o12 o23
  have o14 : R.z1 < R.z4 := Nat.lt_trans o13 o34
  have o15 : R.z1 < R.z5 := Nat.lt_trans o14 o45
  have o24 : R.z2 < R.z4 := Nat.lt_trans o23 o34
  have o25 : R.z2 < R.z5 := Nat.lt_trans o24 o45
  have o35 : R.z3 < R.z5 := Nat.lt_trans o34 o45
  have hnew : ∀ t ∈ times,
      restrictedTonguesAt w N start t ∉
        firstHistory ++ [eventZero] := by
    intro t ht
    dsimp [times] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · intro hm
      rcases List.mem_append.mp hm with hfirst | hzero
      · exact repeatedWriterPost_not_mem_firstHistory hN
          (mem_rawRepeatedWriterNovelTimes_iff.mpr
            ⟨by omega, R.event1⟩) hfirst
      · simp only [List.mem_singleton] at hzero
        exact R.event1.2.2.post_ne_earlier (by omega) hzero
    · intro hm
      rcases List.mem_append.mp hm with hfirst | hzero
      · exact repeatedWriterPost_not_mem_firstHistory hN
          (mem_rawRepeatedWriterNovelTimes_iff.mpr
            ⟨by omega, R.event2⟩) hfirst
      · simp only [List.mem_singleton] at hzero
        exact R.event2.2.2.post_ne_earlier (by omega) hzero
    · intro hm
      rcases List.mem_append.mp hm with hfirst | hzero
      · exact repeatedWriterPost_not_mem_firstHistory hN
          (mem_rawRepeatedWriterNovelTimes_iff.mpr
            ⟨by omega, R.event3⟩) hfirst
      · simp only [List.mem_singleton] at hzero
        exact R.event3.2.2.post_ne_earlier (by omega) hzero
    · intro hm
      rcases List.mem_append.mp hm with hfirst | hzero
      · exact repeatedWriterPost_not_mem_firstHistory hN
          (mem_rawRepeatedWriterNovelTimes_iff.mpr
            ⟨by omega, R.event4⟩) hfirst
      · simp only [List.mem_singleton] at hzero
        exact R.event4.2.2.post_ne_earlier (by omega) hzero
    · intro hm
      rcases List.mem_append.mp hm with hfirst | hzero
      · exact repeatedWriterPost_not_mem_firstHistory hN
          (mem_rawRepeatedWriterNovelTimes_iff.mpr
            ⟨by omega, R.event5⟩) hfirst
      · simp only [List.mem_singleton] at hzero
        exact R.event5.2.2.post_ne_earlier (by omega) hzero
  have h12 :
      restrictedTonguesAt w N start (R.z1 + 1) ≠
        restrictedTonguesAt w N start (R.z2 + 1) :=
    (R.event2.2.2.post_ne_earlier (by omega)).symm
  have h13 :
      restrictedTonguesAt w N start (R.z1 + 1) ≠
        restrictedTonguesAt w N start (R.z3 + 1) :=
    (R.event3.2.2.post_ne_earlier (by omega)).symm
  have h14 :
      restrictedTonguesAt w N start (R.z1 + 1) ≠
        restrictedTonguesAt w N start (R.z4 + 1) :=
    (R.event4.2.2.post_ne_earlier (by omega)).symm
  have h15 :
      restrictedTonguesAt w N start (R.z1 + 1) ≠
        restrictedTonguesAt w N start (R.z5 + 1) :=
    (R.event5.2.2.post_ne_earlier (by omega)).symm
  have h23 :
      restrictedTonguesAt w N start (R.z2 + 1) ≠
        restrictedTonguesAt w N start (R.z3 + 1) :=
    (R.event3.2.2.post_ne_earlier (by omega)).symm
  have h24 :
      restrictedTonguesAt w N start (R.z2 + 1) ≠
        restrictedTonguesAt w N start (R.z4 + 1) :=
    (R.event4.2.2.post_ne_earlier (by omega)).symm
  have h25 :
      restrictedTonguesAt w N start (R.z2 + 1) ≠
        restrictedTonguesAt w N start (R.z5 + 1) :=
    (R.event5.2.2.post_ne_earlier (by omega)).symm
  have h34 :
      restrictedTonguesAt w N start (R.z3 + 1) ≠
        restrictedTonguesAt w N start (R.z4 + 1) :=
    (R.event4.2.2.post_ne_earlier (by omega)).symm
  have h35 :
      restrictedTonguesAt w N start (R.z3 + 1) ≠
        restrictedTonguesAt w N start (R.z5 + 1) :=
    (R.event5.2.2.post_ne_earlier (by omega)).symm
  have h45 :
      restrictedTonguesAt w N start (R.z4 + 1) ≠
        restrictedTonguesAt w N start (R.z5 + 1) :=
    (R.event5.2.2.post_ne_earlier (by omega)).symm
  have hnd :
      (times.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [times]
    simp [List.nodup_cons, h12, h13, h14, h15,
      h23, h24, h25, h34, h35, h45]
  have hcount := noveltyCoverOn_fresh_distinct_count
    hcover hnew hnd
  dsimp [times] at hcount
  omega

/-- Consequently, paying one selected tail close is sufficient to close the
raw reduction: every such payment directly contradicts the five tail
novelties.  The converse is neither asserted nor used. -/
theorem RawSixEventReduction.no_selected_tail_close_paid
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (R : RawSixEventReduction w N start) :
    ¬ (
      restrictedTonguesAt w N start (R.z1 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      restrictedTonguesAt w N start (R.z2 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      restrictedTonguesAt w N start (R.z3 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      restrictedTonguesAt w N start (R.z4 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      restrictedTonguesAt w N start (R.z5 + 1) ∈
          rawFirstWriterHistory w N start (R.z5 + 1) ++
            [restrictedTonguesAt w N start (R.z0 + 1)]) := by
  intro hpaid
  exact R.no_tail_four_cover hN (R.tail_cover_of_one_paid hpaid)

/-! ## Rebase at the actual positive caller return -/

/-- Global novelty survives rebasing at an actually reached suffix. -/
private theorem sixEvent_rawNovelAt_sub_of_reach
    {w : Wiring} {N shift d : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hnovel : RawNovelAt w N start (shift + d)) :
    RawNovelAt w N middle d := by
  have hlocalProductive : RawProductiveAt w N middle d :=
    rawProductiveAt_sub_of_reach hreach
      (rawNovelAt_productive hnovel)
  intro hseen
  obtain ⟨j, hj, hvector⟩ := List.mem_map.mp hseen
  have hjLt : j < d + 1 := List.mem_range.mp hj
  obtain ⟨post, hpost⟩ :=
    Option.isSome_iff_exists.mp hlocalProductive.1
  obtain ⟨earlier, hearlier⟩ := stepN_prefix_some
    (d := j) (K := d + 1) (by omega) hpost
  have hearlierVector := restrictedTonguesAt_add_of_reach
    (N := N) hreach hearlier
  have hpostVector := restrictedTonguesAt_add_of_reach
    (N := N) hreach hpost
  apply hnovel
  apply List.mem_map.mpr
  refine ⟨shift + j, List.mem_range.mpr (by omega), ?_⟩
  calc
    restrictedTonguesAt w N start (shift + j) =
        restrictedTonguesAt w N middle j := hearlierVector
    _ = restrictedTonguesAt w N middle (d + 1) := hvector
    _ = restrictedTonguesAt w N start (shift + (d + 1)) :=
      hpostVector.symm
    _ = restrictedTonguesAt w N start (shift + d + 1) := by
      congr 1

/-- A last-writer frame rebases at any reached boundary before its opening. -/
private theorem RawLastWriterFrame.sixEvent_rebase
    {w : Wiring} {N shift left right : Nat}
    {start middle : Nat × Tongues}
    (F : RawLastWriterFrame w N start left right)
    (hshift : shift ≤ left)
    (hreach : stepN w shift start = some middle) :
    RawLastWriterFrame w N middle
      (left - shift) (right - shift) := by
  let localLeft := left - shift
  let localRight := right - shift
  have hleftTime : shift + localLeft = left := by
    dsimp [localLeft]
    omega
  have hrightTime : shift + localRight = right := by
    dsimp [localRight]
    have := F.order
    omega
  have hopen : RawProductiveAt w N middle localLeft := by
    have hglobal :
        RawProductiveAt w N start (shift + localLeft) := by
      rw [hleftTime]
      exact F.open_productive
    exact rawProductiveAt_sub_of_reach hreach hglobal
  have hclose : RawProductiveAt w N middle localRight := by
    have hglobal :
        RawProductiveAt w N start (shift + localRight) := by
      rw [hrightTime]
      exact F.close_productive
    exact rawProductiveAt_sub_of_reach hreach hglobal
  have hopenLive : (stepN w localLeft middle).isSome := by
    obtain ⟨post, hpost⟩ := Option.isSome_iff_exists.mp hopen.1
    obtain ⟨before, hbefore⟩ := stepN_prefix_some
      (d := localLeft) (K := localLeft + 1) (by omega) hpost
    simp [hbefore]
  have hcloseLive : (stepN w localRight middle).isSome := by
    obtain ⟨post, hpost⟩ := Option.isSome_iff_exists.mp hclose.1
    obtain ⟨before, hbefore⟩ := stepN_prefix_some
      (d := localRight) (K := localRight + 1) (by omega) hpost
    simp [hbefore]
  have hwriterOpen := rawWriterAt_add_of_reach hreach hopenLive
  have hwriterClose := rawWriterAt_add_of_reach hreach hcloseLive
  rw [hleftTime] at hwriterOpen
  rw [hrightTime] at hwriterClose
  refine {
    order := by
      have := F.order
      omega
    open_productive := hopen
    close_productive := hclose
    same_writer := ?_
    no_same_writer_between := ?_
  }
  · exact hwriterOpen.symm.trans
      (F.same_writer.trans hwriterClose)
  · intro j hjLeft hjRight hjProd
    have hjPost : ∃ finish,
        stepN w (j + 1) middle = some finish :=
      Option.isSome_iff_exists.mp hjProd.1
    have hjGlobalProd :
        RawProductiveAt w N start (shift + j) :=
      (RawProductiveAt.shift_iff hreach hjPost).mp hjProd
    have hjCurrent : ∃ current,
        stepN w j middle = some current := by
      obtain ⟨finish, hfinish⟩ := hjPost
      exact stepN_prefix_some (d := j) (K := j + 1)
        (by omega) hfinish
    have hjWriter := rawWriterAt_shift_eq hreach hjCurrent
    have hno := F.no_same_writer_between (shift + j)
      (by omega) (by omega) hjGlobalProd
    intro heq
    apply hno
    calc
      rawWriterAt w start (shift + j) =
          rawWriterAt w middle j := hjWriter.symm
      _ = rawWriterAt w middle localRight := heq
      _ = rawWriterAt w start right := hwriterClose.symm

/-- A globally novel repeated close survives rebasing at a boundary before
its certified last-writer opening. -/
private theorem RawRepeatedWriterNovelAt.sixEvent_rebase_after_frame
    {w : Wiring} {N shift left right : Nat}
    {start middle : Nat × Tongues}
    (H : RawRepeatedWriterNovelAt w N start right)
    (F : RawLastWriterFrame w N start left right)
    (hshift : shift ≤ left)
    (hreach : stepN w shift start = some middle) :
    RawRepeatedWriterNovelAt w N middle (right - shift) := by
  let localLeft := left - shift
  let localRight := right - shift
  have hleftTime : shift + localLeft = left := by
    dsimp [localLeft]
    omega
  have hrightTime : shift + localRight = right := by
    dsimp [localRight]
    have := F.order
    omega
  have localFrame := F.sixEvent_rebase hshift hreach
  refine ⟨localFrame.close_productive, ?_, ?_⟩
  · intro hfirst
    exact hfirst.2 localLeft localFrame.order
      localFrame.open_productive localFrame.same_writer
  · have hglobalNovel :
        RawNovelAt w N start (shift + localRight) := by
      rw [hrightTime]
      exact H.2.2
    have hnovel :=
      sixEvent_rawNovelAt_sub_of_reach hreach hglobalNovel
    simpa [localRight] using hnovel

/-- **Strict serial suffix reduction for six events.**  In the serial tail
of a raw six-event obstruction, an actual completed caller return is reached
at positive absolute time.  A selected later novelty and its canonical
last-writer frame rebase to that returned run, and the local close time is
strictly smaller than its original absolute close time.

This consumes the serial alternative; it does not postulate a recursive
repair object. -/
theorem RawSixEventReduction.serial_tail_strict_suffix
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawSixEventReduction w N start)
    (hserial : FiveFrameSerialBreak
      R.z1 R.a2 R.a3 R.a4 R.a5) :
    ∃ edge settled returnTime laterOpen laterClose,
      stepN w returnTime start = some (edge, settled) ∧
      0 < returnTime ∧
      returnTime ≤ R.z1 ∧
      R.z1 ≤ laterOpen ∧
      laterOpen < laterClose ∧
      RawLastWriterFrame w N start laterOpen laterClose ∧
      RawRepeatedWriterNovelAt w N start laterClose ∧
      RawLastWriterFrame w N (edge, settled)
        (laterOpen - returnTime) (laterClose - returnTime) ∧
      RawRepeatedWriterNovelAt w N (edge, settled)
        (laterClose - returnTime) ∧
      laterClose - returnTime < laterClose := by
  obtain ⟨_g, _base, _oldEntry, _mouthState, q, u, settled,
      edge, repeatTime, caller, _hbefore, _hcaller, _hsimple,
      _hgrooved, _hcallerLe, _hedge, hrepeat, _hopen,
      _hrepeatClose, hreturnClose, _hcontact, hback,
      _hpointwise, _hcover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry
      R.event1 R.event2 R.event3 R.event4 R.event5
      R.frame1 R.frame2 R.frame3 R.frame4 R.frame5 hserial
  let returnTime := repeatTime + caller.length + 1
  have hreturn :
      stepN w returnTime start = some (edge, settled) := by
    dsimp [returnTime]
    rw [show repeatTime + caller.length + 1 =
        repeatTime + (caller.length + 1) by omega,
      stepN_add, hrepeat]
    exact hback
  have hpositive : 0 < returnTime := by
    dsimp [returnTime]
    omega
  have hreturnLe : returnTime ≤ R.z1 := by
    simpa [returnTime, Nat.add_assoc] using hreturnClose
  rcases hserial with h2 | h3 | h4 | h5
  · have hshift : returnTime ≤ R.a2 := by omega
    have hframeLocal :=
      R.frame2.outer.sixEvent_rebase hshift hreturn
    have heventLocal :=
      R.event2.sixEvent_rebase_after_frame
        R.frame2.outer hshift hreturn
    refine ⟨edge, settled, returnTime, R.a2, R.z2,
      hreturn, hpositive, hreturnLe, h2,
      R.frame2.outer.order, R.frame2.outer, R.event2,
      hframeLocal, heventLocal, ?_⟩
    exact Nat.sub_lt_of_pos_le hpositive
      (Nat.le_trans hshift (Nat.le_of_lt R.frame2.outer.order))
  · have hshift : returnTime ≤ R.a3 := by omega
    have hframeLocal :=
      R.frame3.outer.sixEvent_rebase hshift hreturn
    have heventLocal :=
      R.event3.sixEvent_rebase_after_frame
        R.frame3.outer hshift hreturn
    refine ⟨edge, settled, returnTime, R.a3, R.z3,
      hreturn, hpositive, hreturnLe, h3,
      R.frame3.outer.order, R.frame3.outer, R.event3,
      hframeLocal, heventLocal, ?_⟩
    exact Nat.sub_lt_of_pos_le hpositive
      (Nat.le_trans hshift (Nat.le_of_lt R.frame3.outer.order))
  · have hshift : returnTime ≤ R.a4 := by omega
    have hframeLocal :=
      R.frame4.outer.sixEvent_rebase hshift hreturn
    have heventLocal :=
      R.event4.sixEvent_rebase_after_frame
        R.frame4.outer hshift hreturn
    refine ⟨edge, settled, returnTime, R.a4, R.z4,
      hreturn, hpositive, hreturnLe, h4,
      R.frame4.outer.order, R.frame4.outer, R.event4,
      hframeLocal, heventLocal, ?_⟩
    exact Nat.sub_lt_of_pos_le hpositive
      (Nat.le_trans hshift (Nat.le_of_lt R.frame4.outer.order))
  · have hshift : returnTime ≤ R.a5 := by omega
    have hframeLocal :=
      R.frame5.outer.sixEvent_rebase hshift hreturn
    have heventLocal :=
      R.event5.sixEvent_rebase_after_frame
        R.frame5.outer hshift hreturn
    refine ⟨edge, settled, returnTime, R.a5, R.z5,
      hreturn, hpositive, hreturnLe, h5,
      R.frame5.outer.order, R.frame5.outer, R.event5,
      hframeLocal, heventLocal, ?_⟩
    exact Nat.sub_lt_of_pos_le hpositive
      (Nat.le_trans hshift (Nat.le_of_lt R.frame5.outer.order))

end GeneralN
