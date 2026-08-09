import FiveFrameObstruction
import SharpCertificateClosure

/-!
# The serial retrace really precedes its selected continuation

The local return extracted from five serial novelty frames is not merely a
formal recursive premise.  `FiveFrameSerialBreak` names an actual later
closing frame whose opening is productive.  The pointwise retrace theorem
says that every positive depth of the completed reverse has one fixed tongue
state.  A productive opening therefore cannot lie strictly inside that
reverse.

This file packages the resulting global suffix.  The completed reverse is
reached no later than the selected later opening.  Consequently the selected
closing novelty rebases to a genuine repeated-writer novelty of the returned
configuration, and hence supplies a fresh local closing frame without any
continuation premise.

This is a general-`N` control-flow theorem.  It does not claim `StateLaw`.
-/

namespace GeneralN

/-- One actual later frame selected by the serial-break disjunction. -/
structure RawSelectedLaterSerialFrame
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (firstClose : Nat) where
  openTime : Nat
  rerouteTime : Nat
  closeTime : Nat
  after_first_close : firstClose ≤ openTime
  event : RawRepeatedWriterNovelAt w N start closeTime
  frame : RawNovelClosingFrame w N start openTime rerouteTime closeTime

/-- `FiveFrameSerialBreak` contains an actual later frame, not just a bare
time inequality. -/
theorem FiveFrameSerialBreak.select_later_frame
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (H₁ : RawRepeatedWriterNovelAt w N start z₁)
    (H₂ : RawRepeatedWriterNovelAt w N start z₂)
    (H₃ : RawRepeatedWriterNovelAt w N start z₃)
    (H₄ : RawRepeatedWriterNovelAt w N start z₄)
    {a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄ : Nat}
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hserial : FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄) :
    Nonempty (RawSelectedLaterSerialFrame w N start z₀) := by
  rcases hserial with h₁ | h₂ | h₃ | h₄
  · exact ⟨{
      openTime := a₁
      rerouteTime := q₁
      closeTime := z₁
      after_first_close := h₁
      event := H₁
      frame := F₁
    }⟩
  · exact ⟨{
      openTime := a₂
      rerouteTime := q₂
      closeTime := z₂
      after_first_close := h₂
      event := H₂
      frame := F₂
    }⟩
  · exact ⟨{
      openTime := a₃
      rerouteTime := q₃
      closeTime := z₃
      after_first_close := h₃
      event := H₃
      frame := F₃
    }⟩
  · exact ⟨{
      openTime := a₄
      rerouteTime := q₄
      closeTime := z₄
      after_first_close := h₄
      event := H₄
      frame := F₄
    }⟩

/-- A productive event cannot occur strictly inside a pointwise retrace whose
positive-depth configurations all have the same tongue state. -/
theorem productive_not_inside_pointwise_retrace
    {w : Wiring} {N repeatTime span openTime q : Nat}
    {start : Nat × Tongues} {old settled : Tongues}
    (hrepeat : stepN w repeatTime start = some (q, old))
    (hpointwise : ∀ d, d ≤ span →
      ∃ port, stepN w d (q, old) =
        some (port, if d = 0 then old else settled))
    (hproductive : RawProductiveAt w N start openTime)
    (hafter : repeatTime < openTime) :
    repeatTime + span ≤ openTime := by
  apply Classical.byContradiction
  intro hnot
  have hopenBeforeEnd : openTime < repeatTime + span := by omega
  let d := openTime - repeatTime
  have hdPositive : 0 < d := by
    dsimp [d]
    omega
  have hdLt : d < span := by
    dsimp [d]
    omega
  have hdSucc : d + 1 ≤ span := by omega
  have htime : repeatTime + d = openTime := by
    dsimp [d]
    omega
  have htimeSucc : repeatTime + (d + 1) = openTime + 1 := by omega
  obtain ⟨beforePort, hbeforeLocal⟩ := hpointwise d (by omega)
  obtain ⟨afterPort, hafterLocal⟩ := hpointwise (d + 1) hdSucc
  have hbeforeGlobal :
      stepN w openTime start = some (beforePort, settled) := by
    rw [← htime, stepN_add, hrepeat]
    simpa [Nat.ne_of_gt hdPositive] using hbeforeLocal
  have hafterGlobal :
      stepN w (openTime + 1) start = some (afterPort, settled) := by
    rw [← htimeSucc, stepN_add, hrepeat]
    simp only [Option.bind_some]
    simpa using hafterLocal
  apply hproductive.2
  simp [restrictedTonguesAt, tonguesAt,
    hbeforeGlobal, hafterGlobal]

/-- Local copy of the caller-crossing refinement, kept in this owned module
until the shared `SharpCertificateClosure` source rebuilds on Lean 4.32.2.
A novel first escape whose previous write crosses the caller exposes either
a globally first old-side writer or a strictly interlaced last-writer frame. -/
theorem globalSerial_crossing_caller_fresh_or_interlaced
    {w : Wiring} {N repeatTime span returnTime left escape q : Nat}
    {start : Nat × Tongues} {old settled : Tongues}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (H : RawRepeatedWriterNovelAt w N start escape)
    (F : RawLastWriterFrame w N start left escape)
    (hrepeat : stepN w repeatTime start = some (q, old))
    (hpointwise : ∀ d, d ≤ span →
      ∃ port, stepN w d (q, old) =
        some (port, if d = 0 then old else settled))
    (hreturnTime : returnTime = repeatTime + span)
    (hminimal : ∀ t, returnTime ≤ t → t < escape →
      ¬ RawProductiveAt w N start t) :
    ∃ reroute,
      left < reroute ∧ reroute ≤ repeatTime ∧
      RawProductiveAt w N start reroute ∧
      rawWriterAt w start reroute ≠ rawWriterAt w start escape ∧
      (∀ t, left < t → t < reroute →
        RawProductiveAt w N start t →
        rawWriterAt w start t ≠ rawWriterAt w start reroute) ∧
      (RawFirstWriterAt w N start reroute ∨
        ∃ prior,
          RawLastWriterFrame w N start prior reroute ∧
          prior < left) := by
  obtain ⟨_C, reroute, _hC, hleftReroute, hrerouteEscape,
      hrerouteProductive, hwriter, _hchange, hnoSame⟩ :=
    H.first_changed_writer hN F
  have hrerouteOld : reroute ≤ repeatTime := by
    apply Classical.byContradiction
    intro hnot
    have hrepeatReroute : repeatTime < reroute := by omega
    have hreturnReroute : returnTime ≤ reroute := by
      rw [hreturnTime]
      exact productive_not_inside_pointwise_retrace
        hrepeat hpointwise hrerouteProductive hrepeatReroute
    exact hminimal reroute hreturnReroute hrerouteEscape
      hrerouteProductive
  have hdifferent : rawWriterAt w start reroute ≠
      rawWriterAt w start escape :=
    F.no_same_writer_between reroute hleftReroute
      hrerouteEscape hrerouteProductive
  refine ⟨reroute, hleftReroute, hrerouteOld,
    hrerouteProductive, hdifferent, ?_, ?_⟩
  · intro t hleftT htReroute htProductive
    rw [hwriter]
    exact hnoSame t hleftT htReroute htProductive
  · by_cases hfirst : RawFirstWriterAt w N start reroute
    · exact Or.inl hfirst
    · right
      obtain ⟨prior, G⟩ :=
        last_writer_frame_of_productive_not_first
          hrerouteProductive hfirst
      refine ⟨prior, G, ?_⟩
      by_cases hprior : prior < left
      · exact hprior
      · by_cases heq : prior = left
        · subst prior
          exact (hdifferent
            (G.same_writer.symm.trans F.same_writer)).elim
        · have hleftPrior : left < prior := by omega
          exact (hnoSame prior hleftPrior G.order
            G.open_productive
            (G.same_writer.trans hwriter)).elim

/-- Novelty is preserved when an ambient run is rebased at an actually
reached configuration. -/
theorem rawNovelAt_add_rebase
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
      simp only [Nat.add_assoc]

/-- Complete classification of the first productive event after one exact
serial return.  A first writer is paid; a non-novel event replays; a novel
caller-crossing event either exposes a first writer on the old side or the
strictly interlaced pattern `B < A < B < A`. -/
inductive RawPostReturnEscapeOutcome
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (repeatTime returnTime firstClose : Nat) : Prop
  | paid (escape : Nat)
      (after_return : returnTime ≤ escape)
      (before_close : escape ≤ firstClose)
      (productive : RawProductiveAt w N start escape)
      (minimal : ∀ t, returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t)
      (first : RawFirstWriterAt w N start escape) :
      RawPostReturnEscapeOutcome w N start
        repeatTime returnTime firstClose
  | replay (escape left : Nat)
      (after_return : returnTime ≤ escape)
      (before_close : escape ≤ firstClose)
      (minimal : ∀ t, returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t)
      (frame : RawLastWriterFrame w N start left escape)
      (crosses_caller : left ≤ repeatTime)
      (not_novel : ¬ RawNovelAt w N start escape) :
      RawPostReturnEscapeOutcome w N start
        repeatTime returnTime firstClose
  | fresh_old_side (escape left reroute : Nat)
      (after_return : returnTime ≤ escape)
      (before_close : escape ≤ firstClose)
      (minimal : ∀ t, returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t)
      (event : RawRepeatedWriterNovelAt w N start escape)
      (outer : RawLastWriterFrame w N start left escape)
      (left_before_reroute : left < reroute)
      (reroute_before_escape : reroute < escape)
      (reroute_old_side : reroute ≤ repeatTime)
      (reroute_first : RawFirstWriterAt w N start reroute) :
      RawPostReturnEscapeOutcome w N start
        repeatTime returnTime firstClose
  | baba (escape left reroute prior : Nat)
      (after_return : returnTime ≤ escape)
      (before_close : escape ≤ firstClose)
      (minimal : ∀ t, returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t)
      (event : RawRepeatedWriterNovelAt w N start escape)
      (outer : RawLastWriterFrame w N start left escape)
      (inner : RawLastWriterFrame w N start prior reroute)
      (prior_before_left : prior < left)
      (left_before_reroute : left < reroute)
      (reroute_before_escape : reroute < escape)
      (reroute_old_side : reroute ≤ repeatTime) :
      RawPostReturnEscapeOutcome w N start
        repeatTime returnTime firstClose

/-- The concrete data retained after a serial reverse.  In particular, the
selected later close remains a repeated-writer novelty in the returned
suffix and therefore has a locally extracted closing frame. -/
structure RawGlobalSerialContinuation
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (firstClose : Nat) where
  returned : Nat × Tongues
  repeatTime : Nat
  returnTime : Nat
  entryEdge : Nat
  selected : RawSelectedLaterSerialFrame w N start firstClose
  reaches_return : stepN w returnTime start = some returned
  entry_link : w.link entryEdge = some returned.1
  repeat_before_return : repeatTime < returnTime
  return_positive : 0 < returnTime
  return_before_first_close : returnTime ≤ firstClose
  return_before_open : returnTime ≤ selected.openTime
  local_open_productive :
    RawProductiveAt w N returned (selected.openTime - returnTime)
  local_close_event :
    RawRepeatedWriterNovelAt w N returned
      (selected.closeTime - returnTime)
  local_closing_frame :
    ∃ left reroute,
      RawNovelClosingFrame w N returned left reroute
        (selected.closeTime - returnTime)
  first_escape :
    ∃ escape,
      returnTime ≤ escape ∧ escape ≤ firstClose ∧
      RawProductiveAt w N start escape ∧
      (∀ t, returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t) ∧
      (RawFirstWriterAt w N start escape ∨
        ∃ left, RawLastWriterFrame w N start left escape ∧
          left ≤ repeatTime)
  escape_outcome :
    RawPostReturnEscapeOutcome w N start
      repeatTime returnTime firstClose

/-- **Global serial continuation, with no continuation premise.**

The later frame named by `FiveFrameSerialBreak` opens after the completed
reverse.  Its opening and closing productive events therefore both rebase
to the returned configuration.  The opening witnesses that the rebased
closing event is not a first writer; ambient novelty rebases as well. -/
theorem five_serial_novelties_supply_global_continuation
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (H₀ : RawRepeatedWriterNovelAt w N start z₀)
    (H₁ : RawRepeatedWriterNovelAt w N start z₁)
    (H₂ : RawRepeatedWriterNovelAt w N start z₂)
    (H₃ : RawRepeatedWriterNovelAt w N start z₃)
    (H₄ : RawRepeatedWriterNovelAt w N start z₄)
    {a₀ q₀ a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄ : Nat}
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hserial : FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄) :
    Nonempty (RawGlobalSerialContinuation w N start z₀) := by
  obtain ⟨selected⟩ := hserial.select_later_frame
    H₁ H₂ H₃ H₄ F₁ F₂ F₃ F₄
  obtain ⟨g, base, oldEntry, mouthState, q, old, settled, edge,
      repeatTime, caller, _hbefore, _hcaller, _hsimple, _hgrooved,
      _hcallerLe, hedge, hrepeat, _hrepeatAfterOpen,
      hrepeatBeforeClose, hreturnBeforeClose, _hcontact,
      hreturn, hpointwise, _hcover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  let span := caller.length + 1
  let returnTime := repeatTime + span
  let returned : Nat × Tongues := (edge, settled)
  have hrepeatBeforeOpen : repeatTime < selected.openTime := by
    exact Nat.lt_of_lt_of_le hrepeatBeforeClose
      selected.after_first_close
  have hreturnBeforeOpen : returnTime ≤ selected.openTime := by
    dsimp [returnTime, span]
    exact productive_not_inside_pointwise_retrace
      hrepeat hpointwise selected.frame.outer.open_productive
        hrepeatBeforeOpen
  have hreachesReturn : stepN w returnTime start = some returned := by
    dsimp [returnTime, span, returned]
    rw [stepN_add, hrepeat]
    exact hreturn
  let localOpen := selected.openTime - returnTime
  let localClose := selected.closeTime - returnTime
  have hopenEq : returnTime + localOpen = selected.openTime := by
    dsimp [localOpen]
    omega
  have hcloseOrder : selected.openTime < selected.closeTime :=
    selected.frame.outer.order
  have hcloseEq : returnTime + localClose = selected.closeTime := by
    dsimp [localClose]
    omega
  have hlocalOpen : RawProductiveAt w N returned localOpen := by
    have h := rawProductiveAt_sub_of_reach hreachesReturn
      (d := localOpen) (by
        simpa [hopenEq] using selected.frame.outer.open_productive)
    exact h
  have hlocalCloseProductive :
      RawProductiveAt w N returned localClose := by
    have h := rawProductiveAt_sub_of_reach hreachesReturn
      (d := localClose) (by
        simpa [hcloseEq] using selected.event.1)
    exact h
  have hlocalCloseNovel : RawNovelAt w N returned localClose := by
    apply rawNovelAt_add_rebase hreachesReturn
    simpa [hcloseEq] using selected.event.2.2
  have hopenLive : (stepN w localOpen returned).isSome := by
    obtain ⟨post, hpost⟩ :=
      Option.isSome_iff_exists.mp hlocalOpen.1
    obtain ⟨before, hbefore⟩ := stepN_prefix_some
      (d := localOpen) (K := localOpen + 1) (by omega) hpost
    simp [hbefore]
  have hcloseLive : (stepN w localClose returned).isSome := by
    obtain ⟨post, hpost⟩ :=
      Option.isSome_iff_exists.mp hlocalCloseProductive.1
    obtain ⟨before, hbefore⟩ := stepN_prefix_some
      (d := localClose) (K := localClose + 1) (by omega) hpost
    simp [hbefore]
  have hopenWriter := rawWriterAt_add_of_reach
    hreachesReturn hopenLive
  have hcloseWriter := rawWriterAt_add_of_reach
    hreachesReturn hcloseLive
  have hlocalSameWriter :
      rawWriterAt w returned localOpen =
        rawWriterAt w returned localClose := by
    rw [hopenEq] at hopenWriter
    rw [hcloseEq] at hcloseWriter
    exact hopenWriter.symm.trans
      (selected.frame.outer.same_writer.trans hcloseWriter)
  have hlocalOpenClose : localOpen < localClose := by
    dsimp [localOpen, localClose]
    omega
  have hlocalNotFirst :
      ¬ RawFirstWriterAt w N returned localClose := by
    intro hfirst
    exact hfirst.2 localOpen hlocalOpenClose hlocalOpen
      hlocalSameWriter
  have hlocalEvent :
      RawRepeatedWriterNovelAt w N returned localClose :=
    ⟨hlocalCloseProductive, hlocalNotFirst, hlocalCloseNovel⟩
  obtain ⟨left, reroute, localFrame⟩ :=
    hlocalEvent.novelClosingFrame hN
  exact ⟨{
    returned := returned
    repeatTime := repeatTime
    returnTime := returnTime
    entryEdge := g
    selected := selected
    reaches_return := hreachesReturn
    entry_link := by
      dsimp [returned]
      exact w.symm _ _ hedge
    repeat_before_return := by
      dsimp [returnTime, span]
      omega
    return_positive := by
      dsimp [returnTime, span]
      omega
    return_before_first_close := by
      simpa [returnTime, span, Nat.add_assoc] using hreturnBeforeClose
    return_before_open := hreturnBeforeOpen
    local_open_productive := by simpa [localOpen]
    local_close_event := by simpa [localClose]
    local_closing_frame := by
      exact ⟨left, reroute, by simpa [localClose] using localFrame⟩
    first_escape := by
      apply first_productive_escape_first_or_crosses_caller
        (N := N) (repeatTime := repeatTime) (span := span)
        (returnTime := returnTime) (right := z₀) (q := q)
        hrepeat hpointwise
      · rfl
      · exact (by
          simpa [returnTime, span, Nat.add_assoc] using
            hreturnBeforeClose)
      · exact H₀.1
    escape_outcome := by
      obtain ⟨escape, hafter, hbefore, hproductive, hminimal,
          hfirst | ⟨left, hframe, hleft⟩⟩ :=
        first_productive_escape_first_or_crosses_caller
          (N := N) (repeatTime := repeatTime) (span := span)
          (returnTime := returnTime) (right := z₀) (q := q)
          hrepeat hpointwise rfl (by
            simpa [returnTime, span, Nat.add_assoc] using
              hreturnBeforeClose) H₀.1
      · exact RawPostReturnEscapeOutcome.paid escape hafter hbefore
          hproductive hminimal hfirst
      · by_cases hnovel : RawNovelAt w N start escape
        · have hnotFirst : ¬ RawFirstWriterAt w N start escape := by
            intro hfirstEscape
            exact hfirstEscape.2 left hframe.order
              hframe.open_productive hframe.same_writer
          have Hevent :
              RawRepeatedWriterNovelAt w N start escape :=
            ⟨hproductive, hnotFirst, hnovel⟩
          obtain ⟨reroute, hleftReroute, hrerouteOld,
              hrerouteProductive, _hdifferent, _hnoSame,
              hrerouteFirst | ⟨prior, hinner, hprior⟩⟩ :=
            globalSerial_crossing_caller_fresh_or_interlaced
              hN Hevent hframe hrepeat hpointwise rfl hminimal
          · exact RawPostReturnEscapeOutcome.fresh_old_side
              escape left reroute hafter hbefore hminimal Hevent
              hframe hleftReroute (by omega)
              hrerouteOld hrerouteFirst
          · exact RawPostReturnEscapeOutcome.baba
              escape left reroute prior hafter hbefore hminimal
              Hevent hframe hinner hprior hleftReroute
              (by omega) hrerouteOld
        · exact RawPostReturnEscapeOutcome.replay escape left
            hafter hbefore hminimal hframe hleft hnovel
  }⟩

/-- **The first post-return escape is paid or crosses the caller.**

This is the novelty annotation on the concrete returned suffix.  In the
first branch the escape is a globally first productive writer, so its
post-vector is literally in the canonical first-writer history.  In the
second branch its canonical previous write lies on the old side of the
caller contact.  The latter `B-A-B-A` interlacement is the exact remaining
serial obstruction; it is not hidden behind a continuation hypothesis. -/
theorem RawGlobalSerialContinuation.first_escape_paid_or_crosses
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {firstClose horizon : Nat}
    (C : RawGlobalSerialContinuation w N start firstClose)
    (hclose : firstClose < horizon) :
    (∃ escape,
      C.returnTime ≤ escape ∧ escape ≤ firstClose ∧
      RawProductiveAt w N start escape ∧
      (∀ t, C.returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t) ∧
      RawFirstWriterAt w N start escape ∧
      restrictedTonguesAt w N start (escape + 1) ∈
        rawFirstWriterHistory w N start horizon) ∨
    (∃ escape left,
      C.returnTime ≤ escape ∧ escape ≤ firstClose ∧
      RawProductiveAt w N start escape ∧
      (∀ t, C.returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t) ∧
      RawLastWriterFrame w N start left escape ∧
      left ≤ C.repeatTime) := by
  classical
  obtain ⟨escape, hreturn, hcloseEscape, hproductive,
      hminimal, hfirst | ⟨left, hframe, hleft⟩⟩ := C.first_escape
  · left
    refine ⟨escape, hreturn, hcloseEscape, hproductive,
      hminimal, hfirst, ?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨escape, mem_rawFirstWriterTimes_iff.mpr ?_, rfl⟩
    exact ⟨by omega, hfirst⟩
  · right
    exact ⟨escape, left, hreturn, hcloseEscape, hproductive,
      hminimal, hframe, hleft⟩

/-- Proof-relevant form of the first-escape dichotomy, suitable for carrying
through the terminating serial recursion. -/
inductive RawSerialEscapeResolution
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {firstClose : Nat}
    (C : RawGlobalSerialContinuation w N start firstClose)
    (horizon : Nat) : Type
  | paid (escape : Nat)
      (after_return : C.returnTime ≤ escape)
      (before_close : escape ≤ firstClose)
      (productive : RawProductiveAt w N start escape)
      (minimal : ∀ t, C.returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t)
      (first : RawFirstWriterAt w N start escape)
      (in_history :
        restrictedTonguesAt w N start (escape + 1) ∈
          rawFirstWriterHistory w N start horizon) :
      RawSerialEscapeResolution C horizon
  | crosses (escape left : Nat)
      (after_return : C.returnTime ≤ escape)
      (before_close : escape ≤ firstClose)
      (productive : RawProductiveAt w N start escape)
      (minimal : ∀ t, C.returnTime ≤ t → t < escape →
        ¬ RawProductiveAt w N start t)
      (frame : RawLastWriterFrame w N start left escape)
      (crosses_caller : left ≤ C.repeatTime) :
      RawSerialEscapeResolution C horizon

/-- Package `first_escape_paid_or_crosses` as finite recursive evidence. -/
theorem RawGlobalSerialContinuation.resolve_first_escape
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {firstClose horizon : Nat}
    (C : RawGlobalSerialContinuation w N start firstClose)
    (hclose : firstClose < horizon) :
    Nonempty (RawSerialEscapeResolution C horizon) := by
  rcases C.first_escape_paid_or_crosses hclose with
      ⟨escape, hreturn, hcloseEscape, hproductive,
        hminimal, hfirst, hhistory⟩ |
      ⟨escape, left, hreturn, hcloseEscape, hproductive,
        hminimal, hframe, hleft⟩
  · exact ⟨RawSerialEscapeResolution.paid escape hreturn
      hcloseEscape hproductive hminimal hfirst hhistory⟩
  · exact ⟨RawSerialEscapeResolution.crosses escape left hreturn
      hcloseEscape hproductive hminimal hframe hleft⟩

/-! ## Coefficient-one accounting for the extracted reverse -/

/-- The accounting data carried by the actual reverse extracted from a
serial frame.  Its completed return has *exactly* the post-vector of the
contact which turned the train.  Consequently a globally first contact
charges no additional return vector: both the completed return and every
positive depth of the reverse are already in `rawFirstWriterHistory`.

The implication in `first_writer_retrace_zero` is not an extraction
premise.  The enclosing theorem below produces this certificate from the
five raw frames; the implication records the exact accounting consequence
for whichever concrete contact the extraction selected. -/
structure RawSerialReturnAccounting
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (horizon firstClose : Nat) where
  repeatTime : Nat
  returnTime : Nat
  returned : Nat × Tongues
  repeat_before_close : repeatTime < firstClose
  repeat_before_return : repeatTime < returnTime
  return_before_close : returnTime ≤ firstClose
  reaches_return : stepN w returnTime start = some returned
  contact_post_live : (stepN w (repeatTime + 1) start).isSome
  return_vector_eq_contact_post :
    restrictedTonguesAt w N start returnTime =
      restrictedTonguesAt w N start (repeatTime + 1)
  first_writer_return_mem :
    RawFirstWriterAt w N start repeatTime →
      restrictedTonguesAt w N start returnTime ∈
        rawFirstWriterHistory w N start horizon
  first_writer_retrace_zero :
    RawFirstWriterAt w N start repeatTime →
      ∀ times,
        (∀ time, time ∈ times →
          repeatTime < time ∧ time ≤ returnTime) →
        NoveltyCoverOn w N start times
          (rawFirstWriterHistory w N start horizon) 0

/-- **An actual serial reverse is free when its turn is a first writer.**

This is the coefficient-one sharpening of the pointwise retrace theorem.
The completed return is not charged as a separate serial vector: it is
literally the contact's post-vector.  If that contact is globally first,
the whole positive-depth reverse lies in the canonical first-writer history
with novelty budget zero. -/
theorem five_serial_novelties_supply_return_accounting
    {w : Wiring} {N initialEdge horizon : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (H₀ : RawRepeatedWriterNovelAt w N start z₀)
    (H₁ : RawRepeatedWriterNovelAt w N start z₁)
    (H₂ : RawRepeatedWriterNovelAt w N start z₂)
    (H₃ : RawRepeatedWriterNovelAt w N start z₃)
    (H₄ : RawRepeatedWriterNovelAt w N start z₄)
    (hz₀Horizon : z₀ ≤ horizon)
    {a₀ q₀ a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄ : Nat}
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hserial : FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄) :
    Nonempty (RawSerialReturnAccounting w N start horizon z₀) := by
  obtain ⟨g, base, oldEntry, mouthState, q, u, settled, edge,
      repeatTime, caller, _hbefore, hcaller, _hsimple, hgrooved,
      _hcallerLe, hedge, hrepeat, _hrepeatAfterOpen,
      hrepeatBeforeClose, hreturnBeforeClose, hcontact,
      hreturn, hpointwise, _hcover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  let returnTime := repeatTime + caller.length + 1
  let returned : Nat × Tongues := (edge, settled)
  have hreachesReturn : stepN w returnTime start = some returned := by
    dsimp [returnTime, returned]
    rw [show repeatTime + caller.length + 1 =
        repeatTime + (caller.length + 1) by omega,
      stepN_add, hrepeat]
    exact hreturn
  obtain ⟨postPort, hpostLocal⟩ := hpointwise 1 (by omega)
  have hpostGlobal :
      stepN w (repeatTime + 1) start = some (postPort, settled) := by
    rw [stepN_add, hrepeat]
    simpa using hpostLocal
  have hpositiveVector : ∀ time,
      repeatTime < time → time ≤ returnTime →
      restrictedTonguesAt w N start time =
        VectorCount.restrict N settled := by
    intro time hlower hupper
    let d := time - repeatTime
    have hdPositive : 0 < d := by
      dsimp [d]
      omega
    have hdBound : d ≤ caller.length + 1 := by
      dsimp [d, returnTime] at *
      omega
    have htime : repeatTime + d = time := by
      dsimp [d]
      omega
    obtain ⟨port, hlocal⟩ := hpointwise d hdBound
    have hglobal : stepN w time start = some (port, settled) := by
      rw [← htime, stepN_add, hrepeat]
      simpa [Nat.ne_of_gt hdPositive] using hlocal
    simp [restrictedTonguesAt, tonguesAt, hglobal]
  have hpostVector :
      restrictedTonguesAt w N start (repeatTime + 1) =
        VectorCount.restrict N settled :=
    hpositiveVector (repeatTime + 1) (by omega) (by
      dsimp [returnTime]
      omega)
  have hreturnVector :
      restrictedTonguesAt w N start returnTime =
        VectorCount.restrict N settled := by
    exact hpositiveVector returnTime (by
      dsimp [returnTime]
      omega) (Nat.le_refl _)
  have hrepeatHorizon : repeatTime < horizon := by omega
  have hcontactHistory : RawFirstWriterAt w N start repeatTime →
      VectorCount.restrict N settled ∈
        rawFirstWriterHistory w N start horizon := by
    intro hfirst
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    refine ⟨repeatTime, ?_, hpostVector⟩
    exact mem_rawFirstWriterTimes_iff.mpr
      ⟨hrepeatHorizon, hfirst⟩
  exact ⟨{
    repeatTime := repeatTime
    returnTime := returnTime
    returned := returned
    repeat_before_close := hrepeatBeforeClose
    repeat_before_return := by
      dsimp [returnTime]
      omega
    return_before_close := by
      simpa [returnTime, Nat.add_assoc] using hreturnBeforeClose
    reaches_return := hreachesReturn
    contact_post_live := by simp [hpostGlobal]
    return_vector_eq_contact_post := hreturnVector.trans hpostVector.symm
    first_writer_return_mem := by
      intro hfirst
      rw [hreturnVector]
      exact hcontactHistory hfirst
    first_writer_retrace_zero := by
      intro hfirst times htimes
      refine ⟨[], by simp, ?_⟩
      intro time htime
      simp only [List.append_nil]
      have hb := htimes time htime
      rw [hpositiveVector time hb.1 hb.2]
      exact hcontactHistory hfirst
  }⟩

/-- Every extracted serial return has one of exactly three accounting
outcomes.

* a globally first turning write pays for the return in the `N`-sized
  first-writer history;
* a non-novel (or non-productive) turn makes the return replay an earlier
  vector; or
* the turn itself is a strictly earlier repeated-writer novelty.

The third branch is the recursive one.  It decreases in raw time by
`repeat_before_close`; no arbitrary continuation premise is introduced. -/
theorem RawSerialReturnAccounting.first_or_replay_or_earlier_repeated
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {horizon close : Nat}
    (A : RawSerialReturnAccounting w N start horizon close) :
    (RawFirstWriterAt w N start A.repeatTime ∧
      restrictedTonguesAt w N start A.returnTime ∈
        rawFirstWriterHistory w N start horizon) ∨
    (restrictedTonguesAt w N start A.returnTime ∈
      (List.range (A.repeatTime + 1)).map
        (restrictedTonguesAt w N start)) ∨
    RawRepeatedWriterNovelAt w N start A.repeatTime := by
  classical
  by_cases hproductive : RawProductiveAt w N start A.repeatTime
  · by_cases hfirst : RawFirstWriterAt w N start A.repeatTime
    · exact Or.inl ⟨hfirst, A.first_writer_return_mem hfirst⟩
    · by_cases hnovel : RawNovelAt w N start A.repeatTime
      · exact Or.inr (Or.inr ⟨hproductive, hfirst, hnovel⟩)
      · right
        left
        rw [A.return_vector_eq_contact_post]
        exact Classical.not_not.mp hnovel
  · right
    left
    have hsame :
        restrictedTonguesAt w N start (A.repeatTime + 1) =
          restrictedTonguesAt w N start A.repeatTime := by
      apply Classical.byContradiction
      intro hne
      exact hproductive ⟨A.contact_post_live, hne⟩
    apply List.mem_map.mpr
    refine ⟨A.repeatTime, List.mem_range.mpr (by omega), ?_⟩
    exact (A.return_vector_eq_contact_post.trans hsame).symm

/-- A finite proof object resolving the accounting source of the exact
return extracted from an actual serial close.  Every recursive node points
to a strictly earlier repeated novelty.  A leaf return is either paid by one
globally first writer or is already a replay of an earlier vector.  This
does not by itself account for the outer close's globally novel post-vector. -/
inductive RawSerialChargeResolution
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (horizon : Nat) : Nat → Type
  | first {close : Nat}
      (account : RawSerialReturnAccounting w N start horizon close)
      (writer : RawFirstWriterAt w N start account.repeatTime)
      (paid : restrictedTonguesAt w N start account.returnTime ∈
        rawFirstWriterHistory w N start horizon) :
      RawSerialChargeResolution w N start horizon close
  | replay {close : Nat}
      (account : RawSerialReturnAccounting w N start horizon close)
      (seen : restrictedTonguesAt w N start account.returnTime ∈
        (List.range (account.repeatTime + 1)).map
          (restrictedTonguesAt w N start)) :
      RawSerialChargeResolution w N start horizon close
  | step {close : Nat}
      (account : RawSerialReturnAccounting w N start horizon close)
      (earlier : RawRepeatedWriterNovelAt w N start account.repeatTime)
      (tail : RawSerialChargeResolution w N start horizon
        account.repeatTime) :
      RawSerialChargeResolution w N start horizon close

/-- Bounded implementation of the strictly-decreasing serial resolution. -/
private theorem rawSerialChargeResolution_bounded
    {w : Wiring} {N initialEdge horizon laterOpen laterReroute
      laterClose : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (Later : RawRepeatedWriterNovelAt w N start laterClose)
    (LaterFrame : RawNovelClosingFrame w N start
      laterOpen laterReroute laterClose) :
    ∀ bound close,
      close ≤ bound → close ≤ horizon → close ≤ laterOpen →
      RawRepeatedWriterNovelAt w N start close →
      Nonempty (RawSerialChargeResolution w N start horizon close) := by
  intro bound
  induction bound with
  | zero =>
      intro close hcloseBound _hcloseHorizon _hcloseLater H
      have hcloseZero : close = 0 := by omega
      subst close
      have hfirst : RawFirstWriterAt w N start 0 := by
        refine ⟨H.1, ?_⟩
        intro j hj
        omega
      exact (H.2.1 hfirst).elim
  | succ bound ih =>
      intro close hcloseBound hcloseHorizon hcloseLater H
      obtain ⟨left, reroute, Frame⟩ := H.novelClosingFrame hN
      obtain ⟨account⟩ :=
        five_serial_novelties_supply_return_accounting
          hN hentry H Later Later Later Later hcloseHorizon
          Frame LaterFrame LaterFrame LaterFrame LaterFrame
          (Or.inl hcloseLater)
      rcases account.first_or_replay_or_earlier_repeated with
        hfirst | hseen | hearlier
      · exact ⟨RawSerialChargeResolution.first
          account hfirst.1 hfirst.2⟩
      · exact ⟨RawSerialChargeResolution.replay account hseen⟩
      · have hrepeatBound : account.repeatTime ≤ bound := by
          have hstrict := account.repeat_before_close
          omega
        have hrepeatHorizon : account.repeatTime ≤ horizon := by
          exact Nat.le_trans (Nat.le_of_lt account.repeat_before_close)
            hcloseHorizon
        have hrepeatLater : account.repeatTime ≤ laterOpen := by
          exact Nat.le_trans (Nat.le_of_lt account.repeat_before_close)
            hcloseLater
        obtain ⟨tail⟩ := ih account.repeatTime hrepeatBound
          hrepeatHorizon hrepeatLater hearlier
        exact ⟨RawSerialChargeResolution.step account hearlier tail⟩

/-- **Actual recursive serial accounting, with no continuation premise.**

Fix one later raw novelty frame.  Every earlier repeated novelty serially
separated from that frame gives an exact return with a finite accounting
resolution.  At each recursive node the exact reverse returns on its
contact's post-vector; a first writer pays for that return in
`rawFirstWriterHistory`, a replay costs nothing, and the only remaining
source is a strictly earlier repeated novelty.  Recursion is therefore
well-founded on the raw close time itself.  The globally novel outer close
remains a separate obligation, exposed by the six-event checkpoint below. -/
theorem RawRepeatedWriterNovelAt.resolve_serial_charge
    {w : Wiring} {N initialEdge horizon laterOpen laterReroute
      laterClose close : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (H : RawRepeatedWriterNovelAt w N start close)
    (hcloseHorizon : close ≤ horizon)
    (Later : RawRepeatedWriterNovelAt w N start laterClose)
    (LaterFrame : RawNovelClosingFrame w N start
      laterOpen laterReroute laterClose)
    (hserial : close ≤ laterOpen) :
    Nonempty (RawSerialChargeResolution w N start horizon close) := by
  exact rawSerialChargeResolution_bounded hN hentry Later LaterFrame
    close close (Nat.le_refl _) hcloseHorizon hserial H

/-- Expose the root return accounted for by a serial charge resolution. -/
theorem RawSerialChargeResolution.root_account
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {horizon close : Nat}
    (R : RawSerialChargeResolution w N start horizon close) :
    ∃ A : RawSerialReturnAccounting w N start horizon close,
      A.returnTime ≤ close := by
  cases R with
  | first account _writer _paid =>
      exact ⟨account, account.return_before_close⟩
  | replay account _seen =>
      exact ⟨account, account.return_before_close⟩
  | step account _earlier _tail =>
      exact ⟨account, account.return_before_close⟩

/-- A globally novel close post-vector differs from every trajectory vector
at a time no later than the close itself. -/
theorem RawRepeatedWriterNovelAt.post_ne_at_or_before
    {w : Wiring} {N close t : Nat} {start : Nat × Tongues}
    (H : RawRepeatedWriterNovelAt w N start close)
    (ht : t ≤ close) :
    restrictedTonguesAt w N start (close + 1) ≠
      restrictedTonguesAt w N start t := by
  intro heq
  apply H.2.2
  apply List.mem_map.mpr
  exact ⟨t, List.mem_range.mpr (by omega), heq.symm⟩

/-! ## Six-event serial checkpoint -/

/-- Eliminator form of the canonical six-event no-gap facts.  Any repeated
novelty no later than the sixth event is one of the six named endpoints;
events before the first endpoint are excluded by `first0`. -/
theorem repeated_event_eq_one_of_six
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z₀ z₁ z₂ z₃ z₄ z₅ k : Nat}
    (first₀ : ∀ j, j < z₀ →
      ¬ RawRepeatedWriterNovelAt w N start j)
    (no_event₀₁ : ∀ j, z₀ < j → j < z₁ →
      ¬ RawRepeatedWriterNovelAt w N start j)
    (no_event₁₂ : ∀ j, z₁ < j → j < z₂ →
      ¬ RawRepeatedWriterNovelAt w N start j)
    (no_event₂₃ : ∀ j, z₂ < j → j < z₃ →
      ¬ RawRepeatedWriterNovelAt w N start j)
    (no_event₃₄ : ∀ j, z₃ < j → j < z₄ →
      ¬ RawRepeatedWriterNovelAt w N start j)
    (no_event₄₅ : ∀ j, z₄ < j → j < z₅ →
      ¬ RawRepeatedWriterNovelAt w N start j)
    (H : RawRepeatedWriterNovelAt w N start k)
    (hhi : k ≤ z₅) :
    k = z₀ ∨ k = z₁ ∨ k = z₂ ∨
      k = z₃ ∨ k = z₄ ∨ k = z₅ := by
  by_cases hk₀ : k = z₀
  · exact Or.inl hk₀
  by_cases hbefore₀ : k < z₀
  · exact (first₀ k hbefore₀ H).elim
  have hz₀k : z₀ < k := by omega
  by_cases hk₁ : k = z₁
  · exact Or.inr (Or.inl hk₁)
  by_cases hbefore₁ : k < z₁
  · exact (no_event₀₁ k hz₀k hbefore₁ H).elim
  have hz₁k : z₁ < k := by omega
  by_cases hk₂ : k = z₂
  · exact Or.inr (Or.inr (Or.inl hk₂))
  by_cases hbefore₂ : k < z₂
  · exact (no_event₁₂ k hz₁k hbefore₂ H).elim
  have hz₂k : z₂ < k := by omega
  by_cases hk₃ : k = z₃
  · exact Or.inr (Or.inr (Or.inr (Or.inl hk₃)))
  by_cases hbefore₃ : k < z₃
  · exact (no_event₂₃ k hz₂k hbefore₃ H).elim
  have hz₃k : z₃ < k := by omega
  by_cases hk₄ : k = z₄
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hk₄))))
  by_cases hbefore₄ : k < z₄
  · exact (no_event₃₄ k hz₃k hbefore₄ H).elim
  have hz₄k : z₄ < k := by omega
  have hk₅ : k = z₅ := by
    by_cases hbefore₅ : k < z₅
    · exact (no_event₄₅ k hz₄k hbefore₅ H).elim
    · omega
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hk₅))))

/-- What the present argument retains from an actual six-event serial
branch.  The selected later repeated novelty survives in an actually reached
suffix and its raw close-time strictly decreases.  The exact reverse itself
has a finite first-writer/replay resolution, and the first productive escape
is either paid by a globally first writer or exposes a caller-crossing
last-writer frame.

The final field deliberately records the unresolved accounting fact: the
serial head's globally novel close is not in first-writer history.  Thus the
strict suffix currently preserves one repeated novelty, not a fresh
six-event counterexample.  Closing that gap requires turning the
caller-crossing interlacement into the four-state tail or showing that one
of the other five events is absorbed. -/
structure RawSixEventSerialCheckpoint
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (z₀ z₁ z₂ z₃ z₄ z₅ horizon : Nat) where
  first_event : RawRepeatedWriterNovelAt w N start z₀
  serial_head : RawRepeatedWriterNovelAt w N start z₁
  first_before_head : z₀ < z₁
  order₁₂ : z₁ < z₂
  order₂₃ : z₂ < z₃
  order₃₄ : z₃ < z₄
  order₄₅ : z₄ < z₅
  continuation : RawGlobalSerialContinuation w N start z₁
  strict_suffix_close :
    continuation.selected.closeTime - continuation.returnTime <
      continuation.selected.closeTime
  preserved_local_event :
    RawRepeatedWriterNovelAt w N continuation.returned
      (continuation.selected.closeTime - continuation.returnTime)
  return_resolution :
    RawSerialChargeResolution w N start horizon z₁
  resolved_return_avoids_selected_closes :
    ∃ A : RawSerialReturnAccounting w N start horizon z₁,
      A.returnTime ≤ z₁ ∧
      restrictedTonguesAt w N start (z₁ + 1) ≠
        restrictedTonguesAt w N start A.returnTime ∧
      restrictedTonguesAt w N start (z₂ + 1) ≠
        restrictedTonguesAt w N start A.returnTime ∧
      restrictedTonguesAt w N start (z₃ + 1) ≠
        restrictedTonguesAt w N start A.returnTime ∧
      restrictedTonguesAt w N start (z₄ + 1) ≠
        restrictedTonguesAt w N start A.returnTime ∧
      restrictedTonguesAt w N start (z₅ + 1) ≠
        restrictedTonguesAt w N start A.returnTime
  escape_resolution :
    RawSerialEscapeResolution continuation horizon
  canonical_repeated_endpoint :
    ∀ k, k ≤ z₅ → RawRepeatedWriterNovelAt w N start k →
      k = z₀ ∨ k = z₁ ∨ k = z₂ ∨
        k = z₃ ∨ k = z₄ ∨ k = z₅
  serial_head_not_first_history :
    restrictedTonguesAt w N start (z₁ + 1) ∉
      rawFirstWriterHistory w N start horizon

/-- The exact canonical alternatives left by a six-event serial checkpoint.
The only uncharged branch is the final `baba` constructor, whose repeated
novel escape is one of the six selected endpoints. -/
inductive RawCanonicalSerialEscapeOutcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z₀ z₁ z₂ z₃ z₄ z₅ horizon : Nat}
    (S : RawSixEventSerialCheckpoint w N start
      z₀ z₁ z₂ z₃ z₄ z₅ horizon) : Prop
  | paid (escape : Nat)
      (before_head : escape ≤ z₁)
      (first : RawFirstWriterAt w N start escape) :
      RawCanonicalSerialEscapeOutcome S
  | replay (escape : Nat)
      (before_head : escape ≤ z₁)
      (not_novel : ¬ RawNovelAt w N start escape) :
      RawCanonicalSerialEscapeOutcome S
  | fresh_old_side (escape left reroute : Nat)
      (before_head : escape ≤ z₁)
      (event : RawRepeatedWriterNovelAt w N start escape)
      (selected : escape = z₀ ∨ escape = z₁ ∨ escape = z₂ ∨
        escape = z₃ ∨ escape = z₄ ∨ escape = z₅)
      (outer : RawLastWriterFrame w N start left escape)
      (left_before_reroute : left < reroute)
      (reroute_before_escape : reroute < escape)
      (reroute_first : RawFirstWriterAt w N start reroute) :
      RawCanonicalSerialEscapeOutcome S
  | baba (escape left reroute prior : Nat)
      (before_head : escape ≤ z₁)
      (event : RawRepeatedWriterNovelAt w N start escape)
      (selected : escape = z₀ ∨ escape = z₁ ∨ escape = z₂ ∨
        escape = z₃ ∨ escape = z₄ ∨ escape = z₅)
      (outer : RawLastWriterFrame w N start left escape)
      (inner : RawLastWriterFrame w N start prior reroute)
      (prior_before_left : prior < left)
      (left_before_reroute : left < reroute)
      (reroute_before_escape : reroute < escape)
      (inner_replay_or_first_endpoint :
        ¬ RawNovelAt w N start reroute ∨ reroute = z₀) :
      RawCanonicalSerialEscapeOutcome S

/-- Collapse the same-witness post-return classification with all five
canonical no-gap facts retained by the checkpoint. -/
theorem RawSixEventSerialCheckpoint.canonical_escape_outcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z₀ z₁ z₂ z₃ z₄ z₅ horizon : Nat}
    (S : RawSixEventSerialCheckpoint w N start
      z₀ z₁ z₂ z₃ z₄ z₅ horizon) :
    RawCanonicalSerialEscapeOutcome S := by
  have hz₀z₁ := S.first_before_head
  have hz₁z₂ := S.order₁₂
  have hz₂z₃ := S.order₂₃
  have hz₃z₄ := S.order₃₄
  have hz₄z₅ := S.order₄₅
  have hz₁z₅ : z₁ < z₅ := by
    exact Nat.lt_trans hz₁z₂
      (Nat.lt_trans hz₂z₃
        (Nat.lt_trans hz₃z₄ hz₄z₅))
  cases S.continuation.escape_outcome with
  | paid escape _hafter hbefore _hproductive _hminimal hfirst =>
      exact RawCanonicalSerialEscapeOutcome.paid escape hbefore hfirst
  | replay escape _left _hafter hbefore _hminimal _hframe _hcross hnot =>
      exact RawCanonicalSerialEscapeOutcome.replay escape hbefore hnot
  | fresh_old_side escape left reroute hafter hbefore _hminimal
      hevent houter hleftReroute hrerouteEscape _hold hfirst =>
      exact RawCanonicalSerialEscapeOutcome.fresh_old_side
        escape left reroute hbefore hevent
        (S.canonical_repeated_endpoint escape
          (Nat.le_trans hbefore (Nat.le_of_lt hz₁z₅)) hevent)
        houter hleftReroute hrerouteEscape hfirst
  | baba escape left reroute prior hafter hbefore _hminimal
      hevent houter hinner hprior hleftReroute hrerouteEscape hold =>
      have hinnerReplayOrFirst :
          ¬ RawNovelAt w N start reroute ∨ reroute = z₀ := by
        by_cases hnovel : RawNovelAt w N start reroute
        · right
          have hnotFirst : ¬ RawFirstWriterAt w N start reroute := by
            intro hfirst
            exact hfirst.2 prior hinner.order
              hinner.open_productive hinner.same_writer
          have heventInner :
              RawRepeatedWriterNovelAt w N start reroute :=
            ⟨hinner.close_productive, hnotFirst, hnovel⟩
          have hrerouteZ₁ : reroute < z₁ := by
            have hrepeatZ₁ : S.continuation.repeatTime < z₁ :=
              Nat.lt_of_lt_of_le S.continuation.repeat_before_return
                S.continuation.return_before_first_close
            exact Nat.lt_of_le_of_lt hold hrepeatZ₁
          have hrerouteZ₅ : reroute ≤ z₅ :=
            Nat.le_trans (Nat.le_of_lt hrerouteZ₁)
              (Nat.le_of_lt hz₁z₅)
          rcases S.canonical_repeated_endpoint reroute hrerouteZ₅
              heventInner with h₀ | h₁ | h₂ | h₃ | h₄ | h₅
          · exact h₀
          · omega
          · omega
          · omega
          · omega
          · omega
        · exact Or.inl hnovel
      exact RawCanonicalSerialEscapeOutcome.baba
        escape left reroute prior hbefore hevent
        (S.canonical_repeated_endpoint escape
          (Nat.le_trans hbefore (Nat.le_of_lt hz₁z₅)) hevent)
        houter hinner hprior hleftReroute hrerouteEscape
        hinnerReplayOrFirst

/-- **Unconditional six-event serial checkpoint.**

For six chronologically ordered repeated-writer novelties whose last five
fall in the serial branch of `FiveFrameObstruction`, this theorem constructs
all novelty accounting that is currently justified by the raw dynamics:

* the exact return is recursively resolved on a strictly earlier raw time;
* its first subsequent productive escape is paid or crosses the caller; and
* one certified later repeated novelty rebases to a strictly smaller local
  close-time.

No continuation, repair, or tail premise occurs in the statement. -/
theorem six_event_serial_branch_checkpoint
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    {z₀ z₁ z₂ z₃ z₄ z₅ : Nat}
    (h₀₁ : z₀ < z₁) (h₁₂ : z₁ < z₂)
    (h₂₃ : z₂ < z₃) (h₃₄ : z₃ < z₄)
    (h₄₅ : z₄ < z₅)
    (H₀ : RawRepeatedWriterNovelAt w N start z₀)
    (H₁ : RawRepeatedWriterNovelAt w N start z₁)
    (H₂ : RawRepeatedWriterNovelAt w N start z₂)
    (H₃ : RawRepeatedWriterNovelAt w N start z₃)
    (H₄ : RawRepeatedWriterNovelAt w N start z₄)
    (H₅ : RawRepeatedWriterNovelAt w N start z₅)
    (first₀ : ∀ k, k < z₀ →
      ¬ RawRepeatedWriterNovelAt w N start k)
    (no_event₀₁ : ∀ k, z₀ < k → k < z₁ →
      ¬ RawRepeatedWriterNovelAt w N start k)
    (no_event₁₂ : ∀ k, z₁ < k → k < z₂ →
      ¬ RawRepeatedWriterNovelAt w N start k)
    (no_event₂₃ : ∀ k, z₂ < k → k < z₃ →
      ¬ RawRepeatedWriterNovelAt w N start k)
    (no_event₃₄ : ∀ k, z₃ < k → k < z₄ →
      ¬ RawRepeatedWriterNovelAt w N start k)
    (no_event₄₅ : ∀ k, z₄ < k → k < z₅ →
      ¬ RawRepeatedWriterNovelAt w N start k)
    {a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄ a₅ q₅ : Nat}
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (F₅ : RawNovelClosingFrame w N start a₅ q₅ z₅)
    (hserial : FiveFrameSerialBreak z₁ a₂ a₃ a₄ a₅) :
    Nonempty (RawSixEventSerialCheckpoint w N start
      z₀ z₁ z₂ z₃ z₄ z₅ (z₅ + 1)) := by
  obtain ⟨continuation⟩ :=
    five_serial_novelties_supply_global_continuation
      hN hentry H₁ H₂ H₃ H₄ H₅ F₁ F₂ F₃ F₄ F₅ hserial
  have hreturnLeSelectedClose :
      continuation.returnTime ≤ continuation.selected.closeTime :=
    Nat.le_trans continuation.return_before_open
      (Nat.le_of_lt continuation.selected.frame.outer.order)
  have hstrict :
      continuation.selected.closeTime - continuation.returnTime <
        continuation.selected.closeTime :=
    Nat.sub_lt_of_pos_le continuation.return_positive
      hreturnLeSelectedClose
  obtain ⟨returnResolution⟩ :=
    H₁.resolve_serial_charge
      (horizon := z₅ + 1) hN hentry (by omega)
      continuation.selected.event continuation.selected.frame
        continuation.selected.after_first_close
  obtain ⟨escapeResolution⟩ :=
    continuation.resolve_first_escape (horizon := z₅ + 1) (by omega)
  obtain ⟨rootAccount, hrootBefore⟩ :=
    returnResolution.root_account
  have hheadMem :
      z₁ ∈ rawRepeatedWriterNovelTimes w N start (z₅ + 1) :=
    mem_rawRepeatedWriterNovelTimes_iff.mpr ⟨by omega, H₁⟩
  have hheadNotHistory :=
    repeatedWriterPost_not_mem_firstHistory hN hheadMem
  exact ⟨{
    first_event := H₀
    serial_head := H₁
    first_before_head := h₀₁
    order₁₂ := h₁₂
    order₂₃ := h₂₃
    order₃₄ := h₃₄
    order₄₅ := h₄₅
    continuation := continuation
    strict_suffix_close := hstrict
    preserved_local_event := continuation.local_close_event
    return_resolution := returnResolution
    resolved_return_avoids_selected_closes := by
      refine ⟨rootAccount, hrootBefore, ?_, ?_, ?_, ?_, ?_⟩
      · exact H₁.post_ne_at_or_before hrootBefore
      · exact H₂.post_ne_at_or_before (by omega)
      · exact H₃.post_ne_at_or_before (by omega)
      · exact H₄.post_ne_at_or_before (by omega)
      · exact H₅.post_ne_at_or_before (by omega)
    escape_resolution := escapeResolution
    canonical_repeated_endpoint := by
      intro k hbefore Hk
      exact repeated_event_eq_one_of_six
        first₀
        no_event₀₁ no_event₁₂ no_event₂₃ no_event₃₄ no_event₄₅
        Hk hbefore
    serial_head_not_first_history := hheadNotHistory
  }⟩

/-! ## A terminating serial-chain invariant -/

/-- One raw repeated-writer novelty together with one of its actual closing
frames. -/
structure RawFramedNovelty
    (w : Wiring) (N : Nat) (start : Nat × Tongues) where
  openTime : Nat
  rerouteTime : Nat
  closeTime : Nat
  event : RawRepeatedWriterNovelAt w N start closeTime
  frame : RawNovelClosingFrame w N start openTime rerouteTime closeTime

/-- Rebase a framed novelty at a boundary no later than its last-writer
opening.  The closing time is translated exactly.  Re-extracting the local
open frame may move its opening later, but never earlier than the translated
certified opening. -/
theorem RawFramedNovelty.rebase
    {w : Wiring} {N shift : Nat}
    {start middle : Nat × Tongues}
    (F : RawFramedNovelty w N start)
    (hshift : shift ≤ F.openTime)
    (hreach : stepN w shift start = some middle)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) :
    ∃ G : RawFramedNovelty w N middle,
      G.closeTime = F.closeTime - shift ∧
      F.openTime - shift ≤ G.openTime := by
  let localOpen := F.openTime - shift
  let localClose := F.closeTime - shift
  have hopenEq : shift + localOpen = F.openTime := by
    dsimp [localOpen]
    omega
  have hframeOrder : F.openTime < F.closeTime := F.frame.outer.order
  have hcloseEq : shift + localClose = F.closeTime := by
    dsimp [localClose]
    omega
  have hlocalOpen : RawProductiveAt w N middle localOpen := by
    apply rawProductiveAt_sub_of_reach hreach
    simpa [hopenEq] using F.frame.outer.open_productive
  have hlocalCloseProductive :
      RawProductiveAt w N middle localClose := by
    apply rawProductiveAt_sub_of_reach hreach
    simpa [hcloseEq] using F.event.1
  have hlocalCloseNovel : RawNovelAt w N middle localClose := by
    apply rawNovelAt_add_rebase hreach
    simpa [hcloseEq] using F.event.2.2
  have hopenLive : (stepN w localOpen middle).isSome := by
    obtain ⟨post, hpost⟩ :=
      Option.isSome_iff_exists.mp hlocalOpen.1
    obtain ⟨before, hbefore⟩ := stepN_prefix_some
      (d := localOpen) (K := localOpen + 1) (by omega) hpost
    simp [hbefore]
  have hcloseLive : (stepN w localClose middle).isSome := by
    obtain ⟨post, hpost⟩ :=
      Option.isSome_iff_exists.mp hlocalCloseProductive.1
    obtain ⟨before, hbefore⟩ := stepN_prefix_some
      (d := localClose) (K := localClose + 1) (by omega) hpost
    simp [hbefore]
  have hopenWriter := rawWriterAt_add_of_reach hreach hopenLive
  have hcloseWriter := rawWriterAt_add_of_reach hreach hcloseLive
  have hlocalSameWriter :
      rawWriterAt w middle localOpen =
        rawWriterAt w middle localClose := by
    rw [hopenEq] at hopenWriter
    rw [hcloseEq] at hcloseWriter
    exact hopenWriter.symm.trans
      (F.frame.outer.same_writer.trans hcloseWriter)
  have hlocalOpenClose : localOpen < localClose := by
    dsimp [localOpen, localClose]
    omega
  have hlocalNotFirst :
      ¬ RawFirstWriterAt w N middle localClose := by
    intro hfirst
    exact hfirst.2 localOpen hlocalOpenClose hlocalOpen
      hlocalSameWriter
  have hlocalEvent :
      RawRepeatedWriterNovelAt w N middle localClose :=
    ⟨hlocalCloseProductive, hlocalNotFirst, hlocalCloseNovel⟩
  obtain ⟨left, reroute, localFrame⟩ :=
    hlocalEvent.novelClosingFrame hN
  have hopenLower : localOpen ≤ left := by
    apply Classical.byContradiction
    intro hnot
    have hleftOpen : left < localOpen := by omega
    have hne := localFrame.outer.no_same_writer_between
      localOpen hleftOpen hlocalOpenClose hlocalOpen
    exact hne hlocalSameWriter
  exact ⟨{
    openTime := left
    rerouteTime := reroute
    closeTime := localClose
    event := hlocalEvent
    frame := localFrame
  }, rfl, hopenLower⟩

/-- A nonempty list of framed novelties is serial when each frame closes no
later than the next frame opens. -/
inductive RawSerialFrameList
    (w : Wiring) (N : Nat) (start : Nat × Tongues) :
    List (RawFramedNovelty w N start) → Prop
  | one (F : RawFramedNovelty w N start) :
      RawSerialFrameList w N start [F]
  | cons {F G : RawFramedNovelty w N start}
      {rest : List (RawFramedNovelty w N start)}
      (serial : F.closeTime ≤ G.openTime)
      (tail : RawSerialFrameList w N start (G :: rest)) :
      RawSerialFrameList w N start (F :: G :: rest)

/-- Output of rebasing an entire serial list.  The translated list has the
same length; the first translated opening can only move later, and its close
is translated exactly. -/
structure RawRebasedSerialFrameList
    {w : Wiring} {N shift : Nat}
    {start middle : Nat × Tongues}
    (head : RawFramedNovelty w N start)
    (rest : List (RawFramedNovelty w N start)) where
  localHead : RawFramedNovelty w N middle
  localRest : List (RawFramedNovelty w N middle)
  chain : RawSerialFrameList w N middle (localHead :: localRest)
  length_eq :
    (localHead :: localRest).length = (head :: rest).length
  head_close_eq : localHead.closeTime = head.closeTime - shift
  head_open_lower : head.openTime - shift ≤ localHead.openTime

/-- Every remaining frame of a serial list really rebases after the exact
return.  Serial separation is preserved because closes translate exactly
while openings may only move later. -/
theorem RawSerialFrameList.rebase
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {frames : List (RawFramedNovelty w N start)}
    (H : RawSerialFrameList w N start frames)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) :
    ∀ {shift : Nat} {middle : Nat × Tongues},
      stepN w shift start = some middle →
      match frames with
      | [] => True
      | head :: rest => shift ≤ head.openTime →
          Nonempty (RawRebasedSerialFrameList
            (shift := shift) (middle := middle) head rest) := by
  induction H with
  | one F =>
      intro shift middle hreach
      simp only
      intro hshift
      obtain ⟨localF, hclose, hopen⟩ :=
        F.rebase hshift hreach hN
      exact ⟨{
        localHead := localF
        localRest := []
        chain := RawSerialFrameList.one localF
        length_eq := by simp
        head_close_eq := hclose
        head_open_lower := hopen
      }⟩
  | @cons F G rest hserial tail ih =>
      intro shift middle hreach
      simp only
      intro hshift
      obtain ⟨localF, hcloseF, hopenF⟩ :=
        F.rebase hshift hreach hN
      have hshiftG : shift ≤ G.openTime := by
        exact Nat.le_trans hshift
          (Nat.le_trans (Nat.le_of_lt F.frame.outer.order) hserial)
      have htailRebase := ih hreach
      simp only at htailRebase
      obtain ⟨localTail⟩ := htailRebase hshiftG
      have hlocalSerial :
          localF.closeTime ≤ localTail.localHead.openTime := by
        rw [hcloseF]
        exact Nat.le_trans (by omega) localTail.head_open_lower
      exact ⟨{
        localHead := localF
        localRest := localTail.localHead :: localTail.localRest
        chain := RawSerialFrameList.cons hlocalSerial localTail.chain
        length_eq := by
          have hlen := localTail.length_eq
          simp only [List.length_cons]
          simp only [List.length_cons] at hlen
          omega
        head_close_eq := hcloseF
        head_open_lower := hopenF
      }⟩

/-- The actual nested-return computation extracted from a finite serial
frame list.  Every `cons` contains a reached exact-return configuration and
then a recursively constructed tail on a strictly shorter frame list. -/
inductive RawSerialTermination (w : Wiring) (N : Nat) :
    (Nat × Tongues) → Nat → Type
  | last {start : Nat × Tongues}
      (frame : RawFramedNovelty w N start) :
      RawSerialTermination w N start 1
  | cons {start returned : Nat × Tongues} {depth : Nat}
      (head : RawFramedNovelty w N start)
      (returnTime entryEdge : Nat)
      (return_positive : 0 < returnTime)
      (return_before_close : returnTime ≤ head.closeTime)
      (reaches_return : stepN w returnTime start = some returned)
      (entry_link : w.link entryEdge = some returned.1)
      (tail : RawSerialTermination w N returned depth) :
      RawSerialTermination w N start (depth + 1)

/-- Two serially separated framed novelties force the concrete exact return
used by the recursive construction.  The second frame is duplicated only to
instantiate the already proved five-frame disjunction; no distinctness or
finite-`N` enumeration is involved. -/
theorem two_serial_frames_exact_return
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (F G : RawFramedNovelty w N start)
    (hserial : F.closeTime ≤ G.openTime) :
    ∃ returned returnTime entryEdge,
      0 < returnTime ∧
      stepN w returnTime start = some returned ∧
      w.link entryEdge = some returned.1 ∧
      returnTime ≤ F.closeTime ∧
      returnTime ≤ G.openTime := by
  obtain ⟨g, base, oldEntry, mouthState, q, old, settled, edge,
      repeatTime, caller, _hbefore, _hcaller, _hsimple, _hgrooved,
      _hcallerLe, hedge, hrepeat, _hrepeatAfterOpen,
      _hrepeatBeforeClose, hreturnBeforeClose, _hcontact,
      hreturn, _hpointwise, _hcover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry F.event G.event G.event G.event G.event
        F.frame G.frame G.frame G.frame G.frame (Or.inl hserial)
  let returnTime := repeatTime + caller.length + 1
  let returned : Nat × Tongues := (edge, settled)
  have hreaches : stepN w returnTime start = some returned := by
    dsimp [returnTime, returned]
    rw [show repeatTime + caller.length + 1 =
        repeatTime + (caller.length + 1) by omega,
      stepN_add, hrepeat]
    exact hreturn
  refine ⟨returned, returnTime, g, ?_, hreaches, ?_, ?_, ?_⟩
  · dsimp [returnTime]
    omega
  · dsimp [returned]
    exact w.symm _ _ hedge
  · simpa [returnTime, Nat.add_assoc] using hreturnBeforeClose
  · exact Nat.le_trans (by
      simpa [returnTime, Nat.add_assoc] using hreturnBeforeClose) hserial

/-- Bounded recursion used only to justify structural termination.  The
bound is the actual list length; every recursive call receives the rebased
tail, whose length is one smaller. -/
private theorem serialFrameList_termination_bounded
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) :
    ∀ bound start initialEdge frames,
      frames.length ≤ bound →
      RawSerialFrameList w N start frames →
      w.link initialEdge = some start.1 →
      Nonempty (RawSerialTermination w N start frames.length) := by
  intro bound
  induction bound with
  | zero =>
      intro start initialEdge frames hlength H _hentry
      cases H with
      | one F => simp at hlength
      | cons hserial tail => simp at hlength
  | succ bound ih =>
      intro start initialEdge frames hlength H hentry
      cases H with
      | one F =>
          exact ⟨by simpa using RawSerialTermination.last F⟩
      | @cons F G rest hserial tail =>
          obtain ⟨returned, returnTime, newEntryEdge,
              hpositive, hreaches, hnewEntry,
              hbeforeClose, hbeforeNext⟩ :=
            two_serial_frames_exact_return hN hentry F G hserial
          obtain ⟨rebased⟩ :=
            tail.rebase hN hreaches hbeforeNext
          have htailLength :
              (rebased.localHead :: rebased.localRest).length ≤ bound := by
            rw [rebased.length_eq]
            simp only [List.length_cons] at hlength ⊢
            omega
          obtain ⟨tailTermination⟩ :=
            ih returned newEntryEdge
              (rebased.localHead :: rebased.localRest)
              htailLength rebased.chain hnewEntry
          have hbuilt := RawSerialTermination.cons F
            returnTime newEntryEdge hpositive hbeforeClose
              hreaches hnewEntry tailTermination
          exact ⟨by
            simpa [rebased.length_eq] using hbuilt⟩

/-- **Actual recursive serial continuation and termination.**

Every finite raw serial chain compiles to a nested sequence of exact physical
returns.  At each level the remaining frames are rebased from the returned
configuration, and the recursion terminates after exactly the number of
input frames because one head frame is removed at every call.  No tail
function or continuation hypothesis appears in the statement. -/
theorem RawSerialFrameList.terminates
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {frames : List (RawFramedNovelty w N start)}
    (H : RawSerialFrameList w N start frames)
    (hentry : w.link initialEdge = some start.1) :
    Nonempty (RawSerialTermination w N start frames.length) := by
  exact serialFrameList_termination_bounded hN frames.length
    start initialEdge frames (Nat.le_refl _) H hentry

end GeneralN
