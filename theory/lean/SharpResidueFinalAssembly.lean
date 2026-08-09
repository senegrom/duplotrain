import SelectedTripleSharpClosure
import MellitABCABCRecursionBase
import SerialSerialPlacementClosure
import MellitGlobalNoveltyBound
import MellitRamanStrictDescentAssembly
import MellitRamanTopLevelRecursion

/-!
# Honest top-level assembly of the sharp six-event residue

This module consumes the current construction-level closure without turning
an interior first-writer/replay into a payment of its selected close.

The result is deliberately an exact open-case theorem, not
`IncomingSharpSixEventResidueImpossible`.  It removes the fully quiet
`ABCABC` branch by the literal four-cover, retains the refined Raman strict
descent, preserves the canonical serial caller escape, and records explicitly
why `SelectedFramePaidClosure` alone leaves the selected close unpaid.
-/

namespace GeneralN

/-! ## Preserve the canonical serial caller extraction -/

/-- The complete physical output of the canonical tail-serial caller
extraction, including the sharp placement of the escape's previous write. -/
structure RawTailSerialCallerEscape
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop where
  g : Nat
  oldEntry : Nat
  q : Nat
  edge : Nat
  repeatTime : Nat
  returnTime : Nat
  escape : Nat
  base : Tongues
  mouthState : Tongues
  u : Tongues
  settled : Tongues
  caller : List Passage
  start_step : stepN w R.a1 start = some (g, base)
  caller_trace :
    PhysicalTrace w (g, base) caller (oldEntry, mouthState)
  caller_grooved : PassagesGrooved settled caller
  incoming_link : w.link edge = some g
  repeat_step : stepN w repeatTime start = some (q, u)
  return_time : returnTime = repeatTime + caller.length + 1
  return_step : stepN w returnTime start = some (edge, settled)
  return_le_escape : returnTime ≤ escape
  escape_le_first_close : escape ≤ R.z1
  escape_productive : RawProductiveAt w N start escape
  quiet_before_escape :
    ∀ t, returnTime ≤ t → t < escape →
      ¬ RawProductiveAt w N start t
  sharp_placement :
    restrictedTonguesAt w N start (escape + 1) ∈
        rawFirstWriterHistory w N start (R.z5 + 1) ++
          [restrictedTonguesAt w N start (R.z0 + 1)] ∨
      ∃ left,
        RawLastWriterFrame w N start left escape ∧
        escape = R.z1 ∧ left = R.a1 ∧
        ((0 < caller.length ∧ R.a1 ≤ left ∧
            left < R.a1 + caller.length) ∨
          caller = [])

/-- Package the exact serial caller theorem without weakening any timing or
placement field. -/
theorem RawOverlappingFiveWindowReduction.tail_serial_caller_escape_final
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start)
    (hserial : FiveFrameSerialBreak
      R.z1 R.a2 R.a3 R.a4 R.a5) :
    RawTailSerialCallerEscape R := by
  obtain ⟨g, oldEntry, q, edge, repeatTime, returnTime, escape,
      base, mouthState, u, settled, caller,
      hstart, htrace, hgrooved, hlink, hrepeat, hreturnTime,
      hreturn, hreturnEscape, hescape, hproductive, hquiet,
      hplacement⟩ :=
    R.tail_serial_escape_sharp_placement hN hentry hserial
  exact {
    g := g
    oldEntry := oldEntry
    q := q
    edge := edge
    repeatTime := repeatTime
    returnTime := returnTime
    escape := escape
    base := base
    mouthState := mouthState
    u := u
    settled := settled
    caller := caller
    start_step := hstart
    caller_trace := htrace
    caller_grooved := hgrooved
    incoming_link := hlink
    repeat_step := hrepeat
    return_time := hreturnTime
    return_step := hreturn
    return_le_escape := hreturnEscape
    escape_le_first_close := hescape
    escape_productive := hproductive
    quiet_before_escape := hquiet
    sharp_placement := hplacement
  }

/-- Canonical tail shape with all data needed by the next integration step.
The serial constructor contains the literal caller extraction; the selected
constructor contains actual selected-close provenance and paid closure. -/
inductive RawTailSharpOutcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop
  | serial
      (hserial : FiveFrameSerialBreak R.z1 R.a2 R.a3 R.a4 R.a5)
      (caller : RawTailSerialCallerEscape R)
  | selectedTriple
      (T : RawSelectedEndpointTripleResidue w N start)
      (selectedCloses : T.ClosesInSelectedWindow R)
      (closed : SelectedTripleSharpClosurePaid R T)

theorem RawOverlappingFiveWindowReduction.tail_sharp_outcome_final
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start) :
    RawTailSharpOutcome R := by
  rcases R.tail_shape with hserial | htriple
  · exact .serial hserial
      (R.tail_serial_caller_escape_final hN hentry hserial)
  · let T := R.tailSelectedEndpointTriple htriple
    have hcloses : T.ClosesInSelectedWindow R :=
      R.tailSelectedEndpointTriple_closes htriple
    exact .selectedTriple T hcloses
      (T.sharp_closure_paid hN R hcloses)

/-! ## The literal quiet-ABCABC consequence -/

/-- A productive event occurs in one of the five consecutive open/close gaps
of a selected `ABCABC` triple. -/
def SelectedABCABCHasProductiveGap
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameABCABC T) : Prop :=
  ∃ k, RawProductiveAt w N start k ∧
    ((T.frames.openingAt S.i0 < k ∧
        k < T.frames.openingAt S.i1) ∨
      (T.frames.openingAt S.i1 < k ∧
        k < T.frames.openingAt S.i2) ∨
      (T.frames.openingAt S.i2 < k ∧
        k < T.frames.closingAt S.i0) ∨
      (T.frames.closingAt S.i0 < k ∧
        k < T.frames.closingAt S.i1) ∨
      (T.frames.closingAt S.i1 < k ∧
        k < T.frames.closingAt S.i2))

/-- The fully quiet alternative is the literal forbidden four-cover, hence
every selected `ABCABC` survivor has a productive event in one of its five
ordered gaps. -/
theorem SelectedFiveFrameABCABC.has_productive_gap_final
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {C : RawOverlappingFiveWindowReduction w N start}
    (S : SelectedFiveFrameABCABC T)
    (hselected : ∀ i, RawSixSelectedTime C
      (T.frames.closingAt i)) :
    SelectedABCABCHasProductiveGap S := by
  classical
  have hnovel : RawNovelAt w N start
      (T.frames.closingAt S.i2) :=
    (hselected S.i2).rawRepeatedWriterNovelAt.2.2
  by_contra hnone
  have hquiet01 : ∀ k,
      T.frames.openingAt S.i0 < k →
      k < T.frames.openingAt S.i1 →
      ¬ RawProductiveAt w N start k := by
    intro k h0 h1 hprod
    exact hnone ⟨k, hprod, Or.inl ⟨h0, h1⟩⟩
  have hquiet12 : ∀ k,
      T.frames.openingAt S.i1 < k →
      k < T.frames.openingAt S.i2 →
      ¬ RawProductiveAt w N start k := by
    intro k h1 h2 hprod
    exact hnone ⟨k, hprod, Or.inr (Or.inl ⟨h1, h2⟩)⟩
  have hquiet20 : ∀ k,
      T.frames.openingAt S.i2 < k →
      k < T.frames.closingAt S.i0 →
      ¬ RawProductiveAt w N start k := by
    intro k h2 h0 hprod
    exact hnone ⟨k, hprod,
      Or.inr (Or.inr (Or.inl ⟨h2, h0⟩))⟩
  have hquiet03 : ∀ k,
      T.frames.closingAt S.i0 < k →
      k < T.frames.closingAt S.i1 →
      ¬ RawProductiveAt w N start k := by
    intro k h0 h1 hprod
    exact hnone ⟨k, hprod,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨h0, h1⟩)))⟩
  have hquiet34 : ∀ k,
      T.frames.closingAt S.i1 < k →
      k < T.frames.closingAt S.i2 →
      ¬ RawProductiveAt w N start k := by
    intro k h1 h2 hprod
    exact hnone ⟨k, hprod,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))⟩
  exact S.quiet_false hN hnovel
    hquiet01 hquiet12 hquiet20 hquiet03 hquiet34

/-! ## Do not misread an interior paid closure -/

/-- Exact status of a selected frame after the interior descent is paid.
Either the close is event zero, or it is a tail close whose post-vector is
provably absent from the history used by `noTailFourCover`. -/
inductive SelectedFramePaidSharpStatus
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (close : Nat) (paid : SelectedFramePaidClosure C close) : Prop
  | eventZero (hzero : close = C.z0)
  | unpaidTail
      (htail : RawSixTailSelectedTime C close)
      (notPaid : ¬
        restrictedTonguesAt w N start (close + 1) ∈
          rawFirstWriterHistory w N start (C.z5 + 1) ++
            [restrictedTonguesAt w N start (C.z0 + 1)])

theorem SelectedFramePaidClosure.sharp_status
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    {close : Nat}
    (paid : SelectedFramePaidClosure C close)
    (hselected : RawSixSelectedTime C close) :
    SelectedFramePaidSharpStatus C close paid := by
  rcases hselected with hzero | htail
  · exact .eventZero hzero
  · exact .unpaidTail htail
      (SelectedFramePaidClosure.selected_tail_close_still_unpaid
        hN paid htail)

/-! ## The exact remaining open cases -/

/-- Information-preserving strict reduction of the serial/serial leaf. -/
def RawSerialStrictSelectedClose
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop :=
  ∃ (returned : Nat × Tongues) (shift globalClose : Nat)
      (localFrame : RawFramedNovelty w N returned),
    stepN w shift start = some returned ∧
    0 < shift ∧
    (globalClose = R.z1 ∨ globalClose = R.z2 ∨
      globalClose = R.z3 ∨ globalClose = R.z4 ∨
      globalClose = R.z5) ∧
    localFrame.closeTime = globalClose - shift ∧
    localFrame.closeTime < globalClose

/-- The sharpened selected `ABCABC` residue.  It simultaneously retains the
latest charge/replay classification, the stronger strict-descent
classification, and the productive-gap witness obtained after the literal
quiet four-cover is ruled out. -/
structure SelectedABCABCSharpResidual
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) : Prop where
  S : SelectedFiveFrameABCABC T.tripleCase
  prior : Nat
  second : Nat
  reroute : Nat
  third : Nat
  B : RawBABAInterlacement w N start prior second reroute third
  minimal : RawBABAOverlapMinimal B
  chargeReplay : RawBABAChargeReplayClosure C B
  strictDescent : MellitRamanStrictDescentOutcome C B
  productiveGap : SelectedABCABCHasProductiveGap S

/-- The strict-nest residue is retained with an explicit proof that its
interior paid closure is not, by itself, a payment of a tail selected close. -/
structure SelectedStrictNestSharpResidual
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) : Prop where
  S : SelectedFiveFrameStrictNest T.tripleCase
  paid : SelectedFramePaidClosure C
    (T.tripleCase.frames.closingAt S.i0)
  status : SelectedFramePaidSharpStatus C
    (T.tripleCase.frames.closingAt S.i0) paid

/-- Strongest unconditional shape theorem presently derivable at the sharp
six-event boundary.  These constructors are genuine open proof obligations,
not aliases for a completed four-cover. -/
inductive RawSharpFinalOpenCase
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop
  | serialSerial
      (descent : RawSerialSerialNestedDescent R)
      (strict : RawSerialStrictSelectedClose R)
  | selectedABCABC
      (T : RawSelectedEndpointTripleResidue w N start)
      (selectedCloses : T.ClosesInSelectedWindow R)
      (residual : SelectedABCABCSharpResidual R T)
  | selectedStrictNest
      (T : RawSelectedEndpointTripleResidue w N start)
      (selectedCloses : T.ClosesInSelectedWindow R)
      (residual : SelectedStrictNestSharpResidual R T)

private theorem final_open_case_of_closed_shape
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {R : RawOverlappingFiveWindowReduction w N start}
    (closedShape : RawSharpShapeClosure R) :
    RawSharpFinalOpenCase R := by
  rcases closedShape with descent | ⟨T, hcloses, closed⟩
  · exact .serialSerial descent descent.strict_selected_close
  · rcases closed with
      ⟨S, prior, second, reroute, third, B, hmin, hclosed⟩ |
      ⟨S, paid⟩
    · exact .selectedABCABC T hcloses {
        S := S
        prior := prior
        second := second
        reroute := reroute
        third := third
        B := B
        minimal := hmin
        chargeReplay := hclosed
        strictDescent := hmin.mellit_raman_strict_descent_outcome hN R
        productiveGap := S.has_productive_gap_final hN hcloses
      }
    · exact .selectedStrictNest T hcloses {
        S := S
        paid := paid
        status := paid.sharp_status hN (hcloses S.i0)
      }

/-- The exact compiled checkpoint.  It pattern-matches the residue's own raw
shape.  In the selected constructor, where the old package lacks close-time
provenance, it uses the independently constructed canonical closed shape.
The no-four-cover field is preserved literally.

This theorem does **not** prove `IncomingSharpSixEventResidueImpossible`:
each constructor of `RawSharpFinalOpenCase` still requires a physical
selected-close equality or history-membership theorem. -/
structure RawSharpResidueFinalAssembly
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop where
  noTailFourCover : ¬ NoveltyCoverOn w N start
    [R.z1 + 1, R.z2 + 1, R.z3 + 1, R.z4 + 1, R.z5 + 1]
    (rawFirstWriterHistory w N start (R.z5 + 1) ++
      [restrictedTonguesAt w N start (R.z0 + 1)]) 4
  tail : RawTailSharpOutcome R
  openCase : RawSharpFinalOpenCase R

theorem RawSharpSixEventResidue.final_assembly
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    {R : RawOverlappingFiveWindowReduction w N start}
    (H : RawSharpSixEventResidue R) :
    RawSharpResidueFinalAssembly R := by
  refine {
    noTailFourCover := H.noTailFourCover
    tail := R.tail_sharp_outcome_final hN hentry
    openCase := ?_
  }
  rcases H.shape with descent | ⟨_T⟩
  · exact .serialSerial descent descent.strict_selected_close
  · exact final_open_case_of_closed_shape hN
      (R.sharp_shape_closure hN hentry)

end GeneralN
