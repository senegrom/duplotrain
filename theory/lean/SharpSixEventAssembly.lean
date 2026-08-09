import SelectedSupportContactClosure
import CrossingCallerSharpTail
import SixEventSharpClosure
import OverlappingSerialWindows
import TripleSelfLinkCycleClosure
import MinimalForeignCrossingClosure
import MellitNoncompatibleSecondRepeat

/-!
# Sharp assembly of the canonical six-event obstruction

This file performs the top-level case split which is justified by the
currently accepted raw theorems. It deliberately does not call the open
`StateLaw` proved.

For two serial windows, `serial_serial_nested_descent` supplies two actual
reached suffixes and a strict decrease of a selected framed novelty. If at
least one window is triple, `select_endpoint_triple` supplies one concrete
selected `ABCABC` or strict-nest triple, retaining all five raw closing
frames. In every branch the literal four-vector tail cover is already
impossible by `no_tail_four_cover`.

The remaining proposition `RawSharpSixEventResidue` is therefore the exact
current assembly boundary. The later reflector, self-link, support-contact,
and foreign-crossing files close refined instances of its selected-triple
branch, but the raw shape theorem does not yet manufacture those additional
objects. They are not assumed here.
-/

namespace GeneralN

/-- The full strict suffix comparison returned when both overlapping
five-event windows are serial. -/
def RawSerialSerialNestedDescent
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop :=
  Exists fun H : RawGlobalSerialContinuation w N start R.z0 =>
    Exists fun T : RawGlobalSerialContinuation w N start R.z1 =>
      Exists fun SH : RawSelectedLaterSerialFrame w N start R.z0 =>
        Exists fun ST : RawSelectedLaterSerialFrame w N start R.z1 =>
          And
            (Or (SH.closeTime = R.z1)
              (Or (SH.closeTime = R.z2)
                (Or (SH.closeTime = R.z3) (SH.closeTime = R.z4))))
            (And
              (Or (ST.closeTime = R.z2)
                (Or (ST.closeTime = R.z3)
                  (Or (ST.closeTime = R.z4) (ST.closeTime = R.z5))))
              (Or
                (And (H.returnTime <= T.returnTime)
                  (And
                    (stepN w (T.returnTime - H.returnTime) H.returned =
                      some T.returned)
                    (Exists fun FH : RawFramedNovelty w N H.returned =>
                      Exists fun FT : RawFramedNovelty w N T.returned =>
                        And (FH.closeTime = ST.closeTime - H.returnTime)
                          (And (FT.closeTime = ST.closeTime - T.returnTime)
                            (And (FH.closeTime < ST.closeTime)
                              (And (FT.closeTime < ST.closeTime)
                                (And (FT.closeTime <= FH.closeTime)
                                  (H.returnTime < T.returnTime ->
                                    FT.closeTime < FH.closeTime))))))))
                (And (T.returnTime <= H.returnTime)
                  (And
                    (stepN w (H.returnTime - T.returnTime) T.returned =
                      some H.returned)
                    (Exists fun FT : RawFramedNovelty w N T.returned =>
                      Exists fun FH : RawFramedNovelty w N H.returned =>
                        And (FT.closeTime = SH.closeTime - T.returnTime)
                          (And (FH.closeTime = SH.closeTime - H.returnTime)
                            (And (FT.closeTime < SH.closeTime)
                              (And (FH.closeTime < SH.closeTime)
                                (And (FH.closeTime <= FT.closeTime)
                                  (T.returnTime < H.returnTime ->
                                    FH.closeTime < FT.closeTime))))))))))

/-- Package one selected endpoint triple without forgetting which five raw
closing frames produced it. -/
structure RawSelectedEndpointTripleResidue
    (w : Wiring) (N : Nat) (start : Prod Nat Tongues) : Type where
  z0 : Nat
  z1 : Nat
  z2 : Nat
  z3 : Nat
  z4 : Nat
  tripleCase : FiveFrameTripleCase w N start z0 z1 z2 z3 z4
  selected :
    Or (Nonempty (SelectedFiveFrameABCABC tripleCase))
      (Nonempty (SelectedFiveFrameStrictNest tripleCase))

/-- Construct the concrete head-window triple case. -/
def RawOverlappingFiveWindowReduction.headTripleCase
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (htriple : FiveFrameTripleOutcome
      R.a0 R.z0 R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4) :
    FiveFrameTripleCase w N start R.z0 R.z1 R.z2 R.z3 R.z4 := {
  frames := FiveRawClosingFrames.mk
    R.a0 R.q0 R.a1 R.q1 R.a2 R.q2 R.a3 R.q3 R.a4 R.q4
    R.frame0 R.frame1 R.frame2 R.frame3 R.frame4
  triple := htriple
}

/-- Construct the concrete tail-window triple case. -/
def RawOverlappingFiveWindowReduction.tailTripleCase
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (htriple : FiveFrameTripleOutcome
      R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4 R.a5 R.z5) :
    FiveFrameTripleCase w N start R.z1 R.z2 R.z3 R.z4 R.z5 := {
  frames := FiveRawClosingFrames.mk
    R.a1 R.q1 R.a2 R.q2 R.a3 R.q3 R.a4 R.q4 R.a5 R.q5
    R.frame1 R.frame2 R.frame3 R.frame4 R.frame5
  triple := htriple
}

/-- After explicitly splitting both overlapping windows, exactly two kinds
of shape residue remain: the proved serial/serial strict descent, or one
selected concrete endpoint triple. -/
inductive RawSharpShapeResidue
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop
  | serialSerial (descent : RawSerialSerialNestedDescent R)
  | selectedTriple
      (triple : RawSelectedEndpointTripleResidue w N start)

/-- The exact current top-level six-event residue. Besides its shape data,
it records that the already-closed four-vector accounting alternative is
impossible. -/
structure RawSharpSixEventResidue
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop where
  shape : RawSharpShapeResidue R
  noTailFourCover : Not (NoveltyCoverOn w N start
    [R.z1 + 1, R.z2 + 1, R.z3 + 1, R.z4 + 1, R.z5 + 1]
    (rawFirstWriterHistory w N start (R.z5 + 1) ++
      [restrictedTonguesAt w N start (R.z0 + 1)]) 4)

/-- Explicit four-way `head_shape`/`tail_shape` assembly. -/
theorem RawOverlappingFiveWindowReduction.sharp_shape_residue
    {w : Wiring} {N initialEdge : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start) :
    RawSharpShapeResidue R := by
  rcases R.head_shape with hhead | hhead
  . rcases R.tail_shape with htail | htail
    . exact RawSharpShapeResidue.serialSerial
        (R.serial_serial_nested_descent hN hentry hhead htail)
    . let T := R.tailTripleCase htail
      exact RawSharpShapeResidue.selectedTriple {
        z0 := R.z1
        z1 := R.z2
        z2 := R.z3
        z3 := R.z4
        z4 := R.z5
        tripleCase := T
        selected := T.select_endpoint_triple
      }
  . rcases R.tail_shape with htail | htail
    . let T := R.headTripleCase hhead
      exact RawSharpShapeResidue.selectedTriple {
        z0 := R.z0
        z1 := R.z1
        z2 := R.z2
        z3 := R.z3
        z4 := R.z4
        tripleCase := T
        selected := T.select_endpoint_triple
      }
    . let T := R.headTripleCase hhead
      exact RawSharpShapeResidue.selectedTriple {
        z0 := R.z0
        z1 := R.z1
        z2 := R.z2
        z3 := R.z3
        z4 := R.z4
        tripleCase := T
        selected := T.select_endpoint_triple
      }

/-- Assemble one canonical raw reduction into the exact sharp residue. -/
theorem RawOverlappingFiveWindowReduction.toSharpSixEventResidue
    {w : Wiring} {N initialEdge : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start) :
    RawSharpSixEventResidue R := by
  refine {
    shape := R.sharp_shape_residue hN hentry
    noTailFourCover := ?_
  }
  simpa [RawOverlappingFiveWindowReduction.toSixEventReduction] using
    R.toSixEventReduction.no_tail_four_cover hN

/-- Top-level reduction from six globally novel repeated-writer events to
the one explicit current residue. -/
theorem six_repeated_novelties_reduce_to_sharp_residue
    {w : Wiring} {N initialEdge : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (start : Prod Nat Tongues)
    (hentry : w.link initialEdge = some start.1)
    (K : Nat)
    (hsix : 6 <= (rawRepeatedWriterNovelTimes w N start K).length) :
    Exists fun R : RawOverlappingFiveWindowReduction w N start =>
      RawSharpSixEventResidue R := by
  exact Nonempty.elim
    (six_repeated_novelties_reduce_to_overlapping_windows hN start K hsix)
    (fun R => Exists.intro R (R.toSharpSixEventResidue hN hentry))

/-- A single narrow closure proposition for the remaining assembly boundary,
stated directly over raw tracks and switches with a known incoming edge. -/
def IncomingSharpSixEventResidueImpossible : Prop :=
  forall (w : Wiring) (N initialEdge : Nat),
    (forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N)) ->
    forall start : Prod Nat Tongues,
      w.link initialEdge = some start.1 ->
      forall R : RawOverlappingFiveWindowReduction w N start,
        Not (RawSharpSixEventResidue R)

/-- Closing the one displayed residue rules out six repeated novelties for
every start with a known incoming physical edge. -/
theorem six_repeated_novelties_false_of_sharp_residue_impossible
    {w : Wiring} {N initialEdge : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (start : Prod Nat Tongues)
    (hentry : w.link initialEdge = some start.1)
    (K : Nat)
    (hsix : 6 <= (rawRepeatedWriterNovelTimes w N start K).length)
    (hclose : forall R : RawOverlappingFiveWindowReduction w N start,
      Not (RawSharpSixEventResidue R)) : False := by
  have H := six_repeated_novelties_reduce_to_sharp_residue
    hN start hentry K hsix
  exact H.elim (fun R hR => hclose R hR)

end GeneralN
