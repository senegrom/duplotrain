import SelectedTripleSharpClosure
import MellitGlobalIncompatibleClosure

/-!
# Eliminate the direct-lobe branch of the sharp six-event residue

`RawBABAChargeReplayClosure.earlyPureCrossing` used to be a genuine leaf of
the selected `ABCABC` case. The later direct-lobe saturation theorem makes
that leaf empty: its stored `EarlyDirectLobePureCrossingResidue` is precisely
the support contact ruled out by
`RawOverlappingFiveWindowReduction.early_direct_lobe_pure_crossing_false`.

This file threads that contradiction back through the exhaustive raw shape
decomposition. It does not call a selected close "paid", and it does not
claim that any remaining constructor contradicts vector novelty. In
particular, `GeneralN.StateLaw` remains open.
-/

namespace GeneralN

/-- The early pure-crossing package is empty, with no extra dynamical or
counting hypothesis. Its own fields contain the direct lobe, the opposite
reflector, the empty reusable support, and the forbidden support contact. -/
theorem MellitEarlyPureCrossingResidue.impossible
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {C : RawOverlappingFiveWindowReduction w N start}
    (E : MellitEarlyPureCrossingResidue C) : False := by
  exact C.early_direct_lobe_pure_crossing_false
    E.direct E.opposite E.runway_empty E.candy_empty E.pure

/-- The exact `RawBABAChargeReplayClosure` case split after deleting its
now-empty early-pure-crossing constructor. Every surviving constructor
retains all of its original proof data. -/
inductive RawBABAChargeReplayClosureNoEarly
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    (B : RawBABAInterlacement
      w N start prior second reroute third) : Prop
  | cycle (h : MellitReachedSimpleCycle w start)
  | latePair (h : Nonempty (MellitLatePairResidue C))
  | interiorLobe (k : Nat) (h : RawReachedDirectLobeAt w start k)
  | firstWriterCharge (k : Nat)
      (hsecond : second < k) (hreroute : k < reroute)
      (hfirst : RawFirstWriterAt w N start k)
  | quietFirstWriterCharges
      (hquiet : RamanQuietForeignResidue B)
      (hfirst : forall k, second < k -> k < reroute ->
        RawProductiveAt w N start k -> RawFirstWriterAt w N start k)
  | quietReplay
      (hquiet : RamanQuietForeignResidue B)
      (hreplay : Nonempty
        (RawQuietFrameReplay w N start second reroute))

/-- Exhaust the old closure and discharge its early-pure constructor by the
literal physical contradiction above. -/
theorem RawBABAChargeReplayClosure.without_early
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {prior second reroute third : Nat}
    {C : RawOverlappingFiveWindowReduction w N start}
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (H : RawBABAChargeReplayClosure C B) :
    RawBABAChargeReplayClosureNoEarly C B := by
  cases H with
  | cycle hcycle =>
      exact .cycle hcycle
  | latePair hlate =>
      exact .latePair hlate
  | earlyPureCrossing hearly =>
      exact Nonempty.elim hearly (fun E => E.impossible.elim)
  | interiorLobe k hlobe =>
      exact .interiorLobe k hlobe
  | firstWriterCharge k hsecond hreroute hfirst =>
      exact .firstWriterCharge k hsecond hreroute hfirst
  | quietFirstWriterCharges hquiet hfirst =>
      exact .quietFirstWriterCharges hquiet hfirst
  | quietReplay hquiet hreplay =>
      exact .quietReplay hquiet hreplay

/-- The selected-triple closure with the impossible early-pure BABA leaf
removed. No vector-payment conclusion is attached to the surviving leaves. -/
inductive SelectedTripleSharpClosureNoEarly
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) : Prop
  | abcabc
      (S : SelectedFiveFrameABCABC T.tripleCase)
      (prior second reroute third : Nat)
      (B : RawBABAInterlacement
        w N start prior second reroute third)
      (minimal : RawBABAOverlapMinimal B)
      (closed : RawBABAChargeReplayClosureNoEarly C B)
  | strictNest
      (S : SelectedFiveFrameStrictNest T.tripleCase)

/-- Re-run the exhaustive selected-triple closure and erase exactly the one
constructor now known to be contradictory. -/
theorem RawSelectedEndpointTripleResidue.sharp_closure_no_early
    {w : Wiring} {N : Nat}
    (hN : forall a b, w.link a = some b ->
      And (a < 3 * N) (b < 3 * N))
    {start : Prod Nat Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) :
    SelectedTripleSharpClosureNoEarly C T := by
  cases T.sharp_closure hN C with
  | abcabc S prior second reroute third B minimal closed =>
      exact .abcabc S prior second reroute third B minimal
        closed.without_early
  | strictNest S =>
      exact .strictNest S

/-- The exhaustive sharp shape after eliminating the direct-lobe
pure-crossing leaf. -/
inductive RawSharpShapeNoEarly
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop
  | serialSerial (descent : RawSerialSerialNestedDescent R)
  | selectedTriple
      (T : RawSelectedEndpointTripleResidue w N start)
      (closed : SelectedTripleSharpClosureNoEarly R T)

/-- The original literal no-four-cover contradiction endpoint, together
with the strengthened exhaustive shape in which early pure crossing has
actually been contradicted. -/
structure RawSharpSixEventNoEarly
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop where
  noTailFourCover : Not (NoveltyCoverOn w N start
    [R.z1 + 1, R.z2 + 1, R.z3 + 1, R.z4 + 1, R.z5 + 1]
    (rawFirstWriterHistory w N start (R.z5 + 1) ++
      [restrictedTonguesAt w N start (R.z0 + 1)]) 4)
  shape : RawSharpShapeNoEarly R

/-- Strengthen any raw sharp residue without adding a residue hypothesis.
The switch bound is the ordinary well-formedness premise already present in
the general state-law problem. -/
theorem RawSharpSixEventResidue.without_early
    {w : Wiring} {N : Nat}
    (hN : forall a b, w.link a = some b ->
      And (a < 3 * N) (b < 3 * N))
    {start : Prod Nat Tongues}
    {R : RawOverlappingFiveWindowReduction w N start}
    (H : RawSharpSixEventResidue R) :
    RawSharpSixEventNoEarly R := by
  refine {
    noTailFourCover := H.noTailFourCover
    shape := ?_
  }
  cases H.shape with
  | serialSerial descent =>
      exact .serialSerial descent
  | selectedTriple T =>
      exact .selectedTriple T (T.sharp_closure_no_early hN R)

/-- Six novel repeated-writer events therefore reduce to the strictly
smaller exhaustive sharp residue, with the direct-lobe pure-crossing branch
absent rather than merely renamed. -/
theorem six_repeated_novelties_reduce_to_sharp_no_early
    {w : Wiring} {N initialEdge : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (start : Prod Nat Tongues)
    (hentry : w.link initialEdge = some start.1)
    (K : Nat)
    (hsix : 6 <= (rawRepeatedWriterNovelTimes w N start K).length) :
    Exists fun R : RawOverlappingFiveWindowReduction w N start =>
      RawSharpSixEventNoEarly R := by
  cases six_repeated_novelties_reduce_to_sharp_residue
      hN start hentry K hsix with
  | intro R H =>
      exact Exists.intro R (H.without_early hN)

end GeneralN
