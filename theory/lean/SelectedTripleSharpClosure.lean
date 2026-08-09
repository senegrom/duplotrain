import SharpSixEventAssembly
import MellitRamanBABAAssembly
import MinimalBABAQuietCharge
import RamanOuterGapStrictDescent

/-!
# Sharp closure of one selected endpoint triple

This file starts at the literal `RawSelectedEndpointTripleResidue` produced
by `SharpSixEventAssembly`.  It does not use the open certified-echo compiler.

A selected raw `ABCABC` triple already contains a physical BABA: its first
two selected last-writer frames have endpoint order `A B A B`, and the first
frame forbids the second opening from carrying the same writer.  We descend
to an overlap-minimal raw BABA and feed that object to the accepted
Mellit--Raman lobe/pair/crossing closure.  The remaining bare quiet-foreign
branch is sharpened with `quiet_residue_charge_or_replay`.

Consequently the selected-triple boundary has one, and only one, unprocessed
constructor in this file: a concrete selected strict nest.  This is an honest
reduction, not a proof of the global state law.
-/

namespace GeneralN

/-! ## Selecting the physical last-writer frame at a `Fin 5` index -/

/-- The outer last-writer frame at one selected index.  Keeping this accessor
in the raw language avoids introducing the open certified-echo compiler. -/
theorem FiveRawClosingFrames.outerAt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4)
    (i : Fin 5) :
    RawLastWriterFrame w N start (F.openingAt i) (F.closingAt i) := by
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      exact F.frame₀.outer
  | succ i =>
      cases i with
      | zero =>
          exact F.frame₁.outer
      | succ i =>
          cases i with
          | zero =>
              exact F.frame₂.outer
          | succ i =>
              cases i with
              | zero =>
                  exact F.frame₃.outer
              | succ i =>
                  cases i with
                  | zero =>
                      exact F.frame₄.outer
                  | succ i =>
                      omega

/-! ## The direct raw `ABCABC` to BABA bridge -/

/-- The first two frames of a selected `ABCABC` triple form a literal raw
BABA.  Writer inequality is physical: if the closing writers agreed, the
second opening would be a forbidden same-writer productive event inside the
first last-writer frame. -/
theorem SelectedFiveFrameABCABC.first_pair_rawBABA
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameABCABC T) :
    RawBABAInterlacement w N start
      (T.frames.openingAt S.i0) (T.frames.openingAt S.i1)
      (T.frames.closingAt S.i0) (T.frames.closingAt S.i1) := by
  let leftFrame := T.frames.outerAt S.i0
  let rightFrame := T.frames.outerAt S.i1
  have hopen01 : T.frames.openingAt S.i0 <
      T.frames.openingAt S.i1 := S.shape.1
  have hopen12 : T.frames.openingAt S.i1 <
      T.frames.openingAt S.i2 := S.shape.2.1
  have hopen2Close0 : T.frames.openingAt S.i2 <
      T.frames.closingAt S.i0 := S.shape.2.2.1
  have hopen1Close0 : T.frames.openingAt S.i1 <
      T.frames.closingAt S.i0 :=
    Nat.lt_trans hopen12 hopen2Close0
  have hclose01 : T.frames.closingAt S.i0 <
      T.frames.closingAt S.i1 := S.shape.2.2.2.1
  have hopenDifferent :
      rawWriterAt w start (T.frames.openingAt S.i1) ≠
        rawWriterAt w start (T.frames.closingAt S.i0) :=
    leftFrame.no_same_writer_between
      (T.frames.openingAt S.i1) hopen01 hopen1Close0
      rightFrame.open_productive
  have hcloseDifferent :
      rawWriterAt w start (T.frames.closingAt S.i0) ≠
        rawWriterAt w start (T.frames.closingAt S.i1) := by
    intro heq
    apply hopenDifferent
    exact rightFrame.same_writer.trans heq.symm
  exact {
    prior_lt_second := hopen01
    second_lt_reroute := hopen1Close0
    reroute_lt_third := hclose01
    leftFrame := leftFrame
    rightFrame := rightFrame
    different_writers := hcloseDifferent
  }

/-! ## Eliminate the bare quiet BABA constructor -/

/-- Accepted closure outcomes for an overlap-minimal BABA after replacing
the unqualified quiet-foreign residue by its exact charge/replay theorem. -/
inductive RawBABAChargeReplayClosure
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
  | quietFirstWriterCharges
      (hquiet : RamanQuietForeignResidue B)
      (hfirst : ∀ k, second < k → k < reroute →
        RawProductiveAt w N start k → RawFirstWriterAt w N start k)
  | quietReplay
      (hquiet : RamanQuietForeignResidue B)
      (hreplay : Nonempty
        (RawQuietFrameReplay w N start second reroute))

/-- The Mellit--Raman physical outcome has no bare quiet constructor: quiet
foreign traffic is either entirely paid by first writers in the overlap, or
contains a least two-vector replay frame. -/
theorem RawBABAOverlapMinimal.charge_replay_closure
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (C : RawOverlappingFiveWindowReduction w N start)
    {B : RawBABAInterlacement
      w N start prior second reroute third}
    (hmin : RawBABAOverlapMinimal B) :
    RawBABAChargeReplayClosure C B := by
  rcases hmin.mellit_raman_outcome hN C with
    hcycle | hlate | hearly | ⟨k, hlobe⟩ |
      ⟨k, hsecond, hreroute, hfirst⟩ | hquiet
  · exact .cycle hcycle
  · exact .latePair hlate
  · exact .earlyPureCrossing hearly
  · exact .interiorLobe k hlobe
  · exact .firstWriterCharge k hsecond hreroute hfirst
  · rcases hmin.quiet_residue_charge_or_replay hN hquiet with
      hfirst | hreplay
    · exact .quietFirstWriterCharges hquiet hfirst
    · exact .quietReplay hquiet hreplay

/-! ## The selected-triple boundary -/

/-- The sharp selected-triple outcome.  `abcabc` is not a residual label: it
carries an actual overlap-minimal raw BABA and its accepted physical
charge/replay closure.  The sole unprocessed constructor is `strictNest`. -/
inductive SelectedTripleSharpClosure
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) : Prop
  | abcabc
      (S : SelectedFiveFrameABCABC T.tripleCase)
      (prior second reroute third : Nat)
      (B : RawBABAInterlacement
        w N start prior second reroute third)
      (minimal : RawBABAOverlapMinimal B)
      (closed : RawBABAChargeReplayClosure C B)
  | strictNest
      (S : SelectedFiveFrameStrictNest T.tripleCase)

/-- **Unconditional selected-triple sharp closure.**  A selected raw
`ABCABC` is compiled directly to a physical BABA, minimized by overlap, and
sent through the accepted Mellit--Raman plus quiet charge/replay closure.
Exactly one constructor remains: a concrete selected strict nest. -/
theorem RawSelectedEndpointTripleResidue.sharp_closure
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) :
    SelectedTripleSharpClosure C T := by
  rcases T.selected with habc | hstrict
  · obtain ⟨S⟩ := habc
    let B0 := S.first_pair_rawBABA
    obtain ⟨prior, second, reroute, third, B, hmin⟩ :=
      B0.exists_overlap_minimal
    exact .abcabc S prior second reroute third B hmin
      (hmin.charge_replay_closure hN C)
  · obtain ⟨S⟩ := hstrict
    exact .strictNest S

/-! ## Sharpen the strict nest when its erased event provenance is restored -/

/-- The transparent provenance relation which the current
`RawSelectedEndpointTripleResidue` structure does not store: each of its five
closing times is one of the canonical six selected novelties. -/
def RawSelectedEndpointTripleResidue.ClosesInSelectedWindow
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) : Prop :=
  ∀ i, RawSixSelectedTime C (T.tripleCase.frames.closingAt i)

/-- The one genuinely recursive strict-nest residue: a selected novelty lies
strictly inside the innermost selected frame.  Its selected close time is
strictly smaller than that frame's selected close time. -/
structure SelectedStrictNestEarlierSelected
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameStrictNest T) : Type where
  k : Nat
  afterOpening : T.frames.openingAt S.i0 < k
  beforeClosing : k < T.frames.closingAt S.i0
  selected : RawSixSelectedTime C k

/-- A novel close of any last-writer frame has a productive event strictly
inside that frame.  A quiet interior would replay the opening vector and
contradict novelty. -/
theorem RawLastWriterFrame.novel_close_has_interior_productive
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues} {opening closing : Nat}
    (F : RawLastWriterFrame w N start opening closing)
    (hnovel : RawNovelAt w N start closing) :
    ∃ k, opening < k ∧ k < closing ∧
      RawProductiveAt w N start k := by
  by_cases hex : ∃ k, opening < k ∧ k < closing ∧
      RawProductiveAt w N start k
  · exact hex
  · exfalso
    apply F.quiet_close_not_novel hN
      (fun k hopen hclose hprod => by
        apply hex
        exact ⟨k, hopen, hclose, hprod⟩)
    exact hnovel

/-- The innermost close of a selected strict nest cannot have a completely
quiet interior.  Otherwise the quiet-frame replay theorem contradicts the
novelty of that selected close. -/
theorem SelectedFiveFrameStrictNest.innermost_has_productive
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameStrictNest T)
    (hnovel : RawNovelAt w N start (T.frames.closingAt S.i0)) :
    ∃ k,
      T.frames.openingAt S.i0 < k ∧
      k < T.frames.closingAt S.i0 ∧
      RawProductiveAt w N start k := by
  exact (T.frames.outerAt S.i0).novel_close_has_interior_productive
    hN hnovel

/-- Paid outcomes for the strict nest, plus its single smallest recursive
constructor.  A productive event strictly inside the innermost selected
frame is either a first-writer charge, an earlier-vector replay, or an
earlier selected novelty. -/
inductive SelectedStrictNestSharpClosure
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameStrictNest T) : Prop
  | firstWriterCharge (k : Nat)
      (hopen : T.frames.openingAt S.i0 < k)
      (hclose : k < T.frames.closingAt S.i0)
      (hfirst : RawFirstWriterAt w N start k)
  | earlierReplay (k : Nat)
      (hopen : T.frames.openingAt S.i0 < k)
      (hclose : k < T.frames.closingAt S.i0)
      (hreplay : RamanEarlierVectorReplayAt w N start k)
  | earlierSelected
      (residue : Nonempty (SelectedStrictNestEarlierSelected C S))

/-- Restore the selected-event provenance and close two of the three strict
nest branches immediately.  The `afterSelectedTail` case is impossible
because the productive witness occurs before a selected close. -/
theorem SelectedFiveFrameStrictNest.sharp_closure
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameStrictNest T)
    (hselected : ∀ i,
      RawSixSelectedTime C (T.frames.closingAt i)) :
    SelectedStrictNestSharpClosure C S := by
  have hcloseSelected := hselected S.i0
  have hcloseEvent := hcloseSelected.rawRepeatedWriterNovelAt
  obtain ⟨k, hopen, hclose, hprod⟩ :=
    S.innermost_has_productive hN hcloseEvent.2.2
  rcases rawProductiveAt_outer_disposition C hprod with
    hlate | hfirst | hreplay | hkSelected
  · have hcloseLe : T.frames.closingAt S.i0 ≤ C.z5 :=
      hcloseSelected.le_z5
    omega
  · exact .firstWriterCharge k hopen hclose hfirst
  · exact .earlierReplay k hopen hclose hreplay
  · exact .earlierSelected ⟨{
      k := k
      afterOpening := hopen
      beforeClosing := hclose
      selected := hkSelected
    }⟩

/-- The fully paid endpoint of well-founded selected-close descent. -/
inductive SelectedFramePaidClosure
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (close : Nat) : Prop
  | firstWriterCharge (k : Nat)
      (hearlier : k < close)
      (hfirst : RawFirstWriterAt w N start k)
  | earlierReplay (k : Nat)
      (hearlier : k < close)
      (hreplay : RamanEarlierVectorReplayAt w N start k)

/-- **Well-founded selected-close assembly.**  Starting from any selected
novel close and any of its raw last-writer frames, repeated descent through
an interior selected novelty terminates at a first-writer charge or an
earlier-vector replay.  The measure is the literal raw close time. -/
theorem selected_frame_paid_closure
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start) :
    ∀ close,
      RawSixSelectedTime C close →
      ∀ opening,
        RawLastWriterFrame w N start opening close →
        SelectedFramePaidClosure C close := by
  intro close
  apply Nat.strongRecOn (motive := fun close =>
    RawSixSelectedTime C close →
    ∀ opening,
      RawLastWriterFrame w N start opening close →
      SelectedFramePaidClosure C close) close
  intro close ih hselected opening F
  have hcloseEvent := hselected.rawRepeatedWriterNovelAt
  obtain ⟨k, _hopen, hclose, hprod⟩ :=
    F.novel_close_has_interior_productive hN hcloseEvent.2.2
  rcases rawProductiveAt_outer_disposition C hprod with
    hlate | hfirst | hreplay | hkSelected
  · have hcloseLe : close ≤ C.z5 := hselected.le_z5
    omega
  · exact .firstWriterCharge k hclose hfirst
  · exact .earlierReplay k hclose hreplay
  · have Hk := hkSelected.rawRepeatedWriterNovelAt
    obtain ⟨left, Fk⟩ := Hk.last_writer_frame
    rcases ih k hclose hkSelected left Fk with
      ⟨j, hj, hfirst⟩ | ⟨j, hj, hreplay⟩
    · exact .firstWriterCharge j (Nat.lt_trans hj hclose) hfirst
    · exact .earlierReplay j (Nat.lt_trans hj hclose) hreplay

/-- The selected strict nest is therefore fully paid: the earlier-selected
constructor of `SelectedStrictNestSharpClosure` is consumed by strong
induction and does not survive. -/
theorem SelectedFiveFrameStrictNest.paid_closure
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameStrictNest T)
    (hselected : ∀ i,
      RawSixSelectedTime C (T.frames.closingAt i)) :
    SelectedFramePaidClosure C (T.frames.closingAt S.i0) :=
  selected_frame_paid_closure hN C
    (T.frames.closingAt S.i0) (hselected S.i0)
    (T.frames.openingAt S.i0) (T.frames.outerAt S.i0)

/-- Refined selected-triple closure with the erased close-time provenance
supplied explicitly.  The only non-paid/non-physical leaf is now
`SelectedStrictNestEarlierSelected`, whose close time strictly decreases. -/
inductive SelectedTripleSharpClosureWithWindow
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) : Prop
  | abcabc
      (S : SelectedFiveFrameABCABC T.tripleCase)
      (prior second reroute third : Nat)
      (B : RawBABAInterlacement
        w N start prior second reroute third)
      (minimal : RawBABAOverlapMinimal B)
      (closed : RawBABAChargeReplayClosure C B)
  | strictNest
      (S : SelectedFiveFrameStrictNest T.tripleCase)
      (closed : SelectedStrictNestSharpClosure C S)

/-- Stronger selected-triple closure after consuming strict selected-close
descent by well-founded induction. -/
inductive SelectedTripleSharpClosurePaid
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start) : Prop
  | abcabc
      (S : SelectedFiveFrameABCABC T.tripleCase)
      (prior second reroute third : Nat)
      (B : RawBABAInterlacement
        w N start prior second reroute third)
      (minimal : RawBABAOverlapMinimal B)
      (closed : RawBABAChargeReplayClosure C B)
  | strictNestPaid
      (S : SelectedFiveFrameStrictNest T.tripleCase)
      (paid : SelectedFramePaidClosure C
        (T.tripleCase.frames.closingAt S.i0))

/-- Refined version of `sharp_closure`: with the exact selected-close
relation restored, strict nesting is paid or recurses to one strictly earlier
selected close. -/
theorem RawSelectedEndpointTripleResidue.sharp_closure_with_window
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start)
    (hselected : T.ClosesInSelectedWindow C) :
    SelectedTripleSharpClosureWithWindow C T := by
  rcases T.selected with habc | hstrict
  · obtain ⟨S⟩ := habc
    let B0 := S.first_pair_rawBABA
    obtain ⟨prior, second, reroute, third, B, hmin⟩ :=
      B0.exists_overlap_minimal
    exact .abcabc S prior second reroute third B hmin
      (hmin.charge_replay_closure hN C)
  · obtain ⟨S⟩ := hstrict
    exact .strictNest S (S.sharp_closure hN C hselected)

/-- Strict nesting leaves no residual once close provenance is available. -/
theorem RawSelectedEndpointTripleResidue.sharp_closure_paid
    {w : Wiring} {N : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    {start : Nat × Tongues}
    (C : RawOverlappingFiveWindowReduction w N start)
    (T : RawSelectedEndpointTripleResidue w N start)
    (hselected : T.ClosesInSelectedWindow C) :
    SelectedTripleSharpClosurePaid C T := by
  rcases T.selected with habc | hstrict
  · obtain ⟨S⟩ := habc
    let B0 := S.first_pair_rawBABA
    obtain ⟨prior, second, reroute, third, B, hmin⟩ :=
      B0.exists_overlap_minimal
    exact .abcabc S prior second reroute third B hmin
      (hmin.charge_replay_closure hN C)
  · obtain ⟨S⟩ := hstrict
    exact .strictNestPaid S (S.paid_closure hN C hselected)

/-! ## Preserve the selected-close provenance at construction time -/

/-- The concrete selected triple coming from the head five-event window. -/
def RawOverlappingFiveWindowReduction.headSelectedEndpointTriple
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (htriple : FiveFrameTripleOutcome
      R.a0 R.z0 R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4) :
    RawSelectedEndpointTripleResidue w N start :=
  let T := R.headTripleCase htriple
  {
    z0 := R.z0
    z1 := R.z1
    z2 := R.z2
    z3 := R.z3
    z4 := R.z4
    tripleCase := T
    selected := T.select_endpoint_triple
  }

/-- The concrete selected triple coming from the tail five-event window. -/
def RawOverlappingFiveWindowReduction.tailSelectedEndpointTriple
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (htriple : FiveFrameTripleOutcome
      R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4 R.a5 R.z5) :
    RawSelectedEndpointTripleResidue w N start :=
  let T := R.tailTripleCase htriple
  {
    z0 := R.z1
    z1 := R.z2
    z2 := R.z3
    z3 := R.z4
    z4 := R.z5
    tripleCase := T
    selected := T.select_endpoint_triple
  }

/-- Every close retained by the head selected triple is definitionally one
of `z0, ..., z4` in the canonical six-event window. -/
theorem RawOverlappingFiveWindowReduction.headSelectedEndpointTriple_closes
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (htriple : FiveFrameTripleOutcome
      R.a0 R.z0 R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4) :
    (R.headSelectedEndpointTriple htriple).ClosesInSelectedWindow R := by
  intro i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      exact Or.inl rfl
  | succ i =>
      cases i with
      | zero =>
          exact Or.inr (Or.inl rfl)
      | succ i =>
          cases i with
          | zero =>
              exact Or.inr (Or.inr (Or.inl rfl))
          | succ i =>
              cases i with
              | zero =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
              | succ i =>
                  cases i with
                  | zero =>
                      exact Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inl rfl))))
                  | succ i =>
                      omega

/-- Every close retained by the tail selected triple is definitionally one
of `z1, ..., z5` in the canonical six-event window. -/
theorem RawOverlappingFiveWindowReduction.tailSelectedEndpointTriple_closes
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start)
    (htriple : FiveFrameTripleOutcome
      R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4 R.a5 R.z5) :
    (R.tailSelectedEndpointTriple htriple).ClosesInSelectedWindow R := by
  intro i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      exact Or.inr (Or.inl rfl)
  | succ i =>
      cases i with
      | zero =>
          exact Or.inr (Or.inr (Or.inl rfl))
      | succ i =>
          cases i with
          | zero =>
              exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          | succ i =>
              cases i with
              | zero =>
                  exact Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl rfl))))
              | succ i =>
                  cases i with
                  | zero =>
                      exact Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr rfl))))
                  | succ i =>
                      omega

/-- Strengthened top-level shape: the serial/serial descent is retained, but
every selected-triple branch now carries its complete sharp closure and the
proof that its close times are the actual canonical selected events. -/
inductive RawSharpShapeClosure
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (R : RawOverlappingFiveWindowReduction w N start) : Prop
  | serialSerial (descent : RawSerialSerialNestedDescent R)
  | selectedTriple
      (T : RawSelectedEndpointTripleResidue w N start)
      (selectedCloses : T.ClosesInSelectedWindow R)
      (closed : SelectedTripleSharpClosurePaid R T)

/-- **Construction-level selected-triple closure.**  Splitting the actual
head/tail shapes preserves close-time provenance automatically.  No caller
must assume the extra relation, and no certified-echo compiler is used. -/
theorem RawOverlappingFiveWindowReduction.sharp_shape_closure
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start) :
    RawSharpShapeClosure R := by
  rcases R.head_shape with hhead | hhead
  · rcases R.tail_shape with htail | htail
    · exact .serialSerial
        (R.serial_serial_nested_descent hN hentry hhead htail)
    · let T := R.tailSelectedEndpointTriple htail
      have hcloses : T.ClosesInSelectedWindow R :=
        R.tailSelectedEndpointTriple_closes htail
      exact .selectedTriple T hcloses
        (T.sharp_closure_paid hN R hcloses)
  · let T := R.headSelectedEndpointTriple hhead
    have hcloses : T.ClosesInSelectedWindow R :=
      R.headSelectedEndpointTriple_closes hhead
    exact .selectedTriple T hcloses
      (T.sharp_closure_paid hN R hcloses)

end GeneralN
