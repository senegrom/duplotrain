import TripleSelfLinkFinalAssembly

/-!
# Discharging the opposite-reflector self-link branch

The selected self-link cycle yields a literal four-vector cover of all five
tail closes when its first revisit manufactures the opposite reflector. This
file places that cover in the canonical raw six-event tail and applies
RawSixEventReduction.no_tail_four_cover.

The endpoint theorem remains exact about the residual: an early raw self-link,
or a raw cycle whose outside first revisit settles on a simple cycle.
-/

namespace GeneralN

/-- Events one through five of a raw six-event reduction, with their canonical
fixed-stem frames. -/
noncomputable def RawSixEventReduction.tailFixedFrames
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    FiveFixedStemNovelFrames w N start := {
  z₀ := R.z1
  z₁ := R.z2
  z₂ := R.z3
  z₃ := R.z4
  z₄ := R.z5
  order₀₁ := R.order12
  order₁₂ := R.order23
  order₂₃ := R.order34
  order₃₄ := R.order45
  event₀ := R.event1
  event₁ := R.event2
  event₂ := R.event3
  event₃ := R.event4
  event₄ := R.event5
  frame₀ := Classical.choice (R.event1.fixedStemOpenFrame hN)
  frame₁ := Classical.choice (R.event2.fixedStemOpenFrame hN)
  frame₂ := Classical.choice (R.event3.fixedStemOpenFrame hN)
  frame₃ := Classical.choice (R.event4.fixedStemOpenFrame hN)
  frame₄ := Classical.choice (R.event5.fixedStemOpenFrame hN)
}

/-- The canonical physical triple case on events one through five. -/
def RawSixEventReduction.tailTripleCase
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (htriple : FiveFrameTripleOutcome
      R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4 R.a5 R.z5) :
    FiveFrameTripleCase w N start R.z1 R.z2 R.z3 R.z4 R.z5 := {
  frames := FiveRawClosingFrames.mk
    R.a1 R.q1 R.a2 R.q2 R.a3 R.q3 R.a4 R.q4 R.a5 R.q5
    R.frame1 R.frame2 R.frame3 R.frame4 R.frame5
  triple := htriple
}

/-- Empty-history four-cover is stronger than the exact forbidden six-event
tail cover, whose history contains first writers and event zero. -/
theorem RawSixEventReduction.no_tail_fixed_four_cover
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    Not (NoveltyCoverOn w N start
      (R.tailFixedFrames hN).closePostTimes [] 4) := by
  intro hcover
  apply R.no_tail_four_cover hN
  obtain ⟨fresh, hfresh, hmem⟩ := hcover
  refine ⟨fresh, hfresh, ?_⟩
  intro k hk
  have hk' : k ∈ (R.tailFixedFrames hN).closePostTimes := by
    simpa [RawSixEventReduction.tailFixedFrames,
      FiveFixedStemNovelFrames.closePostTimes] using hk
  have hnew : restrictedTonguesAt w N start k ∈ fresh := by
    simpa using hmem k hk'
  exact List.mem_append_right _ hnew

/-- The opposite-reflector outcome of a selected self-link cycle contradicts
the canonical six-event tail. -/
theorem RawSixEventReduction.tail_opposite_reflector_false
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (htriple : FiveFrameTripleOutcome
      R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4 R.a5 R.z5)
    (S : SelectedFiveFrameABCABC (R.tailTripleCase htriple))
    (Cyc : RawCycleThroughSelfLink w start
      ((R.tailTripleCase htriple).frames.closingAt S.i0))
    {outside : Nat} {atRepeat : Prod Nat Tongues} {visited : Nat}
    (A : ManufacturedReflector w outside (3 * (Cyc.branch / 3)))
    (state : Tongues) (backSteps : Nat)
    (hmouth : w.link (3 * (Cyc.branch / 3)) = some outside)
    (hvisited : stepN w visited (outside, Cyc.state) = some atRepeat)
    (hA : PathGrooves A.toSupported.paths state)
    (hbase : A.baseState = Cyc.state)
    (hstate : state = A.activatedState)
    (hback : stepN w backSteps atRepeat =
      some (3 * (Cyc.branch / 3), state)) : False := by
  apply R.no_tail_fixed_four_cover hN
  exact Cyc.five_close_cover_of_opposite_reflector
    (R.tailFixedFrames hN) (R.tailTripleCase htriple) S
      A state backSteps hmouth hvisited hA hbase hstate hback

/-- The outside first revisit must therefore settle on a simple cycle. -/
theorem RawSixEventReduction.tail_cycle_first_revisit_simple
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (R : RawSixEventReduction w N start)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (htriple : FiveFrameTripleOutcome
      R.a1 R.z1 R.a2 R.z2 R.a3 R.z3 R.a4 R.z4 R.a5 R.z5)
    (S : SelectedFiveFrameABCABC (R.tailTripleCase htriple))
    (Cyc : RawCycleThroughSelfLink w start
      ((R.tailTripleCase htriple).frames.closingAt S.i0)) :
    exists outside atRepeat visited,
      w.link (3 * (Cyc.branch / 3)) = some outside /\
      stepN w visited (outside, Cyc.state) = some atRepeat /\
      SettlesOnSimpleCycle w atRepeat := by
  obtain ⟨outside, atRepeat, visited, hmouth, hvisited, houtcome⟩ :=
    Cyc.outside_first_revisit_cycle_or_reflector
  rcases houtcome with hcycle | hreflector
  · exact ⟨outside, atRepeat, visited, hmouth, hvisited, hcycle⟩
  · obtain ⟨A, state, backSteps, hA, hbase, hstate, hback,
        _hpreserves⟩ := hreflector
    exact (R.tail_opposite_reflector_false hN htriple S Cyc
      A state backSteps hmouth hvisited hA hbase hstate hback).elim

end GeneralN
