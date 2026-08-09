import SixEventReduction

/-!
# Six novelties force two overlapping five-frame obstructions

The constant-five target fails only if six repeated-writer novelties occur.
`SixEventReduction` keeps the first novelty separate and applies the
five-frame theorem to the last five.  For the sharp closure it is useful to
retain the *other* five-event window as well.

This file packages one closing frame for each of the six events and applies
`five_repeated_novelties_serial_or_triple` to both overlapping windows

* `z0,z1,z2,z3,z4`, and
* `z1,z2,z3,z4,z5`.

Thus every alleged six-event counterexample has exactly four remaining
top-level cases: serial/serial, serial/triple, triple/serial, or
triple/triple.  No continuation, compiler certificate, or finite-`N`
enumeration occurs in the statement.
-/

namespace GeneralN

private theorem rawLastWriterFrame_open_eq_same_close
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {a b close : Nat}
    (F : RawLastWriterFrame w N start a close)
    (G : RawLastWriterFrame w N start b close) :
    a = b := by
  by_cases hab : a < b
  · exact (F.no_same_writer_between b hab G.order G.open_productive
      G.same_writer).elim
  · by_cases hba : b < a
    · exact (G.no_same_writer_between a hba F.order F.open_productive
        F.same_writer).elim
    · omega

/-- The raw data of six chronological repeated-writer novelties, one actual
closing frame for each event, and the serial-or-triple outcome in both
overlapping five-event windows. -/
structure RawOverlappingFiveWindowReduction
    (w : Wiring) (N : Nat) (start : Nat × Tongues) where
  z0 : Nat
  z1 : Nat
  z2 : Nat
  z3 : Nat
  z4 : Nat
  z5 : Nat
  order01 : z0 < z1
  order12 : z1 < z2
  order23 : z2 < z3
  order34 : z3 < z4
  order45 : z4 < z5
  event0 : RawRepeatedWriterNovelAt w N start z0
  event1 : RawRepeatedWriterNovelAt w N start z1
  event2 : RawRepeatedWriterNovelAt w N start z2
  event3 : RawRepeatedWriterNovelAt w N start z3
  event4 : RawRepeatedWriterNovelAt w N start z4
  event5 : RawRepeatedWriterNovelAt w N start z5
  first0 : ∀ k, k < z0 → ¬ RawRepeatedWriterNovelAt w N start k
  a0 : Nat
  q0 : Nat
  a1 : Nat
  q1 : Nat
  a2 : Nat
  q2 : Nat
  a3 : Nat
  q3 : Nat
  a4 : Nat
  q4 : Nat
  a5 : Nat
  q5 : Nat
  frame0 : RawNovelClosingFrame w N start a0 q0 z0
  frame1 : RawNovelClosingFrame w N start a1 q1 z1
  frame2 : RawNovelClosingFrame w N start a2 q2 z2
  frame3 : RawNovelClosingFrame w N start a3 q3 z3
  frame4 : RawNovelClosingFrame w N start a4 q4 z4
  frame5 : RawNovelClosingFrame w N start a5 q5 z5
  head_shape :
    FiveFrameSerialBreak z0 a1 a2 a3 a4 ∨
      FiveFrameTripleOutcome
        a0 z0 a1 z1 a2 z2 a3 z3 a4 z4
  tail_shape :
    FiveFrameSerialBreak z1 a2 a3 a4 a5 ∨
      FiveFrameTripleOutcome
        a1 z1 a2 z2 a3 z3 a4 z4 a5 z5

/-- Any six-event failure of `FiveRepeatedWriterNovelty` supplies both
overlapping five-frame outcomes over the same six raw events and the same
six chosen closing frames. -/
theorem six_repeated_novelties_reduce_to_overlapping_windows
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hsix : 6 ≤ (rawRepeatedWriterNovelTimes w N start K).length) :
    Nonempty (RawOverlappingFiveWindowReduction w N start) := by
  obtain ⟨R⟩ :=
    six_repeated_novelties_reduce_to_first_and_tail hN start K hsix
  obtain ⟨a0, q0, frame0⟩ := R.event0.novelClosingFrame hN
  have headShape := five_repeated_novelties_serial_or_triple hN
    R.order01 R.order12 R.order23 R.order34
    R.event0 R.event1 R.event2 R.event3 R.event4
  rcases headShape with
    ⟨b0, r0, b1, r1, b2, r2, b3, r3, b4, r4,
      G0, G1, G2, G3, G4, shape⟩
  have hb0 : b0 = a0 := by
    exact rawLastWriterFrame_open_eq_same_close
      G0.outer frame0.outer
  have hb1 : b1 = R.a1 := by
    exact rawLastWriterFrame_open_eq_same_close
      G1.outer R.frame1.outer
  have hb2 : b2 = R.a2 := by
    exact rawLastWriterFrame_open_eq_same_close
      G2.outer R.frame2.outer
  have hb3 : b3 = R.a3 := by
    exact rawLastWriterFrame_open_eq_same_close
      G3.outer R.frame3.outer
  have hb4 : b4 = R.a4 := by
    exact rawLastWriterFrame_open_eq_same_close
      G4.outer R.frame4.outer
  subst b0
  subst b1
  subst b2
  subst b3
  subst b4
  exact ⟨{
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
    a0 := a0
    q0 := q0
    a1 := R.a1
    q1 := R.q1
    a2 := R.a2
    q2 := R.q2
    a3 := R.a3
    q3 := R.q3
    a4 := R.a4
    q4 := R.q4
    a5 := R.a5
    q5 := R.q5
    frame0 := frame0
    frame1 := R.frame1
    frame2 := R.frame2
    frame3 := R.frame3
    frame4 := R.frame4
    frame5 := R.frame5
    head_shape := shape
    tail_shape := R.tail_shape
  }⟩

end GeneralN
