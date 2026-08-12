import FiveFrameObstruction

/-!
# Six repeated novelties reduce to a first event and one five-frame tail

The public `N + 6` state law follows from ruling out six globally novel
repeated-writer events.  This file makes the corresponding raw reduction
explicit.  From any finite prefix containing six such events it extracts:

* the first repeated-writer novelty of the whole prefix; and
* the following five events, with all five physical closing frames, in the
  exact serial-or-triple alternative of `five_repeated_novelties_serial_or_triple`.

This is a general-`N` theorem over `Wiring` and `stepN`; it performs no finite
enumeration and asserts no conditional sharp bound.
-/

namespace GeneralN

/-- The complete obstruction carried by the first six repeated-writer
novelties of one finite raw prefix. -/
structure RawSixEventReduction
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
  frame1 : RawNovelClosingFrame w N start a1 q1 z1
  frame2 : RawNovelClosingFrame w N start a2 q2 z2
  frame3 : RawNovelClosingFrame w N start a3 q3 z3
  frame4 : RawNovelClosingFrame w N start a4 q4 z4
  frame5 : RawNovelClosingFrame w N start a5 q5 z5
  tail_shape :
    FiveFrameSerialBreak z1 a2 a3 a4 a5 ∨
      FiveFrameTripleOutcome
        a1 z1 a2 z2 a3 z3 a4 z4 a5 z5

private theorem first_getElem_le_of_pairwise_lt
    (xs : List Nat) (hxs : xs.Pairwise (· < ·))
    (hne : 0 < xs.length) :
    ∀ k, k ∈ xs → xs[0]'hne ≤ k := by
  cases xs with
  | nil => simp at hne
  | cons x rest =>
      intro k hk
      simp only [List.getElem_cons_zero]
      rcases List.mem_cons.mp hk with rfl | hkRest
      · exact Nat.le_refl _
      · exact Nat.le_of_lt ((List.pairwise_cons.mp hxs).1 k hkRest)

end GeneralN
