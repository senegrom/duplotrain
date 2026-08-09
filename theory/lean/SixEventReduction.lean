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

/-- **Raw six-event reduction.**  Every failure of the constant-five
repeated-novelty target has a canonical first event followed by one actual
five-frame serial-or-triple obstruction. -/
theorem six_repeated_novelties_reduce_to_first_and_tail
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hsix : 6 ≤ (rawRepeatedWriterNovelTimes w N start K).length) :
    Nonempty (RawSixEventReduction w N start) := by
  classical
  let events := rawRepeatedWriterNovelTimes w N start K
  have hsixEvents : 6 ≤ events.length := by
    simpa [events] using hsix
  let z0 := events[0]'(by omega)
  let z1 := events[1]'(by omega)
  let z2 := events[2]'(by omega)
  let z3 := events[3]'(by omega)
  let z4 := events[4]'(by omega)
  let z5 := events[5]'(by omega)
  have hsorted : events.Pairwise (· < ·) := by
    dsimp [events]
    unfold rawRepeatedWriterNovelTimes
    exact List.pairwise_lt_range.filter _
  have hget := List.pairwise_iff_getElem.mp hsorted
  have h01 : z0 < z1 := hget 0 1 (by omega) (by omega) (by omega)
  have h12 : z1 < z2 := hget 1 2 (by omega) (by omega) (by omega)
  have h23 : z2 < z3 := hget 2 3 (by omega) (by omega) (by omega)
  have h34 : z3 < z4 := hget 3 4 (by omega) (by omega) (by omega)
  have h45 : z4 < z5 := hget 4 5 (by omega) (by omega) (by omega)
  have hmem0 : z0 ∈ events := by
    simpa [z0] using List.getElem_mem events (n := 0) (by omega)
  have hmem1 : z1 ∈ events := by
    simpa [z1] using List.getElem_mem events (n := 1) (by omega)
  have hmem2 : z2 ∈ events := by
    simpa [z2] using List.getElem_mem events (n := 2) (by omega)
  have hmem3 : z3 ∈ events := by
    simpa [z3] using List.getElem_mem events (n := 3) (by omega)
  have hmem4 : z4 ∈ events := by
    simpa [z4] using List.getElem_mem events (n := 4) (by omega)
  have hmem5 : z5 ∈ events := by
    simpa [z5] using List.getElem_mem events (n := 5) (by omega)
  have H0 : RawRepeatedWriterNovelAt w N start z0 :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem0)).2
  have H1 : RawRepeatedWriterNovelAt w N start z1 :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem1)).2
  have H2 : RawRepeatedWriterNovelAt w N start z2 :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem2)).2
  have H3 : RawRepeatedWriterNovelAt w N start z3 :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem3)).2
  have H4 : RawRepeatedWriterNovelAt w N start z4 :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem4)).2
  have H5 : RawRepeatedWriterNovelAt w N start z5 :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem5)).2
  have hfirst : ∀ k, k < z0 →
      ¬ RawRepeatedWriterNovelAt w N start k := by
    intro k hk Hk
    have hz0K : z0 < K :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp (by
        simpa [events] using hmem0)).1
    have hkMem : k ∈ events := by
      dsimp [events]
      exact mem_rawRepeatedWriterNovelTimes_iff.mpr
        ⟨by omega, Hk⟩
    have hmin : z0 ≤ k := by
      have hpositive : 0 < events.length := by omega
      simpa [z0] using
        first_getElem_le_of_pairwise_lt events hsorted hpositive k hkMem
    omega
  obtain ⟨a1, q1, a2, q2, a3, q3, a4, q4, a5, q5,
      F1, F2, F3, F4, F5, hshape⟩ :=
    five_repeated_novelties_serial_or_triple hN
      h12 h23 h34 h45 H1 H2 H3 H4 H5
  exact ⟨{
    z0 := z0
    z1 := z1
    z2 := z2
    z3 := z3
    z4 := z4
    z5 := z5
    order01 := h01
    order12 := h12
    order23 := h23
    order34 := h34
    order45 := h45
    event0 := H0
    event1 := H1
    event2 := H2
    event3 := H3
    event4 := H4
    event5 := H5
    first0 := hfirst
    a1 := a1
    q1 := q1
    a2 := a2
    q2 := q2
    a3 := a3
    q3 := q3
    a4 := a4
    q4 := q4
    a5 := a5
    q5 := q5
    frame1 := F1
    frame2 := F2
    frame3 := F3
    frame4 := F4
    frame5 := F5
    tail_shape := hshape
  }⟩

end GeneralN
