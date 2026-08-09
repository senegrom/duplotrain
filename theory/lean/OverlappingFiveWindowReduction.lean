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

private theorem pairwise_getElem_zero_le
    (xs : List Nat) (hxs : xs.Pairwise (· < ·))
    (hne : 0 < xs.length) :
    ∀ k, k ∈ xs → xs[0]'hne ≤ k := by
  intro k hk
  obtain ⟨j, hj, hvalue⟩ := List.getElem_of_mem hk
  by_cases hj0 : j = 0
  · subst j
    exact Nat.le_of_eq hvalue
  · have h0j : 0 < j := by omega
    have hlt := (List.pairwise_iff_getElem.mp hxs)
      0 j hne hj h0j
    rw [hvalue] at hlt
    exact Nat.le_of_lt hlt

/-- Adjacent elements of a strictly increasing list have no list member
strictly between them. -/
private theorem pairwise_getElem_adjacent_no_between
    (xs : List Nat) (hxs : xs.Pairwise (· < ·))
    (i : Nat) (hi : i + 1 < xs.length) :
    ∀ k, k ∈ xs → xs[i]'(by omega) < k →
      k < xs[i+1]'hi → False := by
  intro k hk hleft hright
  obtain ⟨j, hj, hvalue⟩ := List.getElem_of_mem hk
  have hget := List.pairwise_iff_getElem.mp hxs
  by_cases hji : j ≤ i
  · by_cases hEq : j = i
    · subst j
      rw [hvalue] at hleft
      exact (Nat.lt_irrefl k hleft).elim
    · have hji' : j < i := by omega
      have hlt := hget j i hj (by omega) hji'
      rw [hvalue] at hlt
      omega
  · have hij : i < j := by omega
    by_cases hEq : j = i + 1
    · subst j
      rw [hvalue] at hright
      exact (Nat.lt_irrefl k hright).elim
    · have hi1j : i + 1 < j := by omega
      have hlt := hget (i+1) j hi hj hi1j
      rw [hvalue] at hlt
      omega

/-- The canonical first six repeated novelties, including the fact that no
additional repeated novelty lies between adjacent selected events. -/
structure RawConsecutiveSixEvents
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
  no_event01 : ∀ k, z0 < k → k < z1 →
    ¬ RawRepeatedWriterNovelAt w N start k
  no_event12 : ∀ k, z1 < k → k < z2 →
    ¬ RawRepeatedWriterNovelAt w N start k
  no_event23 : ∀ k, z2 < k → k < z3 →
    ¬ RawRepeatedWriterNovelAt w N start k
  no_event34 : ∀ k, z3 < k → k < z4 →
    ¬ RawRepeatedWriterNovelAt w N start k
  no_event45 : ∀ k, z4 < k → k < z5 →
    ¬ RawRepeatedWriterNovelAt w N start k

/-- Extract the canonical first six events with all five no-gap facts. -/
theorem six_repeated_novelties_have_consecutive_first_six
    {w : Wiring} {N : Nat} (start : Nat × Tongues) (K : Nat)
    (hsix : 6 ≤ (rawRepeatedWriterNovelTimes w N start K).length) :
    Nonempty (RawConsecutiveSixEvents w N start) := by
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
  have eventOfMem : ∀ {k}, k ∈ events →
      RawRepeatedWriterNovelAt w N start k := by
    intro k hk
    exact (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hk)).2
  have H0 := eventOfMem hmem0
  have H1 := eventOfMem hmem1
  have H2 := eventOfMem hmem2
  have H3 := eventOfMem hmem3
  have H4 := eventOfMem hmem4
  have H5 := eventOfMem hmem5
  have eventMem : ∀ {k}, RawRepeatedWriterNovelAt w N start k →
      k < K → k ∈ events := by
    intro k Hk hkK
    dsimp [events]
    exact mem_rawRepeatedWriterNovelTimes_iff.mpr ⟨hkK, Hk⟩
  have hz0K : z0 < K :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem0)).1
  have hz1K : z1 < K :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem1)).1
  have hz2K : z2 < K :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem2)).1
  have hz3K : z3 < K :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem3)).1
  have hz4K : z4 < K :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem4)).1
  have hz5K : z5 < K :=
    (mem_rawRepeatedWriterNovelTimes_iff.mp (by
      simpa [events] using hmem5)).1
  refine ⟨{
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
    first0 := by
      intro k hk Hk
      have hkMem := eventMem Hk (by omega)
      have hmin : z0 ≤ k := by
        simpa [z0] using pairwise_getElem_zero_le events hsorted
          (by omega) k hkMem
      omega
    no_event01 := by
      intro k hk0 hk1 Hk
      exact pairwise_getElem_adjacent_no_between events hsorted 0
        (by omega) k (eventMem Hk (by omega))
        (by simpa [z0] using hk0) (by simpa [z1] using hk1)
    no_event12 := by
      intro k hk1 hk2 Hk
      exact pairwise_getElem_adjacent_no_between events hsorted 1
        (by omega) k (eventMem Hk (by omega))
        (by simpa [z1] using hk1) (by simpa [z2] using hk2)
    no_event23 := by
      intro k hk2 hk3 Hk
      exact pairwise_getElem_adjacent_no_between events hsorted 2
        (by omega) k (eventMem Hk (by omega))
        (by simpa [z2] using hk2) (by simpa [z3] using hk3)
    no_event34 := by
      intro k hk3 hk4 Hk
      exact pairwise_getElem_adjacent_no_between events hsorted 3
        (by omega) k (eventMem Hk (by omega))
        (by simpa [z3] using hk3) (by simpa [z4] using hk4)
    no_event45 := by
      intro k hk4 hk5 Hk
      exact pairwise_getElem_adjacent_no_between events hsorted 4
        (by omega) k (eventMem Hk (by omega))
        (by simpa [z4] using hk4) (by simpa [z5] using hk5)
  }⟩

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
  no_event01 : ∀ k, z0 < k → k < z1 →
    ¬ RawRepeatedWriterNovelAt w N start k
  no_event12 : ∀ k, z1 < k → k < z2 →
    ¬ RawRepeatedWriterNovelAt w N start k
  no_event23 : ∀ k, z2 < k → k < z3 →
    ¬ RawRepeatedWriterNovelAt w N start k
  no_event34 : ∀ k, z3 < k → k < z4 →
    ¬ RawRepeatedWriterNovelAt w N start k
  no_event45 : ∀ k, z4 < k → k < z5 →
    ¬ RawRepeatedWriterNovelAt w N start k
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

/-- Apply the five-frame theorem to both windows of one fixed canonical
six-event sequence.  Uniqueness of last-writer openings identifies the four
shared frames, so both outcomes are expressed with one common set of raw
frame endpoints. -/
theorem RawConsecutiveSixEvents.overlapping_windows
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (C : RawConsecutiveSixEvents w N start) :
    Nonempty (RawOverlappingFiveWindowReduction w N start) := by
  obtain ⟨a0, q0, a1, q1, a2, q2, a3, q3, a4, q4,
      F0, F1, F2, F3, F4, headShape⟩ :=
    five_repeated_novelties_serial_or_triple hN
      C.order01 C.order12 C.order23 C.order34
      C.event0 C.event1 C.event2 C.event3 C.event4
  obtain ⟨b1, _r1, b2, _r2, b3, _r3, b4, _r4, b5, r5,
      G1, G2, G3, G4, G5, tailShape⟩ :=
    five_repeated_novelties_serial_or_triple hN
      C.order12 C.order23 C.order34 C.order45
      C.event1 C.event2 C.event3 C.event4 C.event5
  have hb1 : b1 = a1 :=
    rawLastWriterFrame_open_eq_same_close G1.outer F1.outer
  have hb2 : b2 = a2 :=
    rawLastWriterFrame_open_eq_same_close G2.outer F2.outer
  have hb3 : b3 = a3 :=
    rawLastWriterFrame_open_eq_same_close G3.outer F3.outer
  have hb4 : b4 = a4 :=
    rawLastWriterFrame_open_eq_same_close G4.outer F4.outer
  subst b1
  subst b2
  subst b3
  subst b4
  exact ⟨{
    z0 := C.z0
    z1 := C.z1
    z2 := C.z2
    z3 := C.z3
    z4 := C.z4
    z5 := C.z5
    order01 := C.order01
    order12 := C.order12
    order23 := C.order23
    order34 := C.order34
    order45 := C.order45
    event0 := C.event0
    event1 := C.event1
    event2 := C.event2
    event3 := C.event3
    event4 := C.event4
    event5 := C.event5
    first0 := C.first0
    no_event01 := C.no_event01
    no_event12 := C.no_event12
    no_event23 := C.no_event23
    no_event34 := C.no_event34
    no_event45 := C.no_event45
    a0 := a0
    q0 := q0
    a1 := a1
    q1 := q1
    a2 := a2
    q2 := q2
    a3 := a3
    q3 := q3
    a4 := a4
    q4 := q4
    a5 := b5
    q5 := r5
    frame0 := F0
    frame1 := F1
    frame2 := F2
    frame3 := F3
    frame4 := F4
    frame5 := G5
    head_shape := headShape
    tail_shape := tailShape
  }⟩

/-- Any six-event failure of `FiveRepeatedWriterNovelty` supplies both
overlapping five-frame outcomes over the same canonical six raw events, with
the five consecutive-event facts retained. -/
theorem six_repeated_novelties_reduce_to_overlapping_windows
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hsix : 6 ≤ (rawRepeatedWriterNovelTimes w N start K).length) :
    Nonempty (RawOverlappingFiveWindowReduction w N start) := by
  obtain ⟨C⟩ :=
    six_repeated_novelties_have_consecutive_first_six start K hsix
  exact C.overlapping_windows hN

end GeneralN
