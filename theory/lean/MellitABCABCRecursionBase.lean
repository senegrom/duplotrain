import MellitRamanResidueDescent
import SharpSixEventAssembly

/-!
# The raw ABCABC recursion base

Three raw last-writer frames in endpoint order

`a0 < a1 < a2 < z0 < z1 < z2`

already contain two literal overlapping BABAs: the first two frames and the
last two frames.  This is the direct bridge from a selected raw `ABCABC`
triple to the Mellit/Raman descent; no endpoint-empty compiler is needed.

The terminal branch of that descent is also exact.  If all five open gaps
are unproductive, the six endpoint writes are `A,B,C,A,B,C`.  The three
writers are pairwise different, so their flips commute and cancel.  The
post-vector at `z2` is therefore the vector at `a0`, contradicting novelty
at `z2`.

Everything here is general in `N` and stated directly over `Wiring` and
`stepN`.
-/

namespace GeneralN

/-- Recover the raw closing frame selected by a `Fin 5` index.  The endpoint
selectors in `TripleFramePhysicalClosure` retained the index but did not yet
expose this dependent accessor. -/
theorem FiveRawClosingFrames.outerFrameAt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    ∀ i : Fin 5,
      RawLastWriterFrame w N start
        (F.openingAt i) (F.closingAt i) :=
  fun i =>
    Fin.cases F.frame₀.outer (fun i1 =>
      Fin.cases F.frame₁.outer (fun i2 =>
        Fin.cases F.frame₂.outer (fun i3 =>
          Fin.cases F.frame₃.outer (fun i4 =>
            Fin.cases F.frame₄.outer (fun i5 => Fin.elim0 i5) i4) i3) i2) i1) i

/-- The first two frames of a raw `ABCABC` endpoint pattern form a BABA. -/
theorem rawABCABCFirstBABA
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {a0 z0 a1 z1 a2 z2 : Nat}
    (F0 : RawLastWriterFrame w N start a0 z0)
    (F1 : RawLastWriterFrame w N start a1 z1)
    (H : EndpointABCABC a0 z0 a1 z1 a2 z2) :
    RawBABAInterlacement w N start a0 a1 z0 z1 := {
  prior_lt_second := H.1
  second_lt_reroute := Nat.lt_trans H.2.1 H.2.2.1
  reroute_lt_third := H.2.2.2.1
  leftFrame := F0
  rightFrame := F1
  different_writers := F1.no_same_writer_between z0
    (Nat.lt_trans H.2.1 H.2.2.1) H.2.2.2.1 F0.close_productive
}

/-- Shifting one frame right gives the strictly shorter selected-tail BABA. -/
theorem rawABCABCSecondBABA
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {a0 z0 a1 z1 a2 z2 : Nat}
    (F1 : RawLastWriterFrame w N start a1 z1)
    (F2 : RawLastWriterFrame w N start a2 z2)
    (H : EndpointABCABC a0 z0 a1 z1 a2 z2) :
    RawBABAInterlacement w N start a1 a2 z1 z2 := {
  prior_lt_second := H.2.1
  second_lt_reroute := Nat.lt_trans H.2.2.1 H.2.2.2.1
  reroute_lt_third := H.2.2.2.2
  leftFrame := F1
  rightFrame := F2
  different_writers := F2.no_same_writer_between z1
    (Nat.lt_trans H.2.2.1 H.2.2.2.1) H.2.2.2.2
    F1.close_productive
}

/-- The first two frames of a selected raw `ABCABC` triple directly supply
the BABA used by the Mellit/Raman argument. -/
theorem SelectedFiveFrameABCABC.firstTwoRawBABA
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameABCABC T) :
    RawBABAInterlacement w N start
      (T.frames.openingAt S.i0) (T.frames.openingAt S.i1)
      (T.frames.closingAt S.i0) (T.frames.closingAt S.i1) :=
  rawABCABCFirstBABA
    (T.frames.outerFrameAt S.i0)
    (T.frames.outerFrameAt S.i1) S.shape

/-- Advancing to the second and third selected frames consumes the first
selected close and provides the adjacent BABA for the recursive call. -/
theorem SelectedFiveFrameABCABC.lastTwoRawBABA
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameABCABC T) :
    RawBABAInterlacement w N start
      (T.frames.openingAt S.i1) (T.frames.openingAt S.i2)
      (T.frames.closingAt S.i1) (T.frames.closingAt S.i2) :=
  rawABCABCSecondBABA
    (T.frames.outerFrameAt S.i1)
    (T.frames.outerFrameAt S.i2) S.shape

/-- Across a quiet open gap, the represented vector at the next endpoint is
the represented vector immediately after the preceding endpoint. -/
private theorem restrictedTonguesAt_eq_after_quiet_gap
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {left right : Nat}
    (horder : left < right)
    (hright : RawProductiveAt w N start right)
    (hquiet : ∀ k, left < k → k < right →
      ¬ RawProductiveAt w N start k) :
    restrictedTonguesAt w N start right =
      restrictedTonguesAt w N start (left + 1) := by
  obtain ⟨post, hpost⟩ :=
    Option.isSome_iff_exists.mp hright.1
  obtain ⟨finish, hfinish⟩ := stepN_prefix_some
    (d := right) (K := right + 1) (by omega) hpost
  let span := right - (left + 1)
  have hsum : left + 1 + span = right := by
    dsimp [span]
    omega
  have h := restrictedTonguesAt_eq_of_quiet_interval
    (first := left + 1) (span := span) (finish := finish)
    (by simpa [hsum] using hfinish) (by
      intro k hkLeft hkRight
      apply hquiet k <;> omega)
  simpa [hsum] using h

/-- Six quiet endpoint writes in `ABCABC` order restore the represented
vector exactly. -/
theorem rawABCABC_quiet_return
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {a0 z0 a1 z1 a2 z2 : Nat}
    (F0 : RawLastWriterFrame w N start a0 z0)
    (F1 : RawLastWriterFrame w N start a1 z1)
    (F2 : RawLastWriterFrame w N start a2 z2)
    (H : EndpointABCABC a0 z0 a1 z1 a2 z2)
    (hquiet01 : ∀ k, a0 < k → k < a1 →
      ¬ RawProductiveAt w N start k)
    (hquiet12 : ∀ k, a1 < k → k < a2 →
      ¬ RawProductiveAt w N start k)
    (hquiet20 : ∀ k, a2 < k → k < z0 →
      ¬ RawProductiveAt w N start k)
    (hquiet03 : ∀ k, z0 < k → k < z1 →
      ¬ RawProductiveAt w N start k)
    (hquiet34 : ∀ k, z1 < k → k < z2 →
      ¬ RawProductiveAt w N start k) :
    restrictedTonguesAt w N start (z2 + 1) =
      restrictedTonguesAt w N start a0 := by
  let C0 := rawWriterAt w start z0
  let C1 := rawWriterAt w start z1
  let C2 := rawWriterAt w start z2
  have ha0a1 := H.1
  have ha1a2 := H.2.1
  have ha2z0 := H.2.2.1
  have hz0z1 := H.2.2.2.1
  have hz1z2 := H.2.2.2.2
  have hC01 : C0 ≠ C1 := by
    simpa [C0, C1] using F1.no_same_writer_between z0
      (Nat.lt_trans ha1a2 ha2z0) hz0z1 F0.close_productive
  have hC02 : C0 ≠ C2 := by
    simpa [C0, C2] using F2.no_same_writer_between z0
      ha2z0 (Nat.lt_trans hz0z1 hz1z2) F0.close_productive
  have hC12 : C1 ≠ C2 := by
    simpa [C1, C2] using F2.no_same_writer_between z1
      (Nat.lt_trans ha2z0 hz0z1) hz1z2 F1.close_productive
  have hstable01 := restrictedTonguesAt_eq_after_quiet_gap
    ha0a1 F1.open_productive hquiet01
  have hstable12 := restrictedTonguesAt_eq_after_quiet_gap
    ha1a2 F2.open_productive hquiet12
  have hstable20 := restrictedTonguesAt_eq_after_quiet_gap
    ha2z0 F0.close_productive hquiet20
  have hstable03 := restrictedTonguesAt_eq_after_quiet_gap
    hz0z1 F1.close_productive hquiet03
  have hstable34 := restrictedTonguesAt_eq_after_quiet_gap
    hz1z2 F2.close_productive hquiet34
  have hflipA0 : restrictedTonguesAt w N start (a0 + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start a0) C0) := by
    have h := rawProductiveAt_restricted_flip hN F0.open_productive
    simpa [C0, F0.same_writer] using h
  have hflipA1 : restrictedTonguesAt w N start (a1 + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start a1) C1) := by
    have h := rawProductiveAt_restricted_flip hN F1.open_productive
    simpa [C1, F1.same_writer] using h
  have hflipA2 : restrictedTonguesAt w N start (a2 + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start a2) C2) := by
    have h := rawProductiveAt_restricted_flip hN F2.open_productive
    simpa [C2, F2.same_writer] using h
  have hflipZ0 : restrictedTonguesAt w N start (z0 + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start z0) C0) := by
    simpa [C0] using rawProductiveAt_restricted_flip
      hN F0.close_productive
  have hflipZ1 : restrictedTonguesAt w N start (z1 + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start z1) C1) := by
    simpa [C1] using rawProductiveAt_restricted_flip
      hN F1.close_productive
  have hflipZ2 : restrictedTonguesAt w N start (z2 + 1) =
      VectorCount.restrict N (flipAt (tonguesAt w start z2) C2) := by
    simpa [C2] using rawProductiveAt_restricted_flip
      hN F2.close_productive
  have hcornerA1 : restrictedTonguesAt w N start (a1 + 1) =
      VectorCount.restrict N
        (flipAt (flipAt (tonguesAt w start a0) C0) C1) := by
    calc
      restrictedTonguesAt w N start (a1 + 1) =
          VectorCount.restrict N (flipAt (tonguesAt w start a1) C1) :=
        hflipA1
      _ = VectorCount.restrict N
          (flipAt (tonguesAt w start (a0 + 1)) C1) :=
        restrict_flipAt_congr hstable01
      _ = VectorCount.restrict N
          (flipAt (flipAt (tonguesAt w start a0) C0) C1) :=
        restrict_flipAt_congr hflipA0
  have hcornerA2 : restrictedTonguesAt w N start (a2 + 1) =
      VectorCount.restrict N
        (flipAt (flipAt (flipAt (tonguesAt w start a0) C0) C1) C2) := by
    calc
      restrictedTonguesAt w N start (a2 + 1) =
          VectorCount.restrict N (flipAt (tonguesAt w start a2) C2) :=
        hflipA2
      _ = VectorCount.restrict N
          (flipAt (tonguesAt w start (a1 + 1)) C2) :=
        restrict_flipAt_congr hstable12
      _ = VectorCount.restrict N
          (flipAt (flipAt (flipAt (tonguesAt w start a0) C0) C1) C2) :=
        restrict_flipAt_congr hcornerA1
  have hcornerZ0 : restrictedTonguesAt w N start (z0 + 1) =
      VectorCount.restrict N
        (flipAt
          (flipAt (flipAt (flipAt (tonguesAt w start a0) C0) C1) C2) C0) := by
    calc
      restrictedTonguesAt w N start (z0 + 1) =
          VectorCount.restrict N (flipAt (tonguesAt w start z0) C0) :=
        hflipZ0
      _ = VectorCount.restrict N
          (flipAt (tonguesAt w start (a2 + 1)) C0) :=
        restrict_flipAt_congr hstable20
      _ = VectorCount.restrict N
          (flipAt
            (flipAt (flipAt (flipAt (tonguesAt w start a0) C0) C1) C2) C0) :=
        restrict_flipAt_congr hcornerA2
  have hcornerZ1 : restrictedTonguesAt w N start (z1 + 1) =
      VectorCount.restrict N
        (flipAt
          (flipAt
            (flipAt (flipAt (flipAt (tonguesAt w start a0) C0) C1) C2) C0) C1) := by
    calc
      restrictedTonguesAt w N start (z1 + 1) =
          VectorCount.restrict N (flipAt (tonguesAt w start z1) C1) :=
        hflipZ1
      _ = VectorCount.restrict N
          (flipAt (tonguesAt w start (z0 + 1)) C1) :=
        restrict_flipAt_congr hstable03
      _ = VectorCount.restrict N
          (flipAt
            (flipAt
              (flipAt (flipAt (flipAt (tonguesAt w start a0) C0) C1) C2) C0) C1) :=
        restrict_flipAt_congr hcornerZ0
  calc
    restrictedTonguesAt w N start (z2 + 1) =
        VectorCount.restrict N (flipAt (tonguesAt w start z2) C2) :=
      hflipZ2
    _ = VectorCount.restrict N
        (flipAt (tonguesAt w start (z1 + 1)) C2) :=
      restrict_flipAt_congr hstable34
    _ = VectorCount.restrict N
        (flipAt
          (flipAt
            (flipAt
              (flipAt (flipAt (flipAt (tonguesAt w start a0) C0) C1) C2) C0) C1) C2) :=
      restrict_flipAt_congr hcornerZ1
    _ = restrictedTonguesAt w N start a0 := by
      rw [flipAt_comm (Ne.symm hC02),
        flipAt_comm (Ne.symm hC01), flipAt_flipAt,
        flipAt_comm (Ne.symm hC12), flipAt_flipAt, flipAt_flipAt]
      rfl

/-- The quiet branch of raw `ABCABC` is impossible as soon as its last
close is novel.  This is the contradiction base of the selected-tail
recursion, not another residual outcome. -/
theorem rawABCABC_quiet_false
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {a0 z0 a1 z1 a2 z2 : Nat}
    (F0 : RawLastWriterFrame w N start a0 z0)
    (F1 : RawLastWriterFrame w N start a1 z1)
    (F2 : RawLastWriterFrame w N start a2 z2)
    (H : EndpointABCABC a0 z0 a1 z1 a2 z2)
    (hnovel : RawNovelAt w N start z2)
    (hquiet01 : ∀ k, a0 < k → k < a1 →
      ¬ RawProductiveAt w N start k)
    (hquiet12 : ∀ k, a1 < k → k < a2 →
      ¬ RawProductiveAt w N start k)
    (hquiet20 : ∀ k, a2 < k → k < z0 →
      ¬ RawProductiveAt w N start k)
    (hquiet03 : ∀ k, z0 < k → k < z1 →
      ¬ RawProductiveAt w N start k)
    (hquiet34 : ∀ k, z1 < k → k < z2 →
      ¬ RawProductiveAt w N start k) : False := by
  apply hnovel
  apply List.mem_map.mpr
  refine ⟨a0, List.mem_range.mpr ?_, ?_⟩
  · have ha0z2 : a0 < z2 :=
      Nat.lt_trans H.1
        (Nat.lt_trans H.2.1
          (Nat.lt_trans H.2.2.1
            (Nat.lt_trans H.2.2.2.1 H.2.2.2.2)))
    omega
  · exact (rawABCABC_quiet_return hN F0 F1 F2 H
      hquiet01 hquiet12 hquiet20 hquiet03 hquiet34).symm

/-- Selected-triple form of the contradiction base.  This is the direct
consumer needed by the sharp six-event assembly: no certified endpoint-empty
`ABCABC` object appears in the statement. -/
theorem SelectedFiveFrameABCABC.quiet_false
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameABCABC T)
    (hnovel : RawNovelAt w N start (T.frames.closingAt S.i2))
    (hquiet01 : ∀ k,
      T.frames.openingAt S.i0 < k →
      k < T.frames.openingAt S.i1 →
      ¬ RawProductiveAt w N start k)
    (hquiet12 : ∀ k,
      T.frames.openingAt S.i1 < k →
      k < T.frames.openingAt S.i2 →
      ¬ RawProductiveAt w N start k)
    (hquiet20 : ∀ k,
      T.frames.openingAt S.i2 < k →
      k < T.frames.closingAt S.i0 →
      ¬ RawProductiveAt w N start k)
    (hquiet03 : ∀ k,
      T.frames.closingAt S.i0 < k →
      k < T.frames.closingAt S.i1 →
      ¬ RawProductiveAt w N start k)
    (hquiet34 : ∀ k,
      T.frames.closingAt S.i1 < k →
      k < T.frames.closingAt S.i2 →
      ¬ RawProductiveAt w N start k) : False :=
  rawABCABC_quiet_false hN
    (T.frames.outerFrameAt S.i0)
    (T.frames.outerFrameAt S.i1)
    (T.frames.outerFrameAt S.i2)
    S.shape hnovel hquiet01 hquiet12 hquiet20 hquiet03 hquiet34

end GeneralN
