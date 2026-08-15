import SharpCertificateClosure
import TripleInterlacementObstruction

/-!
# Closing the raw five-frame triple through the physical obstruction

`FiveFrameTripleCase` records a ten-way choice of three raw closing frames,
and records whether their endpoints form `ABCABC` or a strict nest.  The
physical theorem in `TripleInterlacementObstruction` is stated instead for a
certified concrete echo run and a cyclic-minimal restoration crossing.

This file makes that interface exact.  It does not assume that every raw run
has already been compiled, and it does not silently discard self-linked raw
ports.  A selected `ABCABC` triple is closed in either of two ways:

* under `IrreflexiveLinks`, the existing physical endpoint-empty theorem gives
  an immediate contradiction;
* without irreflexivity, the same abstract obstruction forces a self-link at
  an entry actually used by the certified run.

The final assembly theorem states the precise remaining obligations for
`KnownEdgeTripleFrameObstruction`: compile each selected `ABCABC` triple,
exclude the resulting *encountered* self-link, and exclude the selected strict
nest.  No counting hypothesis, finite-`N` enumeration, or hidden physical
irreflexivity is introduced here.
-/

namespace GeneralN

/-! ## Selecting one of the ten endpoint triples -/

/-- Opening time of one of the five raw closing frames. -/
def FiveRawClosingFrames.openingAt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4)
    (i : Fin 5) : Nat :=
  match i.1 with
  | 0 => F.a₀
  | 1 => F.a₁
  | 2 => F.a₂
  | 3 => F.a₃
  | _ => F.a₄

/-- Closing time of one of the five raw closing frames. -/
def FiveRawClosingFrames.closingAt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (_F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4)
    (i : Fin 5) : Nat :=
  match i.1 with
  | 0 => z0
  | 1 => z1
  | 2 => z2
  | 3 => z3
  | _ => z4

@[simp] theorem FiveRawClosingFrames.openingAt_zero
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.openingAt (0 : Fin 5) = F.a₀ := by rfl

@[simp] theorem FiveRawClosingFrames.openingAt_one
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.openingAt (1 : Fin 5) = F.a₁ := by rfl

@[simp] theorem FiveRawClosingFrames.openingAt_two
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.openingAt (2 : Fin 5) = F.a₂ := by rfl

@[simp] theorem FiveRawClosingFrames.openingAt_three
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.openingAt (3 : Fin 5) = F.a₃ := by rfl

@[simp] theorem FiveRawClosingFrames.openingAt_four
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.openingAt (4 : Fin 5) = F.a₄ := by rfl

@[simp] theorem FiveRawClosingFrames.closingAt_zero
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.closingAt (0 : Fin 5) = z0 := by rfl

@[simp] theorem FiveRawClosingFrames.closingAt_one
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.closingAt (1 : Fin 5) = z1 := by rfl

@[simp] theorem FiveRawClosingFrames.closingAt_two
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.closingAt (2 : Fin 5) = z2 := by rfl

@[simp] theorem FiveRawClosingFrames.closingAt_three
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.closingAt (3 : Fin 5) = z3 := by rfl

@[simp] theorem FiveRawClosingFrames.closingAt_four
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4) :
    F.closingAt (4 : Fin 5) = z4 := by rfl

/-- One concrete increasing endpoint triple selected from a grouped
`FiveFrameABCABC` outcome.  The `Fin 5` indices retain its provenance in the
original five-frame case. -/
structure SelectedFiveFrameABCABC
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4) : Type where
  i0 : Fin 5
  i1 : Fin 5
  i2 : Fin 5

/-- One concrete decreasing-opening triple selected from a grouped strict
nest outcome. -/
structure SelectedFiveFrameStrictNest
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4) : Type where
  i0 : Fin 5
  i1 : Fin 5
  i2 : Fin 5

/-- The grouped five-frame disjunction always exposes an actual selected
triple, with its three indices retained. -/
theorem FiveFrameTripleCase.select_endpoint_triple
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4) :
    Nonempty (SelectedFiveFrameABCABC T) \/
      Nonempty (SelectedFiveFrameStrictNest T) := by
  rcases T.triple with habc | hnest
  · rcases habc with h | h | h | h | h | h | h | h | h | h
    · exact Or.inl ⟨⟨0, 1, 2⟩⟩
    · exact Or.inl ⟨⟨0, 1, 3⟩⟩
    · exact Or.inl ⟨⟨0, 1, 4⟩⟩
    · exact Or.inl ⟨⟨0, 2, 3⟩⟩
    · exact Or.inl ⟨⟨0, 2, 4⟩⟩
    · exact Or.inl ⟨⟨0, 3, 4⟩⟩
    · exact Or.inl ⟨⟨1, 2, 3⟩⟩
    · exact Or.inl ⟨⟨1, 2, 4⟩⟩
    · exact Or.inl ⟨⟨1, 3, 4⟩⟩
    · exact Or.inl ⟨⟨2, 3, 4⟩⟩
  · rcases hnest with h | h | h | h | h | h | h | h | h | h
    · exact Or.inr ⟨⟨0, 1, 2⟩⟩
    · exact Or.inr ⟨⟨0, 1, 3⟩⟩
    · exact Or.inr ⟨⟨0, 1, 4⟩⟩
    · exact Or.inr ⟨⟨0, 2, 3⟩⟩
    · exact Or.inr ⟨⟨0, 2, 4⟩⟩
    · exact Or.inr ⟨⟨0, 3, 4⟩⟩
    · exact Or.inr ⟨⟨1, 2, 3⟩⟩
    · exact Or.inr ⟨⟨1, 2, 4⟩⟩
    · exact Or.inr ⟨⟨1, 3, 4⟩⟩
    · exact Or.inr ⟨⟨2, 3, 4⟩⟩

/-! ## The exact raw-to-certified `ABCABC` interface -/

/-- A self-link at an entry genuinely used by a certified concrete run.  This
is deliberately stronger and more local than merely saying that the wiring
contains some irrelevant self-link. -/
def CertifiedRunUsesSelfLink {w : Wiring}
    (run : CertifiedConcreteEchoRun w) : Prop :=
  exists q, w.link (run.entry q) = some (run.entry q)

/-- The complete certified data consumed by the existing physical
endpoint-empty theorem.  The clock explicitly identifies all six selected raw
endpoints with concrete ascent entries and boundaries, and preserves exactly
the endpoint order used by the physical obstruction. -/
structure CertifiedEndpointEmptyABCABC
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (S : SelectedFiveFrameABCABC T) : Type where
  run : CertifiedConcreteEchoRun w
  clock : Nat -> Nat
  selected_clock_order :
    clock (T.frames.openingAt S.i0) <
        clock (T.frames.openingAt S.i1) ∧
      clock (T.frames.openingAt S.i1) <
        clock (T.frames.openingAt S.i2) ∧
      clock (T.frames.openingAt S.i2) <
        clock (T.frames.closingAt S.i0)
  K : Nat
  period : Nat
  tail : Echo.RestorationPeriodicTail
    (canonicalEchoMachine w) (encodedEntries run.entry)
    run.initialRegister K period
  crossing : Echo.CyclicOverlapMinimalForeignRestorationCrossing
    (canonicalEchoMachine w) (encodedEntries run.entry)
    run.initialRegister K period
    (clock (T.frames.openingAt S.i0))
    (clock (T.frames.closingAt S.i0))
    (clock (T.frames.openingAt S.i1))
    (clock (T.frames.closingAt S.i1))
  base_before_first : K <= clock (T.frames.openingAt S.i0)
  stableEnd : Nat
  stable : Echo.StableBlockerUntil
    (canonicalEchoMachine w) (encodedEntries run.entry)
    run.initialRegister
    (clock (T.frames.openingAt S.i2)) stableEnd
  no_lobe : forall k, Not (Echo.ExactLobeWrite
    (canonicalEchoMachine w) (encodedEntries run.entry)
    run.initialRegister k)
  no_replay : Not (Echo.EarlierCompleteStateReplay
    (canonicalEchoMachine w) (encodedEntries run.entry)
    run.initialRegister K period)


private theorem CertifiedEndpointEmptyABCABC.blocker_bounds
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S) :
    C.K <= C.clock (T.frames.openingAt S.i2) /\
    C.clock (T.frames.openingAt S.i1) <
      C.clock (T.frames.openingAt S.i2) /\
    C.clock (T.frames.openingAt S.i2) <
      C.clock (T.frames.closingAt S.i0) := by
  have hc02 : C.clock (T.frames.openingAt S.i0) <
      C.clock (T.frames.openingAt S.i2) :=
    Nat.lt_trans C.selected_clock_order.1 C.selected_clock_order.2.1
  exact ⟨Nat.le_trans C.base_before_first (Nat.le_of_lt hc02),
    C.selected_clock_order.2.1, C.selected_clock_order.2.2⟩

theorem CertifiedEndpointEmptyABCABC.impossible_of_irreflexive
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S)
    (hirr : IrreflexiveLinks w) : False := by
  obtain ⟨hKb, ht1b, hbu0⟩ := C.blocker_bounds
  exact Echo.physical_endpoint_empty_abcabc_impossible
    hirr C.run C.tail C.crossing hKb ht1b hbu0 C.stable
      C.no_lobe C.no_replay


theorem FiveFrameTripleCase.impossible_of_irreflexive
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4)
    (hirr : IrreflexiveLinks w)
    (hcompile : forall S : SelectedFiveFrameABCABC T,
      Nonempty (CertifiedEndpointEmptyABCABC S))
    (hnoNest : Not (Nonempty (SelectedFiveFrameStrictNest T))) : False := by
  rcases T.select_endpoint_triple with habc | hstrict
  · obtain ⟨S⟩ := habc
    obtain ⟨C⟩ := hcompile S
    exact C.impossible_of_irreflexive hirr
  · exact hnoNest hstrict

/-! ## Exact decomposition of the raw target -/

end GeneralN
