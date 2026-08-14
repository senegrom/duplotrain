import SharpCertificateClosure

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
  shape : EndpointABCABC
    (T.frames.openingAt i0) (T.frames.closingAt i0)
    (T.frames.openingAt i1) (T.frames.closingAt i1)
    (T.frames.openingAt i2) (T.frames.closingAt i2)

/-- One concrete decreasing-opening triple selected from a grouped strict
nest outcome. -/
structure SelectedFiveFrameStrictNest
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4) : Type where
  i0 : Fin 5
  i1 : Fin 5
  i2 : Fin 5
  shape : EndpointStrictNest
    (T.frames.openingAt i0) (T.frames.closingAt i0)
    (T.frames.openingAt i1) (T.frames.closingAt i1)
    (T.frames.openingAt i2) (T.frames.closingAt i2)

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
    · exact Or.inl <| Nonempty.intro {
        i0 := 0, i1 := 1, i2 := 2
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 0, i1 := 1, i2 := 3
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 0, i1 := 1, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 0, i1 := 2, i2 := 3
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 0, i1 := 2, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 0, i1 := 3, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 1, i1 := 2, i2 := 3
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 1, i1 := 2, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 1, i1 := 3, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inl <| Nonempty.intro {
        i0 := 2, i1 := 3, i2 := 4
        shape := by
          simpa using h }
  · rcases hnest with h | h | h | h | h | h | h | h | h | h
    · exact Or.inr <| Nonempty.intro {
        i0 := 0, i1 := 1, i2 := 2
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 0, i1 := 1, i2 := 3
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 0, i1 := 1, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 0, i1 := 2, i2 := 3
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 0, i1 := 2, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 0, i1 := 3, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 1, i1 := 2, i2 := 3
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 1, i1 := 2, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 1, i1 := 3, i2 := 4
        shape := by
          simpa using h }
    · exact Or.inr <| Nonempty.intro {
        i0 := 2, i1 := 3, i2 := 4
        shape := by
          simpa using h }

/-! ## The exact raw-to-certified `ABCABC` interface -/

/-- A self-link at an entry genuinely used by a certified concrete run.  This
is deliberately stronger and more local than merely saying that the wiring
contains some irrelevant self-link. -/
def CertifiedRunUsesSelfLink {w : Wiring}
    (run : CertifiedConcreteEchoRun w) : Prop :=
  exists q, w.link (run.entry q) = some (run.entry q)

/-- An encountered self-link in a certified run is not an unrelated wiring
defect: its realised descent supplies the stem successor, so the selected
branch is exactly a two-step identity reflector. -/
theorem certified_used_self_link_has_identity_reflector
    {w : Wiring} {run : CertifiedConcreteEchoRun w}
    (huse : CertifiedRunUsesSelfLink run) :
    exists q outside,
      w.link (run.entry q) = some (run.entry q) ∧
      IsReflector w (3 * (run.entry q / 3)) outside 2
        (fun state => state (run.entry q / 3) = bval (run.entry q))
        (fun state => state) := by
  obtain ⟨q, hself⟩ := huse
  have hslot := run.toConcreteAscentTrace.freeSlot q
  rcases hslot.1 with ⟨t, ps, landing, t', hd⟩
  cases hd with
  | last hbranch hmouth _ =>
      exact ⟨q, landing, hself,
        self_linked_branch_is_identity_reflector
          hbranch hself hmouth⟩
  | @cons _ p next landing tail _ hbranch hmouth _ _ =>
      exact ⟨q, next, hself,
        self_linked_branch_is_identity_reflector
          hbranch hself hmouth⟩

/-- One selected raw productive time is represented by the corresponding
certified ascent time, both at the physical entry port and at the incoming
tongue boundary. -/
def CertifiedRepresentsRawTime {w : Wiring}
    (run : CertifiedConcreteEchoRun w) (clock : Nat -> Nat)
    (start : Nat × Tongues) (k : Nat) : Prop :=
  run.entry (clock k) = rawEntryAt w start k ∧
    run.boundary (clock k) = tonguesAt w start k

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
  represents_open0 : CertifiedRepresentsRawTime run clock start
    (T.frames.openingAt S.i0)
  represents_close0 : CertifiedRepresentsRawTime run clock start
    (T.frames.closingAt S.i0)
  represents_open1 : CertifiedRepresentsRawTime run clock start
    (T.frames.openingAt S.i1)
  represents_close1 : CertifiedRepresentsRawTime run clock start
    (T.frames.closingAt S.i1)
  represents_open2 : CertifiedRepresentsRawTime run clock start
    (T.frames.openingAt S.i2)
  represents_close2 : CertifiedRepresentsRawTime run clock start
    (T.frames.closingAt S.i2)
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

/-- The exact third escape branch returned by the abstract physical
obstruction for this certificate. -/
def CertifiedEndpointEmptyABCABC.HasFixedEscape
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S) : Prop :=
  exists q,
    (canonicalEchoMachine w).bar (encodedEntries C.run.entry q) =
      encodedEntries C.run.entry q

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

/-- After the certificate has excluded the lobe and complete-replay branches,
the abstract obstruction leaves exactly a fixed canonical entry. -/
theorem CertifiedEndpointEmptyABCABC.forces_fixed_escape
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S) : C.HasFixedEscape := by
  obtain ⟨hKb, ht1b, hbu0⟩ := C.blocker_bounds
  have hout := Echo.cyclic_minimal_stable_blocker_obstruction
    (canonicalEchoMachine w) (encodedEntries C.run.entry)
    C.run.initialRegister
    (certifiedConcreteEcho_isRun C.run) C.run.initialWellFormed
    C.tail C.crossing hKb ht1b hbu0 C.stable
  rcases hout with hlobe | hreplay | hfixed
  · obtain ⟨k, hk⟩ := hlobe
    exact (C.no_lobe k hk).elim
  · exact (C.no_replay hreplay).elim
  · exact hfixed

/-- The desired direct bridge to
`TripleInterlacementObstruction.physical_endpoint_empty_abcabc_impossible`.
Once the selected raw triple has the certified data above, physical
irreflexivity closes it. -/
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

/-- A fixed canonical jump at a concrete encoded entry is the self-link at
that very entry, not merely an unspecified self-link elsewhere in the wiring. -/
theorem certified_fixed_encoded_entry_has_self_link
    {w : Wiring} (run : CertifiedConcreteEchoRun w) {q : Nat}
    (hfixed :
      (canonicalEchoMachine w).bar (encodedEntries run.entry q) =
        encodedEntries run.entry q) :
    w.link (run.entry q) = some (run.entry q) := by
  have hencoded : encodeSlot (wireBar w (run.entry q)) =
      encodeSlot (run.entry q) := by
    simpa [encodedEntries, canonicalEchoMachine, encodedMachine,
      encodedBar_encodeSlot] using hfixed
  have hwire : wireBar w (run.entry q) = run.entry q :=
    encodeSlot_injective hencoded
  have hslot := run.toConcreteAscentTrace.freeSlot q
  have hlink : w.link (run.entry q) =
      some (wireBar w (run.entry q)) := hslot.2.2.1
  rwa [hwire] at hlink

/-- Conversely, a self-link at a certified entry fixes its encoded canonical
jump. -/
theorem certified_self_linked_entry_has_fixed_bar
    {w : Wiring} (run : CertifiedConcreteEchoRun w) {q : Nat}
    (hself : w.link (run.entry q) = some (run.entry q)) :
    (canonicalEchoMachine w).bar (encodedEntries run.entry q) =
      encodedEntries run.entry q := by
  have hslot := run.toConcreteAscentTrace.freeSlot q
  have hlink : w.link (run.entry q) =
      some (wireBar w (run.entry q)) := hslot.2.2.1
  rw [hself] at hlink
  have hwire : wireBar w (run.entry q) = run.entry q := by
    injection hlink with h
    exact h.symm
  simp [encodedEntries, canonicalEchoMachine, encodedMachine,
    encodedBar_encodeSlot, hwire]

/-- Honest non-irreflexive form of the physical closure.  If lobe and replay
escapes are absent, an `ABCABC` certificate forces a self-link actually
encountered by its certified run. -/
theorem CertifiedEndpointEmptyABCABC.forces_used_self_link
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S) :
    CertifiedRunUsesSelfLink C.run := by
  obtain ⟨q, hq⟩ := C.forces_fixed_escape
  exact ⟨q, certified_fixed_encoded_entry_has_self_link C.run hq⟩


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
