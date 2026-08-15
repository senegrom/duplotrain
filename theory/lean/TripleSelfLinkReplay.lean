import TripleFramePhysicalClosure

/-!
# The self-linked escape in the five-frame obstruction

The abstract triple obstruction can end at a fixed `bar` entry.  For the
canonical raw-track compiler this is an external branch linked to itself.
This file records the exact raw consequence: the selected switch makes a
two-passage identity bounce, and any switch-simple runway leading to it is
retraced completely without changing a tongue.

The final section isolates the remaining global control-flow obligation.  It
does not assume link irreflexivity and it does not call the local bounce a
global replay.  The missing extraction must place the encountered bounce in
the raw five-frame history and return either the already-forbidden complete
echo replay or the existing `RunwayTailBeforeSecond` novelty certificate.
-/

namespace GeneralN

/-! ## Exact raw semantics of a self-linked selected branch -/


structure SelfLinkPairTailBeforeSecond
    (w : Wiring) (N : Nat) (start : Prod Nat Tongues)
    (second : Nat) where
  g : Nat
  e : Nat
  A : ManufacturedFlipReflector w g e
  R : ManufacturedStayReflector w e g
  state : Tongues
  shift : Nat
  reached : stepN w shift start = some (g, state)
  live : forall d, exists finish,
    stepN w d (g, state) = some finish
  groovesA : PathGrooves
    (ManufacturedReflector.flip A).toSupported.paths state
  groovesR : PathGrooves
    (ManufacturedReflector.stay R).toSupported.paths state
  compatible : (ManufacturedReflector.flip A).toSupported.action.Avoids
    (ManufacturedReflector.stay R).toSupported.paths
  reached_before_second : shift <= second + 1

def CertifiedSelfLinkReplayOrTail
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (F : FiveFixedStemNovelFrames w N start)
    (C : CertifiedEndpointEmptyABCABC S) : Prop :=
  Echo.EarlierCompleteStateReplay
      (canonicalEchoMachine w) (encodedEntries C.run.entry)
      C.run.initialRegister C.K C.period \/
    Nonempty (RunwayTailBeforeSecond w N start F.z₁) \/
    Nonempty (SelfLinkPairTailBeforeSecond w N start F.z₁)

def KnownEdgeABCABCSelfLinkReplayOrTailClosure : Prop :=
  forall (w : Wiring) (N e : Nat),
    (forall p q, w.link p = some q -> p < 3 * N /\ q < 3 * N) ->
    forall (start : Prod Nat Tongues),
      w.link e = some start.1 ->
      forall F : FiveFixedStemNovelFrames w N start,
        forall T : FiveFrameTripleCase w N start
          F.z₀ F.z₁ F.z₂ F.z₃ F.z₄,
          forall S : SelectedFiveFrameABCABC T,
            forall C : CertifiedEndpointEmptyABCABC S,
              CertifiedRunUsesSelfLink C.run ->
              CertifiedSelfLinkReplayOrTail F C

end GeneralN
