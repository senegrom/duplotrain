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

/-- A selected self-linked branch is literally the two recorded passages
`stem -> branch -> stem`, after which the immutable stem edge leads to
`outside`.  The full tongue vector is unchanged. -/
theorem self_link_exact_two_passage_trace
    {w : Wiring} {branch outside : Nat} {state : Tongues}
    (hbranch : branch % 3 ≠ 0)
    (hself : w.link branch = some branch)
    (hmouth : w.link (3 * (branch / 3)) = some outside)
    (hselected : state (branch / 3) = bval branch) :
    PhysicalTrace w (3 * (branch / 3), state)
      [(3 * (branch / 3), branch),
       (branch, 3 * (branch / 3))]
      (outside, state) := by
  have hstemMod : (3 * (branch / 3)) % 3 = 0 := by omega
  have hstemDiv : (3 * (branch / 3)) / 3 = branch / 3 := by omega
  have hforward :
      arrive state (3 * (branch / 3)) = (branch, state) := by
    simp [arrive, hstemMod, hstemDiv, hselected,
      branchPort_bval hbranch]
  have hpin : pin state branch = state := pin_of_agrees hselected
  have hback :
      arrive state branch = (3 * (branch / 3), state) := by
    simp [arrive, hbranch, hpin]
  exact PhysicalTrace.cons hforward hself
    (PhysicalTrace.cons hback hmouth (PhysicalTrace.nil _))

theorem self_link_core_stay_reflector
    {w : Wiring} {branch outside : Nat} {state : Tongues}
    (hbranch : branch % 3 ≠ 0)
    (hself : w.link branch = some branch)
    (hmouth : w.link (3 * (branch / 3)) = some outside)
    (hselected : state (branch / 3) = bval branch) :
    Nonempty (ManufacturedStayReflector w
      (3 * (branch / 3)) outside) := by
  have hstemMod : (3 * (branch / 3)) % 3 = 0 := by omega
  have hstemDiv : (3 * (branch / 3)) / 3 = branch / 3 := by omega
  have hforward :
      arrive state (3 * (branch / 3)) = (branch, state) := by
    simp [arrive, hstemMod, hstemDiv, hselected,
      branchPort_bval hbranch]
  have hentry : w.link outside = some (3 * (branch / 3)) :=
    w.symm _ _ hmouth
  let R : ManufacturedStayReflector w
      (3 * (branch / 3)) outside := {
    base := state
    mouthState := state
    returnState := state
    runway := []
    mouth := 3 * (branch / 3)
    arm := branch
    runwayTrace := PhysicalTrace.nil _
    coreTrace := PhysicalTrace.cons hforward hself (PhysicalTrace.nil _)
    simple := by simp [SwitchSimple, passageSwitch]
    stemEndpoint := Or.inl (by omega)
    selfLink := hself
    entryEdge := hentry
  }
  exact Nonempty.intro R

theorem flip_then_self_link_all_time_two_phase_tongues
    {w : Wiring} {g e : Nat}
    (A : ManufacturedFlipReflector w g e)
    (R : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hA : PathGrooves (ManufacturedReflector.flip A).toSupported.paths state)
    (hR : PathGrooves (ManufacturedReflector.stay R).toSupported.paths state)
    (hAR : (ManufacturedReflector.flip A).toSupported.action.Avoids
      (ManufacturedReflector.stay R).toSupported.paths)
    (d : Nat) :
    tonguesAt w (g, state) d ∈
      [state, flipAt state A.actionSwitch] := by
  have hfour := manufactured_pair_all_time_four_phase_tongues
    (ManufacturedReflector.flip A) (ManufacturedReflector.stay R)
      state hA hR hAR (by trivial) d
  simp [ManufacturedReflector.toSupported,
    ManufacturedFlipReflector.toSupported,
    ManufacturedStayReflector.toSupported,
    LocalAction.apply] at hfour
  rcases hfour with hstate | hflip | hrestore
  · simp [hstate]
  · simp [hflip]
  · rw [flipAt_flipAt] at hrestore
    simp [hrestore]

/-- Consequently every sample of the compatible flip/self-link tail has a
two-vector novelty cover over any supplied history. -/
theorem flip_then_self_link_two_novelty_cover
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedFlipReflector w g e)
    (R : ManufacturedStayReflector w e g)
    (state : Tongues)
    (hA : PathGrooves (ManufacturedReflector.flip A).toSupported.paths state)
    (hR : PathGrooves (ManufacturedReflector.stay R).toSupported.paths state)
    (hAR : (ManufacturedReflector.flip A).toSupported.action.Avoids
      (ManufacturedReflector.stay R).toSupported.paths)
    (times : List Nat) (history : List (List Bool)) :
    NoveltyCoverOn w N (g, state) times history 2 := by
  let fresh :=
    [VectorCount.restrict N state,
     VectorCount.restrict N (flipAt state A.actionSwitch)]
  refine ⟨fresh, by simp [fresh], ?_⟩
  intro d _hd
  have hphase := flip_then_self_link_all_time_two_phase_tongues
    A R state hA hR hAR d
  simp at hphase
  apply List.mem_append_right history
  rcases hphase with hstate | hflip
  · simp [fresh, restrictedTonguesAt, hstate]
  · simp [fresh, restrictedTonguesAt, hflip]

/-- A compatible flip/self-link pair reached no later than the second closing
frame.  This is the exact periodic-tail certificate naturally produced when
the global repair construction meets the encountered self-link. -/
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

/-- Four chronological global novelties cannot occur after a compatible
flip/self-link pair has been reached: the entire raw tail has only two tongue
vectors. -/
theorem no_five_fixed_stem_novelties_of_self_link_pair_tail
    {w : Wiring} {N : Nat} {start : Prod Nat Tongues}
    (F : FiveFixedStemNovelFrames w N start)
    (P : SelfLinkPairTailBeforeSecond w N start F.z₁) : False := by
  let localStart : Prod Nat Tongues := (P.g, P.state)
  let localTimes :=
    [F.z₁ + 1 - P.shift,
     F.z₂ + 1 - P.shift,
     F.z₃ + 1 - P.shift,
     F.z₄ + 1 - P.shift]
  have hcover : NoveltyCoverOn w N localStart localTimes [] 2 := by
    dsimp [localStart]
    exact flip_then_self_link_two_novelty_cover
      P.A P.R P.state P.groovesA P.groovesR P.compatible
        localTimes []
  have hz₁₂ : F.z₁ < F.z₂ := F.order₁₂
  have hz₂₃ : F.z₂ < F.z₃ := F.order₂₃
  have hz₃₄ : F.z₃ < F.z₄ := F.order₃₄
  have hshiftLe₁ : P.shift <= F.z₁ + 1 := P.reached_before_second
  have hshiftLe₂ : P.shift <= F.z₂ + 1 := by omega
  have hshiftLe₃ : P.shift <= F.z₃ + 1 := by omega
  have hshiftLe₄ : P.shift <= F.z₄ + 1 := by omega
  have hv₁ : restrictedTonguesAt w N localStart
      (F.z₁ + 1 - P.shift) =
      restrictedTonguesAt w N start (F.z₁ + 1) := by
    obtain ⟨finish, hfinish⟩ := P.live (F.z₁ + 1 - P.shift)
    have h := restrictedTonguesAt_add_of_reach
      (N := N) (d := F.z₁ + 1 - P.shift) P.reached hfinish
    dsimp [localStart]
    rw [← h]
    congr 1
    omega
  have hv₂ : restrictedTonguesAt w N localStart
      (F.z₂ + 1 - P.shift) =
      restrictedTonguesAt w N start (F.z₂ + 1) := by
    obtain ⟨finish, hfinish⟩ := P.live (F.z₂ + 1 - P.shift)
    have h := restrictedTonguesAt_add_of_reach
      (N := N) (d := F.z₂ + 1 - P.shift) P.reached hfinish
    dsimp [localStart]
    rw [← h]
    congr 1
    omega
  have hv₃ : restrictedTonguesAt w N localStart
      (F.z₃ + 1 - P.shift) =
      restrictedTonguesAt w N start (F.z₃ + 1) := by
    obtain ⟨finish, hfinish⟩ := P.live (F.z₃ + 1 - P.shift)
    have h := restrictedTonguesAt_add_of_reach
      (N := N) (d := F.z₃ + 1 - P.shift) P.reached hfinish
    dsimp [localStart]
    rw [← h]
    congr 1
    omega
  have hv₄ : restrictedTonguesAt w N localStart
      (F.z₄ + 1 - P.shift) =
      restrictedTonguesAt w N start (F.z₄ + 1) := by
    obtain ⟨finish, hfinish⟩ := P.live (F.z₄ + 1 - P.shift)
    have h := restrictedTonguesAt_add_of_reach
      (N := N) (d := F.z₄ + 1 - P.shift) P.reached hfinish
    dsimp [localStart]
    rw [← h]
    congr 1
    omega
  have hglobalNodup := four_raw_novel_post_vectors_nodup
    F.order₁₂ F.order₂₃ F.order₃₄
    F.event₁.2.2 F.event₂.2.2 F.event₃.2.2 F.event₄.2.2
  have hlocalNodup :
      (localTimes.map (restrictedTonguesAt w N localStart)).Nodup := by
    simpa [localTimes, hv₁, hv₂, hv₃, hv₄] using hglobalNodup
  have hcount := noveltyCoverOn_distinct_count hcover hlocalNodup
  have hlength : localTimes.length = 4 := by simp [localTimes]
  have hle : localTimes.length <= 2 := by simpa using hcount
  rw [hlength] at hle
  omega

/-! ## The remaining raw five-frame control-flow interface -/

/-- Resolution data sufficient to eliminate the encountered self-link in one
selected five-frame certificate.  The replay branch contradicts the
certificate's `no_replay` field; the runway branch contradicts the four later
globally novel states by `no_five_fixed_stem_novelties_of_runway_tail`.

This proposition deliberately contains the unresolved placement step.  The
unconditional theorems above produce the physical identity reflector, but the
current certified clock does not state where its witness lies in the raw
five-frame timeline. -/
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
