import MinimalBABADogbone
import SharpCertificateClosure
import ManufacturedPairTailNovelty

/-!
# The second physical repeat after a raw exact BABA lobe

`MinimalBABADogbone` turns a sparse exact-lobe endpoint into an actual
branch-to-branch track edge and a `ManufacturedFlipReflector`.  This file
starts at the configuration immediately outside that reflector.  A concrete
nonsimple physical suffix then invokes the first-revisit theorem a second
time.  The result is either a tongue-stable simple cycle or an oppositely
oriented manufactured reflector.

The quantitative reduction below does not call arbitrary eventual
periodicity a four-state tail.  It separates the exact alternatives needed
by the sharp argument: a literal four-vector cover when the two actions are
support-compatible, or a concrete passage of the second reflector through
the direct lobe's action switch.  The latter is the contact which the
overlap-minimal BABA accounting must charge.
-/

namespace GeneralN

/-- The actual post-state of a raw productive event is the activated state
of the manufactured direct lobe extracted from an exact sparse lobe write. -/
theorem rawExactLobeWrite_post_is_activated
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start next : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hnext : stepN w (k + 1) start = some next) :
    next.2 = flipAt (tonguesAt w start k) (rawWriterAt w start k) := by
  obtain ⟨cur, produced, C, hC, hcur, hproduced, _hstep,
      _hentry, _hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hproducedEq : produced = next := by
    exact Option.some.inj (hproduced.symm.trans hnext)
  subst produced
  have hcurState : tonguesAt w start k = cur.2 := by
    simp [tonguesAt, hcur]
  rw [hC] at hflip
  simpa [hcurState] using hflip

/-- A canonical branch-to-branch lobe is oriented from the branch selected
in any tongue state to that state's unmatched branch. -/
theorem canonicalDirectLobe_selected_to_unmatched
    {w : Wiring} {C : Nat}
    (hcanonical : w.link (3 * C + 1) = some (3 * C + 2))
    (u : Tongues) :
    w.link (selectedBranch u C) = some (unmatchedBranch u C) := by
  cases hbit : u C with
  | false =>
      simpa [selectedBranch, unmatchedBranch, branchPort, hbit]
        using hcanonical
  | true =>
      have hback := w.symm _ _ hcanonical
      simpa [selectedBranch, unmatchedBranch, branchPort, hbit]
        using hback

/-- Converse transport needed for a static lobe found at the other endpoint
of a last-writer frame.  At any raw productive traversal of that same
canonical branch edge, the sparse overwrite bookkeeping satisfies
`ExactLobeWrite`.  This remains a statement about bookkeeping only; it does
not assert that the sparse sequence is an echo run. -/
theorem canonicalDirectLobe_to_exactLobeWrite
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hcanonical :
      w.link (3 * rawWriterAt w start k + 1) =
        some (3 * rawWriterAt w start k + 2)) :
    Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k := by
  let C := rawWriterAt w start k
  have hC : C < N := rawProductiveAt_writer_lt hN hprod
  have hold :
      Echo.oldSlot (rawOverwriteMachine w) (rawOverwriteEntry w N start)
          (rawOverwriteInitial start) k =
        selectedBranch (tonguesAt w start k) C := by
    simpa [C] using rawOverwrite_oldSlot_eq_selected hN hprod
  have hnew :
      rawOverwriteEntry w N start (k + 1) =
        selectedBranch (tonguesAt w start (k + 1)) C := by
    simp [rawOverwriteEntry, hprod, C]
  have hflip := rawProductiveAt_restricted_flip hN hprod
  have hbit := restrict_eq_apply hflip hC
  have hbit' :
      (tonguesAt w start (k + 1)) C =
        !((tonguesAt w start k) C) := by
    simpa [C, flipAt] using hbit
  have hafter :
      selectedBranch (tonguesAt w start (k + 1)) C =
        unmatchedBranch (tonguesAt w start k) C := by
    unfold selectedBranch unmatchedBranch
    rw [hbit']
  have hcanonicalC : w.link (3 * C + 1) = some (3 * C + 2) := by
    simpa [C] using hcanonical
  have hbranch := canonicalDirectLobe_selected_to_unmatched
    hcanonicalC (tonguesAt w start k)
  have hback := w.symm _ _ hbranch
  have hforwardBar :
      wireBar w (selectedBranch (tonguesAt w start k) C) =
        unmatchedBranch (tonguesAt w start k) C :=
    wireBar_of_link hbranch
  have hbackBar :
      wireBar w (unmatchedBranch (tonguesAt w start k) C) =
        selectedBranch (tonguesAt w start k) C :=
    wireBar_of_link hback
  refine ⟨?_, ?_, ?_⟩
  · rw [hnew, hold]
    change selectedBranch (tonguesAt w start (k + 1)) C =
      wireBar w (selectedBranch (tonguesAt w start k) C)
    exact hafter.trans hforwardBar.symm
  · rw [hnew, hold]
    change selectedBranch (tonguesAt w start k) C =
      wireBar w (selectedBranch (tonguesAt w start (k + 1)) C)
    rw [hafter]
    exact hbackBar.symm
  · rw [hold]
    change wireBar w (selectedBranch (tonguesAt w start k) C) / 3 =
      selectedBranch (tonguesAt w start k) C / 3
    rw [hforwardBar, unmatchedBranch_switch, selectedBranch_switch]

/-- Starting immediately outside the left BABA writer's opening traversal,
the finite suffix through the right frame's close is physically nonsimple:
the right writer occurs at both `second` and `third`.  This is the concrete
second repeat required by the manufactured-reflector theorem. -/
theorem RawBABAInterlacement.post_left_open_suffix_nonsimple
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third) :
    ∃ (next finish : Nat × Tongues) (passages : List Passage),
      stepN w (prior + 1) start = some next ∧
      passages.length = third - prior ∧
      PhysicalTrace w next passages finish ∧
      ¬ SwitchSimple passages := by
  obtain ⟨next, hnext⟩ :=
    Option.isSome_iff_exists.mp B.leftFrame.open_productive.1
  let span := third - prior
  have hspanTime : prior + 1 + span = third + 1 := by
    dsimp [span]
    have hpriorThird := Nat.lt_trans B.prior_lt_second
      (Nat.lt_trans B.second_lt_reroute B.reroute_lt_third)
    omega
  have hglobal : (stepN w (prior + 1 + span) start).isSome := by
    rw [hspanTime]
    exact B.rightFrame.close_productive.1
  obtain ⟨finish, hfinish⟩ :=
    stepN_suffix_some_of_reach hnext hglobal
  obtain ⟨passages, hlength, htrace⟩ :=
    physicalTrace_of_stepN w hfinish
  refine ⟨next, finish, passages, hnext, hlength, htrace, ?_⟩
  intro hsimple
  let dSecond := second - (prior + 1)
  let dThird := third - (prior + 1)
  have hsecondTime : prior + 1 + dSecond = second := by
    dsimp [dSecond]
    have hpriorSecond := B.prior_lt_second
    omega
  have hthirdTime : prior + 1 + dThird = third := by
    dsimp [dThird]
    have hpriorThird := Nat.lt_trans B.prior_lt_second
      (Nat.lt_trans B.second_lt_reroute B.reroute_lt_third)
    omega
  have hsecondGlobal : RawProductiveAt w N start
      (prior + 1 + dSecond) := by
    rw [hsecondTime]
    exact B.rightFrame.open_productive
  have hthirdGlobal : RawProductiveAt w N start
      (prior + 1 + dThird) := by
    rw [hthirdTime]
    exact B.rightFrame.close_productive
  have hsecondLocal : RawProductiveAt w N next dSecond :=
    rawProductiveAt_sub_of_reach hnext hsecondGlobal
  have hthirdLocal : RawProductiveAt w N next dThird :=
    rawProductiveAt_sub_of_reach hnext hthirdGlobal
  obtain ⟨secondPost, hsecondPost⟩ :=
    Option.isSome_iff_exists.mp hsecondLocal.1
  obtain ⟨secondPre, hsecondPre⟩ := stepN_prefix_some
    (d := dSecond) (K := dSecond + 1) (by omega) hsecondPost
  have hsecondLive : (stepN w dSecond next).isSome := by
    simp [hsecondPre]
  obtain ⟨thirdPost, hthirdPost⟩ :=
    Option.isSome_iff_exists.mp hthirdLocal.1
  obtain ⟨thirdPre, hthirdPre⟩ := stepN_prefix_some
    (d := dThird) (K := dThird + 1) (by omega) hthirdPost
  have hthirdLive : (stepN w dThird next).isSome := by
    simp [hthirdPre]
  have hwriterSecond := rawWriterAt_add_of_reach hnext hsecondLive
  rw [hsecondTime] at hwriterSecond
  have hwriterThird := rawWriterAt_add_of_reach hnext hthirdLive
  rw [hthirdTime] at hwriterThird
  have hlocalSame :
      rawWriterAt w next dSecond = rawWriterAt w next dThird := by
    calc
      rawWriterAt w next dSecond = rawWriterAt w start second :=
        hwriterSecond.symm
      _ = rawWriterAt w start third := B.rightFrame.same_writer
      _ = rawWriterAt w next dThird := hwriterThird
  have hSecondThird : dSecond < dThird := by
    dsimp [dSecond, dThird]
    have hpriorSecond := B.prior_lt_second
    have hsecondThird :=
      Nat.lt_trans B.second_lt_reroute B.reroute_lt_third
    omega
  have hThirdSpan : dThird < span := by
    dsimp [dThird, span]
    have hpriorThird := Nat.lt_trans B.prior_lt_second
      (Nat.lt_trans B.second_lt_reroute B.reroute_lt_third)
    omega
  have hThirdLength : dThird < passages.length := by
    rw [hlength]
    exact hThirdSpan
  have hfirst := htrace.rawProductiveAt_first_of_switchSimple
    hsimple hThirdLength hthirdLocal
  exact (hfirst.2 dSecond hSecondThird hsecondLocal) hlocalSame

/-- Starting immediately outside the right BABA writer's opening traversal,
the finite suffix through its own close is physically nonsimple whenever the
right frame is a direct lobe.  The two repeated passages are consecutive at
the close: time `third - 1` faces the lobe stem, and time `third` enters its
unmatched branch.  This is the exact right-hand counterpart of
`post_left_open_suffix_nonsimple`; no geometric symmetry principle is used. -/
theorem RawBABAInterlacement.post_right_open_suffix_nonsimple
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {prior second reroute third : Nat}
    (B : RawBABAInterlacement
      w N start prior second reroute third)
    (hclose : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) third) :
    ∃ (next finish : Nat × Tongues) (passages : List Passage),
      stepN w (second + 1) start = some next ∧
      passages.length = third - second ∧
      PhysicalTrace w next passages finish ∧
      ¬ SwitchSimple passages := by
  obtain ⟨next, hnext⟩ :=
    Option.isSome_iff_exists.mp B.rightFrame.open_productive.1
  let span := third - second
  have hspanTime : second + 1 + span = third + 1 := by
    dsimp [span]
    have hsecondThird :=
      Nat.lt_trans B.second_lt_reroute B.reroute_lt_third
    omega
  have hglobal : (stepN w (second + 1 + span) start).isSome := by
    rw [hspanTime]
    exact B.rightFrame.close_productive.1
  obtain ⟨finish, hfinish⟩ :=
    stepN_suffix_some_of_reach hnext hglobal
  obtain ⟨passages, hlength, htrace⟩ :=
    physicalTrace_of_stepN w hfinish
  refine ⟨next, finish, passages, hnext, hlength, htrace, ?_⟩
  intro hsimple
  have hthirdPos : 0 < third := by
    have hsecondThird :=
      Nat.lt_trans B.second_lt_reroute B.reroute_lt_third
    omega
  obtain ⟨_outside, state, hprevious, _hpost, _hstem⟩ :=
    rawExactLobeWrite_observed_reflection
      hN B.rightFrame.close_productive hclose hthirdPos
  let dPrevious := third - 1 - (second + 1)
  let dThird := third - (second + 1)
  have hgap : second + 1 < third := by
    have hsecondReroute := B.second_lt_reroute
    have hrerouteThird := B.reroute_lt_third
    omega
  have hpreviousTime : second + 1 + dPrevious = third - 1 := by
    dsimp [dPrevious]
    omega
  have hthirdTime : second + 1 + dThird = third := by
    dsimp [dThird]
    omega
  have hpreviousLocal : stepN w dPrevious next =
      some (3 * rawWriterAt w start third, state) := by
    have h := hprevious
    rw [← hpreviousTime, stepN_add, hnext] at h
    exact h
  have hpreviousLive : (stepN w dPrevious next).isSome := by
    rw [hpreviousLocal]
    simp
  have hthirdGlobal : RawProductiveAt w N start
      (second + 1 + dThird) := by
    rw [hthirdTime]
    exact B.rightFrame.close_productive
  have hthirdLocal : RawProductiveAt w N next dThird :=
    rawProductiveAt_sub_of_reach hnext hthirdGlobal
  obtain ⟨thirdPost, hthirdPost⟩ :=
    Option.isSome_iff_exists.mp hthirdLocal.1
  obtain ⟨thirdPre, hthirdPre⟩ := stepN_prefix_some
    (d := dThird) (K := dThird + 1) (by omega) hthirdPost
  have hthirdLive : (stepN w dThird next).isSome := by
    rw [hthirdPre]
    simp
  have hwriterPreviousShift :=
    rawWriterAt_add_of_reach hnext hpreviousLive
  rw [hpreviousTime] at hwriterPreviousShift
  have hwriterThirdShift := rawWriterAt_add_of_reach hnext hthirdLive
  rw [hthirdTime] at hwriterThirdShift
  have hwriterPreviousGlobal :
      rawWriterAt w start (third - 1) = rawWriterAt w start third := by
    simp [rawWriterAt, rawEntryAt, hprevious]
  have hlocalSame :
      rawWriterAt w next dPrevious = rawWriterAt w next dThird := by
    calc
      rawWriterAt w next dPrevious = rawWriterAt w start (third - 1) :=
        hwriterPreviousShift.symm
      _ = rawWriterAt w start third := hwriterPreviousGlobal
      _ = rawWriterAt w next dThird := hwriterThirdShift
  have hPreviousThird : dPrevious < dThird := by
    dsimp [dPrevious, dThird]
    omega
  have hThirdSpan : dThird < span := by
    dsimp [dThird, span]
    omega
  have hPreviousLength : dPrevious < passages.length := by
    rw [hlength]
    exact Nat.lt_trans hPreviousThird hThirdSpan
  have hThirdLength : dThird < passages.length := by
    rw [hlength]
    exact hThirdSpan
  have hwriterPreviousPassage :=
    htrace.rawWriterAt_eq_passageSwitch_getElem hPreviousLength
  have hwriterThirdPassage :=
    htrace.rawWriterAt_eq_passageSwitch_getElem hThirdLength
  have hpair := List.pairwise_iff_getElem.mp hsimple
  have hne := hpair dPrevious dThird
    (by simpa using hPreviousLength)
    (by simpa using hThirdLength) hPreviousThird
  apply hne
  simpa [hwriterPreviousPassage, hwriterThirdPassage] using hlocalSame

/-- Mellit's second-repeat step, anchored to a raw exact-lobe event.

The second reflector really has the opposite endpoints.  In that branch the
proof also records the raw reach back to the first lobe's stem, both groove
certificates in the reached state, and the complete theta theorem's genuine
eventual period. -/
theorem rawExactLobeWrite_second_repeat_cycle_or_pair
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start next finish : Nat × Tongues} {k : Nat}
    {passages : List Passage}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k)
    (hnext : stepN w (k + 1) start = some next)
    (htrace : PhysicalTrace w next passages finish)
    (hnonsimple : ¬ SwitchSimple passages) :
    (∃ atRepeat visited,
        stepN w visited next = some atRepeat ∧
        SettlesOnSimpleCycle w atRepeat) ∨
      (∃ (A : ManufacturedFlipReflector w
            (3 * rawWriterAt w start k) next.1)
          (B : ManufacturedReflector w next.1
            (3 * rawWriterAt w start k))
          (atRepeat : Nat × Tongues) (visited backSteps : Nat),
        next.2 = (ManufacturedReflector.flip A).activatedState ∧
        A.runway = [] ∧ A.candy = [] ∧
        A.actionSwitch = rawWriterAt w start k ∧
        stepN w visited next = some atRepeat ∧
        stepN w (visited + backSteps) next =
          some (3 * rawWriterAt w start k, B.activatedState) ∧
        PathGrooves (ManufacturedReflector.flip A).toSupported.paths
          B.baseState ∧
        PathGrooves B.toSupported.paths B.activatedState ∧
        EventuallyPeriodic w
          (3 * rawWriterAt w start k, B.activatedState)) := by
  obtain ⟨witness, hwitness, hstemWitness⟩ :=
    rawProductiveAt_fixed_stem_successor hN hprod
  have hwitnessEq : witness = next := by
    exact Option.some.inj (hwitness.symm.trans hnext)
  subst witness
  have hbranch := rawExactLobeWrite_selected_to_unmatched hN hprod hlobe
  let A : ManufacturedFlipReflector w
      (3 * rawWriterAt w start k) next.1 :=
    manufacturedFlipReflectorOfSelectedLobe
      (rawWriterAt w start k) next.1 (tonguesAt w start k)
      hbranch hstemWitness
  have hactivated :
      next.2 = (ManufacturedReflector.flip A).activatedState := by
    have hpost := rawExactLobeWrite_post_is_activated hN hprod hnext
    simpa [A, manufacturedFlipReflectorOfSelectedLobe,
      ManufacturedReflector.activatedState] using hpost
  obtain ⟨atRepeat, visited, hvisited, houtcome⟩ :=
    htrace.first_revisit_activated_outcome hnonsimple hstemWitness
  rcases houtcome with hcycle | hreflector
  · exact Or.inl ⟨atRepeat, visited, hvisited, hcycle⟩
  · obtain ⟨B, state, backSteps, hBpaths, hBbase,
        hstate, hback, _hpreserves⟩ := hreflector
    have hreach : stepN w (visited + backSteps) next =
        some (3 * rawWriterAt w start k, B.activatedState) := by
      rw [stepN_add, hvisited]
      simpa [hstate] using hback
    have hAatBase :
        PathGrooves (ManufacturedReflector.flip A).toSupported.paths
          B.baseState := by
      simp [A, manufacturedFlipReflectorOfSelectedLobe,
        ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported, PathGrooves,
        PassagesGrooved]
    have hAatActivated :
        PathGrooves (ManufacturedReflector.flip A).toSupported.paths
          B.activatedState := by
      simp [A, manufacturedFlipReflectorOfSelectedLobe,
        ManufacturedReflector.toSupported,
        ManufacturedFlipReflector.toSupported, PathGrooves,
        PassagesGrooved]
    have hBatActivated :
        PathGrooves B.toSupported.paths B.activatedState := by
      simpa [hstate] using hBpaths
    have hperiodic : EventuallyPeriodic w
        (3 * rawWriterAt w start k, B.activatedState) :=
      manufactured_pair_eventually_periodic
        (.flip A) B B.activatedState hAatActivated hBatActivated
    exact Or.inr ⟨A, B, atRepeat, visited, backSteps,
      hactivated, rfl, rfl, (by
        simp [A, manufacturedFlipReflectorOfSelectedLobe,
          ManufacturedFlipReflector.actionSwitch]), hvisited, hreach,
      hAatBase, hBatActivated, hperiodic⟩

/-- Quantitative form of the second-repeat fork.

In the opposite-reflector branch, every selected time before the reached
pair may be charged to an arbitrary supplied history.  Thereafter either the
two reflectors are support-compatible and the literal budget-four novelty
cover follows, or the second reflector contains a concrete support passage
through the exact writer switch of the direct BABA lobe.  No generic
eventual-periodicity claim is substituted for the four-vector conclusion. -/
theorem rawExactLobeWrite_second_repeat_four_cover_or_contact
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start next finish : Nat × Tongues} {k : Nat}
    {passages : List Passage}
    (hprod : RawProductiveAt w N start k)
    (hlobe : Echo.ExactLobeWrite
      (rawOverwriteMachine w) (rawOverwriteEntry w N start)
      (rawOverwriteInitial start) k)
    (hnext : stepN w (k + 1) start = some next)
    (htrace : PhysicalTrace w next passages finish)
    (hnonsimple : ¬ SwitchSimple passages) :
    (∃ atRepeat visited,
        stepN w visited next = some atRepeat ∧
        SettlesOnSimpleCycle w atRepeat) ∨
      (∃ (A : ManufacturedFlipReflector w
            (3 * rawWriterAt w start k) next.1)
          (B : ManufacturedReflector w next.1
            (3 * rawWriterAt w start k))
          (K : Nat),
        stepN w K start =
          some (3 * rawWriterAt w start k, B.activatedState) ∧
        A.runway = [] ∧ A.candy = [] ∧
        A.actionSwitch = rawWriterAt w start k ∧
        ∀ (times : List Nat) (history : List (List Bool)),
          (∀ j ∈ times, j < K →
            restrictedTonguesAt w N start j ∈ history) →
          FourNoveltyCover w N start times history ∨
            ∃ path ∈ B.toSupported.paths, ∃ passage ∈ path,
              passageSwitch passage = rawWriterAt w start k) := by
  rcases rawExactLobeWrite_second_repeat_cycle_or_pair
      hN hprod hlobe hnext htrace hnonsimple with hcycle | hpair
  · exact Or.inl hcycle
  · obtain ⟨A, B, atRepeat, visited, backSteps,
        _hactivated, hArunway, hAcandy, hAaction,
        hvisited, hlocalReach, _hAatBase, hBatActivated,
        _hperiodic⟩ := hpair
    let K := k + 1 + (visited + backSteps)
    have hreach : stepN w K start =
        some (3 * rawWriterAt w start k, B.activatedState) := by
      dsimp [K]
      rw [stepN_add, hnext]
      exact hlocalReach
    refine Or.inr ⟨A, B, K, hreach, hArunway, hAcandy,
      hAaction, ?_⟩
    intro times history hhistory
    have hAatActivated :
        PathGrooves (ManufacturedReflector.flip A).toSupported.paths
          B.activatedState := by
      change PathGrooves [A.runway, A.candy] B.activatedState
      rw [hArunway, hAcandy]
      simp [PathGrooves, PassagesGrooved]
    have hBA : B.toSupported.action.Avoids
        (ManufacturedReflector.flip A).toSupported.paths := by
      change B.toSupported.action.Avoids [A.runway, A.candy]
      rw [hArunway, hAcandy]
      cases B.toSupported.action <;> simp [LocalAction.Avoids]
    by_cases hAB :
        (ManufacturedReflector.flip A).toSupported.action.Avoids
          B.toSupported.paths
    · exact Or.inl
        (manufactured_pair_history_and_tail_four_novelty_cover
          (ManufacturedReflector.flip A) B B.activatedState
          hAatActivated hBatActivated hAB hBA hreach
          times history hhistory)
    · have hnot : ¬ (LocalAction.flip A.actionSwitch).Avoids
          B.toSupported.paths := by
        simpa [ManufacturedReflector.toSupported,
          ManufacturedFlipReflector.toSupported] using hAB
      obtain ⟨path, hpath, passage, hpassage, hcontact⟩ :=
        contact_of_not_avoids_flip hnot
      exact Or.inr ⟨path, hpath, passage, hpassage, by
        simpa [hAaction] using hcontact⟩

end GeneralN
