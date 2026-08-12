import KnownEdgeNAddFiveAlt
import KnownEdgeNAddFourChangedClosed
import BoundaryAbsentSecondWriter
import RepeatedNoveltyDecomposition
import TrackNovelReplay
import GlobalSerialContinuation
import ReuseForcesReplayClosure

/-!
# The protected-pair `N+4` frontier

The protected two-reflector branch currently uses a construction-history
cover of size `N+3` and two fresh repair-tail vectors.  This file isolates a
second history overlap.  If the first reflector's omitted facing mouth is
the first productive writer of the second construction, its post-write
vector is the first reflector's pre-return vector.  Erasing that duplicate
gives an `N+2` construction cover.

The final theorem is unconditional.  It says that either such an `N+2`
cover exists, or the first reflector is a flip reflector whose facing mouth
is productively written by the second construction only after an earlier
productive event.  The latter is the precise remaining history-side
residual for the protected-pair `N+4` attack.
-/

namespace GeneralN

/-- A switch-simple trace cannot return to its literal starting port and
then continue.  The passage at time zero and the passage at the return time
would have the same writer switch, contradicting switch simplicity. -/
private theorem protectedPair_no_strict_return_to_start_port
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    {k : Nat} {returned : Tongues}
    (hpositive : 0 < k)
    (hinside : k < passages.length)
    (hreturn : stepN w k start = some (start.1, returned)) : False := by
  have hzero :=
    htrace.rawWriterAt_eq_passageSwitch_getElem
      (k := 0) (by omega)
  have hreturned :=
    htrace.rawWriterAt_eq_passageSwitch_getElem
      (k := k) hinside
  have hwriters :
      rawWriterAt w start 0 = rawWriterAt w start k := by
    simp [rawWriterAt, rawEntryAt, stepN, hreturn]
  have hpair := List.pairwise_iff_getElem.mp hsimple
  have hne := hpair 0 k
    (by simpa using (show 0 < passages.length by omega))
    (by simpa using hinside) hpositive
  apply hne
  simpa [hzero, hreturned] using hwriters

/-- The pre-return vector is retained by a reflector's compressed sharp
history. -/
theorem ManufacturedReflector.preReturn_mem_sharpHistoryCore
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e) :
    VectorCount.restrict N A.preReturn.2 ∈ A.sharpHistoryCore N := by
  apply A.mem_sharpHistoryCore_of_mem
  unfold ManufacturedReflector.sharpConstructionHistory
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨A.exploration.length, List.mem_range.mpr (by omega), ?_⟩
  have hreach := A.exploration_trace.sound
  simp [restrictedTonguesAt, tonguesAt, hreach]

/-- The facing mouth coordinate of a flip reflector is not part of its
reusable support. -/
private theorem ManufacturedFlipReflector.action_not_mem_reusable
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e) :
    R.actionSwitch ∉ (ManufacturedReflector.flip R).reusableSwitches := by
  intro hmem
  change R.actionSwitch ∈
    ((R.runway ++ R.candy).map passageSwitch) at hmem
  obtain ⟨passage, hpassage, hswitch⟩ := List.mem_map.mp hmem
  rcases List.mem_append.mp hpassage with hrunway | hcandy
  · exact (R.support_foreign R.runway (by simp)
      passage hrunway) hswitch
  · exact (R.support_foreign R.candy (by simp)
      passage hcandy) hswitch

/-- The omitted facing mouth is nevertheless one of the represented
coordinates. -/
private theorem ManufacturedFlipReflector.action_lt
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e) :
    R.actionSwitch < N := by
  have hlt :=
    (ManufacturedReflector.flip R).exploration_trace.switch_lt
      hN (R.mouth, R.firstArm) (by
        simp [ManufacturedReflector.exploration])
  simpa [passageSwitch, ManufacturedFlipReflector.actionSwitch] using hlt

/-- A productive write of the old flip reflector's action switch is the
last productive event of the second switch-simple exploration.

Entering that action branch exits through the old mouth.  Because the old
support is grooved at both endpoints of the second exploration, no later
productive event can have damaged an old runway coordinate; hence the
runway is still grooved immediately after the action write.  The train must
therefore retrace the runway pointwise to the literal start port `e`.
Switch simplicity forces the second exploration to end no later than that
return, while a productive event strictly after the action write would have
to lie at or beyond the end of the pointwise retrace. -/
theorem ManufacturedFlipReflector.action_writer_is_last_productive
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch) :
    ∀ j, t < j → j < B.exploration.length →
      ¬ RawProductiveAt w N (e, B.baseState) j := by
  intro j htj hjBound hjProd
  let start : Nat × Tongues := (e, B.baseState)
  have htData := mem_rawFirstWriterTimes_iff.mp ht
  have hactionProd : RawProductiveAt w N start t := by
    simpa [start] using htData.2.1
  obtain ⟨cur, next, writerSwitch, hwriterDef, hcur, hnext,
      hstep, _hentry, hexit, _hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hactionProd
  have hwriterSwitch : writerSwitch = R.actionSwitch := by
    exact hwriterDef.trans (by simpa [start] using hwriter)
  subst writerSwitch
  have hmouth : 3 * R.actionSwitch = R.mouth := by
    unfold ManufacturedFlipReflector.actionSwitch
    have hstem := R.mouth_is_stem
    omega
  have hparts := step_some_parts hstep
  have hactionArrive :
      arrive cur.2 cur.1 = (R.mouth, next.2) := by
    calc
      arrive cur.2 cur.1 = (exitPort cur, next.2) := by
        apply Prod.ext
        · rfl
        · exact hparts.2.symm
      _ = (R.mouth, next.2) := by
        rw [hexit, hwriterSwitch, hmouth]
  let endpointSpan := B.exploration.length - (t + 1)
  have hendpointSum :
      t + 1 + endpointSpan = B.exploration.length := by
    dsimp [endpointSpan]
    omega
  have hendpointReach :
      stepN w (t + 1 + endpointSpan) start = some B.preReturn := by
    rw [hendpointSum]
    simpa [start] using B.exploration_trace.sound
  have hpostRunwayGrooved : PassagesGrooved next.2 R.runway := by
    intro passage hpassage
    have hendpointGroove :
        arrive B.preReturn.2 passage.2 =
          (passage.1, B.preReturn.2) :=
      hpreGrooves R.runway (by
        change R.runway ∈ [R.runway, R.candy]
        exact List.mem_cons_self) passage hpassage
    have hexitSwitch :
        passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch B.preReturn.2 passage.2
      rw [hendpointGroove] at hs
      simpa [passageSwitch] using hs.symm
    have hmemReusable : passageSwitch passage ∈
        (ManufacturedReflector.flip R).reusableSwitches := by
      change passageSwitch passage ∈
        (R.runway ++ R.candy).map passageSwitch
      apply List.mem_map.mpr
      exact ⟨passage, List.mem_append_left _ hpassage, rfl⟩
    have hswitchLt : passageSwitch passage < N :=
      (ManufacturedReflector.flip R).reusableSwitch_lt hN hmemReusable
    have hbit :
        next.2 (passageSwitch passage) =
          B.preReturn.2 (passageSwitch passage) := by
      apply Classical.byContradiction
      intro hne
      have hendpointNe :
          B.preReturn.2 (passageSwitch passage) ≠
            next.2 (passageSwitch passage) := by
        intro heq
        exact hne heq.symm
      have hchange :
          (tonguesAt w start (t + 1 + endpointSpan))
              (passageSwitch passage) ≠
            (tonguesAt w start (t + 1))
              (passageSwitch passage) := by
        simpa [tonguesAt, hendpointReach, hnext] using hendpointNe
      obtain ⟨later, hlaterLeft, hlaterRight,
          hlaterProd, hlaterWriter⟩ :=
        changed_coordinate_has_writer_between
          hswitchLt hendpointReach hchange
      have hlaterBound : later < B.exploration.length := by
        rw [hendpointSum] at hlaterRight
        exact hlaterRight
      have hnotReusable :=
        PhysicalTrace.productive_writer_not_reusable_of_endpoint_grooves
          hN (ManufacturedReflector.flip R) B.exploration_trace
          B.exploration_simple hbaseGrooves hpreGrooves
          hlaterBound hlaterProd
      apply hnotReusable
      rw [hlaterWriter]
      exact hmemReusable
    apply groove_transfer hendpointGroove
    rw [hexitSwitch]
    exact hbit
  have hpointwise :=
    (physicalTrace_contact_retraces_prefix_pointwise
      R.runwayTrace hpostRunwayGrooved R.entryEdge hactionArrive).2
  have hbackTrace := physicalTrace_contact_retraces_prefix
    R.runwayTrace hpostRunwayGrooved R.entryEdge hactionArrive
  let runwaySpan := R.runway.length + 1
  have hbackSound :
      stepN w runwaySpan (cur.1, cur.2) = some (e, next.2) := by
    simpa [runwaySpan, reversePassages_length, Nat.add_comm] using
      hbackTrace.sound
  let returnTime := t + runwaySpan
  have hreturn :
      stepN w returnTime start = some (e, next.2) := by
    dsimp [returnTime]
    rw [stepN_add, hcur]
    exact hbackSound
  have hexplorationByReturn : B.exploration.length ≤ returnTime := by
    apply Nat.le_of_not_gt
    intro hinside
    exact protectedPair_no_strict_return_to_start_port
      B.exploration_trace B.exploration_simple
        (k := returnTime) (returned := next.2)
        (by dsimp [returnTime, runwaySpan]; omega)
        hinside (by simpa [start] using hreturn)
  have hjOutside := productive_not_inside_pointwise_retrace
    (N := N) (repeatTime := t) (span := runwaySpan)
    (openTime := j) (start := start)
    (old := cur.2) (settled := next.2) (q := cur.1)
    hcur (by simpa [runwaySpan] using hpointwise)
    (by simpa [start] using hjProd) htj
  dsimp [returnTime] at hexplorationByReturn
  omega

/-- Every support-preserving protected repair prefix ends in either the
protected reflector's activated state or its pre-return state.  For a flip
reflector these are the two values of its action tongue; for a stay
reflector the core groove rules out even that one-coordinate difference. -/
theorem ManufacturedReflector.repair_prefix_contact_eq_activated_or_preReturn
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {approach : List Passage} {finishPort : Nat} {contact : Tongues}
    (hprefix : PhysicalTrace w (g, B.activatedState) approach
      (finishPort, contact))
    (hsimple : SwitchSimple approach)
    (hroute : ∀ passage ∈ approach,
      passage ∈ A.orientedRoute B.activatedState)
    (hBcontact : PathGrooves B.toSupported.paths contact) :
    contact = B.activatedState ∨ contact = B.preReturn.2 := by
  have hchanges := A.repair_prefix_changes_only_protected_return
    B hA hBstart hprefix hsimple hroute hBcontact
  cases B with
  | stay R =>
      change contact = R.returnState ∨ contact = R.returnState
      have hchanges' : ∀ j, contact j ≠ R.returnState j →
          j = R.arm / 3 := by
        intro j hj
        have h := hchanges j (by
          change contact j ≠ R.returnState j
          exact hj)
        change j = R.arm / 3 at h
        exact h
      have hrelation :
          R.returnState = contact ∨
            R.returnState = flipAt contact (R.arm / 3) :=
        tongues_eq_or_eq_flipAt_of_changes_only
          (u := R.returnState) (v := contact)
          (k := R.arm / 3) hchanges'
      rcases hrelation with heq | hflip
      · exact Or.inl heq.symm
      · have hcoreStart : arrive R.returnState R.arm =
            (R.mouth, R.returnState) :=
          passagesGrooved_singleton.mp (pathGrooves_pair.mp hBstart).2
        have hcoreContact : arrive contact R.arm =
            (R.mouth, contact) :=
          passagesGrooved_singleton.mp (pathGrooves_pair.mp hBcontact).2
        have hkeyAgree :
            R.returnState (R.arm / 3) = contact (R.arm / 3) :=
          grooved_states_agree_on_passage hcoreStart hcoreContact
        have hk := congrFun hflip (R.arm / 3)
        rw [hkeyAgree] at hk
        cases hval : contact (R.arm / 3) <;>
          simp [flipAt, hval] at hk
  | flip R =>
      change contact = R.afterReturn ∨ contact = R.returnState
      have hchanges' : ∀ j, contact j ≠ R.afterReturn j →
          j = R.actionSwitch := by
        intro j hj
        have h := hchanges j (by
          change contact j ≠ R.afterReturn j
          exact hj)
        change j = R.secondArm / 3 at h
        exact h.trans R.secondArm_switch
      have hrelation :
          R.afterReturn = contact ∨
            R.afterReturn = flipAt contact R.actionSwitch :=
        tongues_eq_or_eq_flipAt_of_changes_only
          (u := R.afterReturn) (v := contact)
          (k := R.actionSwitch) hchanges'
      rcases hrelation with heq | hflip
      · exact Or.inl heq.symm
      · right
        have hpre : R.returnState =
            flipAt R.afterReturn R.actionSwitch := by
          simpa [ManufacturedReflector.preReturn,
            ManufacturedReflector.activatedState,
            ManufacturedReflector.toSupported,
            ManufacturedFlipReflector.toSupported,
            LocalAction.apply] using
              (ManufacturedReflector.flip R).preReturn_eq_action_activated
        calc
          contact = flipAt (flipAt contact R.actionSwitch)
              R.actionSwitch := by rw [flipAt_flipAt]
          _ = flipAt R.afterReturn R.actionSwitch := by rw [hflip]
          _ = R.returnState := hpre.symm

/-- A two-phase historical prefix followed by a direct two-vector suffix
has one-vector novelty over the shared history. -/
theorem two_phase_prefix_then_direct_tail_one_novelty
    {w : Wiring} {N lead : Nat}
    {start endpoint : Nat × Tongues} {u v : Tongues}
    (hreach : stepN w lead start = some endpoint)
    (hphase : ∀ d, d ≤ lead → ∃ port phase,
      stepN w d start = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (hendpoint : endpoint.2 = v)
    (history : List (List Bool))
    (hu : VectorCount.restrict N u ∈ history)
    (hv : VectorCount.restrict N v ∈ history)
    (htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes, (stepN w k endpoint).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N endpoint)).Nodup →
      tailTimes.length ≤ 2)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    NoveltyCoverOn w N start times history 1 := by
  have hprefix : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ history := by
    intro d hd
    obtain ⟨port, phase, hrun, hp⟩ := hphase d hd
    have hvec : restrictedTonguesAt w N start d =
        VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hrun]
    rw [hvec]
    rcases hp with rfl | rfl
    · exact hu
    · exact hv
  have hboundary : VectorCount.restrict N endpoint.2 ∈ history := by
    simpa [hendpoint] using hv
  have hcover := boundary_history_then_direct_tail_cover
    hreach history hprefix hboundary htail (by omega)
      times hlive hnd
  simpa using hcover

/-- A direct three-state tail with two distinct historical states actually
costs at most one new vector.  The witnesses need not occur in the sampled
list: if two different nonhistorical samples existed, adjoining the two
historical witness times would contradict the three-state cap. -/
private theorem direct_three_tail_one_novelty_of_two_historical_witnesses
    {w : Wiring} {N d₁ d₂ p₁ p₂ : Nat}
    {start : Nat × Tongues} {u₁ u₂ : Tongues}
    (history : List (List Bool))
    (hrun₁ : stepN w d₁ start = some (p₁, u₁))
    (hrun₂ : stepN w d₂ start = some (p₂, u₂))
    (hhist₁ : VectorCount.restrict N u₁ ∈ history)
    (hhist₂ : VectorCount.restrict N u₂ ∈ history)
    (hne : VectorCount.restrict N u₁ ≠
      VectorCount.restrict N u₂)
    (hthree : ∀ samples : List Nat,
      (∀ k ∈ samples, (stepN w k start).isSome) →
      (samples.map (restrictedTonguesAt w N start)).Nodup →
      samples.length ≤ 3)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome) :
    NoveltyCoverOn w N start times history 1 := by
  let f := restrictedTonguesAt w N start
  have hf₁ : f d₁ = VectorCount.restrict N u₁ := by
    simp [f, restrictedTonguesAt, tonguesAt, hrun₁]
  have hf₂ : f d₂ = VectorCount.restrict N u₂ := by
    simp [f, restrictedTonguesAt, tonguesAt, hrun₂]
  have hd₁Live : (stepN w d₁ start).isSome := by
    rw [hrun₁]
    simp
  have hd₂Live : (stepN w d₂ start).isSome := by
    rw [hrun₂]
    simp
  by_cases hnew : ∃ k, k ∈ times ∧ f k ∉ history
  · obtain ⟨k₀, hk₀, hk₀New⟩ := hnew
    refine ⟨[f k₀], by simp, ?_⟩
    intro k hk
    by_cases hkHist : f k ∈ history
    · exact List.mem_append_left _ hkHist
    · apply List.mem_append_right
      simp only [List.mem_singleton]
      apply Classical.byContradiction
      intro hkNe
      have hf₁Hist : f d₁ ∈ history := by simpa [hf₁] using hhist₁
      have hf₂Hist : f d₂ ∈ history := by simpa [hf₂] using hhist₂
      have h₁₂ : f d₁ ≠ f d₂ := by simpa [hf₁, hf₂] using hne
      have h₁₀ : f d₁ ≠ f k₀ := by
        intro heq
        apply hk₀New
        rw [← heq]
        exact hf₁Hist
      have h₂₀ : f d₂ ≠ f k₀ := by
        intro heq
        apply hk₀New
        rw [← heq]
        exact hf₂Hist
      have h₁k : f d₁ ≠ f k := by
        intro heq
        apply hkHist
        rw [← heq]
        exact hf₁Hist
      have h₂k : f d₂ ≠ f k := by
        intro heq
        apply hkHist
        rw [← heq]
        exact hf₂Hist
      have h₀k : f k₀ ≠ f k := by
        intro heq
        exact hkNe heq.symm
      have hndFour :
          ([d₁, d₂, k₀, k].map f).Nodup := by
        simp [h₁₂, h₁₀, h₂₀, h₁k, h₂k, h₀k]
      have hfourLive : ∀ j ∈ [d₁, d₂, k₀, k],
          (stepN w j start).isSome := by
        intro j hj
        simp at hj
        rcases hj with rfl | rfl | rfl | rfl
        · exact hd₁Live
        · exact hd₂Live
        · exact hlive _ hk₀
        · exact hlive _ hk
      have hbound := hthree [d₁, d₂, k₀, k] hfourLive hndFour
      simp at hbound
  · refine ⟨[], by simp, ?_⟩
    intro k hk
    simp only [List.append_nil]
    apply Classical.byContradiction
    intro hkNot
    exact hnew ⟨k, hk, hkNot⟩

/-- Flipping a represented switch changes the restricted tongue vector. -/
private theorem restrict_flipAt_ne_of_lt
    {N C : Nat} {u : Tongues} (hC : C < N) :
    VectorCount.restrict N (flipAt u C) ≠
      VectorCount.restrict N u := by
  intro heq
  have hbit := restrict_eq_apply heq hC
  simp [flipAt] at hbit

/-- A direct four-state tail with three pairwise-distinct historical reached
states costs at most one new vector. -/
private theorem direct_four_tail_one_novelty_of_three_historical_witnesses
    {w : Wiring} {N d₁ d₂ d₃ p₁ p₂ p₃ : Nat}
    {start : Nat × Tongues} {u₁ u₂ u₃ : Tongues}
    (history : List (List Bool))
    (hrun₁ : stepN w d₁ start = some (p₁, u₁))
    (hrun₂ : stepN w d₂ start = some (p₂, u₂))
    (hrun₃ : stepN w d₃ start = some (p₃, u₃))
    (hhist₁ : VectorCount.restrict N u₁ ∈ history)
    (hhist₂ : VectorCount.restrict N u₂ ∈ history)
    (hhist₃ : VectorCount.restrict N u₃ ∈ history)
    (hne₁₂ : VectorCount.restrict N u₁ ≠
      VectorCount.restrict N u₂)
    (hne₁₃ : VectorCount.restrict N u₁ ≠
      VectorCount.restrict N u₃)
    (hne₂₃ : VectorCount.restrict N u₂ ≠
      VectorCount.restrict N u₃)
    (hfour : ∀ samples : List Nat,
      (∀ k ∈ samples, (stepN w k start).isSome) →
      (samples.map (restrictedTonguesAt w N start)).Nodup →
      samples.length ≤ 4)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome) :
    NoveltyCoverOn w N start times history 1 := by
  let f := restrictedTonguesAt w N start
  have hf₁ : f d₁ = VectorCount.restrict N u₁ := by
    simp [f, restrictedTonguesAt, tonguesAt, hrun₁]
  have hf₂ : f d₂ = VectorCount.restrict N u₂ := by
    simp [f, restrictedTonguesAt, tonguesAt, hrun₂]
  have hf₃ : f d₃ = VectorCount.restrict N u₃ := by
    simp [f, restrictedTonguesAt, tonguesAt, hrun₃]
  have hd₁Live : (stepN w d₁ start).isSome := by rw [hrun₁]; simp
  have hd₂Live : (stepN w d₂ start).isSome := by rw [hrun₂]; simp
  have hd₃Live : (stepN w d₃ start).isSome := by rw [hrun₃]; simp
  by_cases hnew : ∃ k, k ∈ times ∧ f k ∉ history
  · obtain ⟨k₀, hk₀, hk₀New⟩ := hnew
    refine ⟨[f k₀], by simp, ?_⟩
    intro k hk
    by_cases hkHist : f k ∈ history
    · exact List.mem_append_left _ hkHist
    · apply List.mem_append_right
      simp only [List.mem_singleton]
      apply Classical.byContradiction
      intro hkNe
      have hf₁Hist : f d₁ ∈ history := by simpa [hf₁] using hhist₁
      have hf₂Hist : f d₂ ∈ history := by simpa [hf₂] using hhist₂
      have hf₃Hist : f d₃ ∈ history := by simpa [hf₃] using hhist₃
      have h₁₂ : f d₁ ≠ f d₂ := by simpa [hf₁, hf₂] using hne₁₂
      have h₁₃ : f d₁ ≠ f d₃ := by simpa [hf₁, hf₃] using hne₁₃
      have h₂₃ : f d₂ ≠ f d₃ := by simpa [hf₂, hf₃] using hne₂₃
      have h₁₀ : f d₁ ≠ f k₀ := by
        intro heq; exact hk₀New (heq ▸ hf₁Hist)
      have h₂₀ : f d₂ ≠ f k₀ := by
        intro heq; exact hk₀New (heq ▸ hf₂Hist)
      have h₃₀ : f d₃ ≠ f k₀ := by
        intro heq; exact hk₀New (heq ▸ hf₃Hist)
      have h₁k : f d₁ ≠ f k := by
        intro heq; exact hkHist (heq ▸ hf₁Hist)
      have h₂k : f d₂ ≠ f k := by
        intro heq; exact hkHist (heq ▸ hf₂Hist)
      have h₃k : f d₃ ≠ f k := by
        intro heq; exact hkHist (heq ▸ hf₃Hist)
      have h₀k : f k₀ ≠ f k := by
        intro heq; exact hkNe heq.symm
      have hndFive : ([d₁, d₂, d₃, k₀, k].map f).Nodup := by
        simp [h₁₂, h₁₃, h₂₃, h₁₀, h₂₀, h₃₀,
          h₁k, h₂k, h₃k, h₀k]
      have hfiveLive : ∀ j ∈ [d₁, d₂, d₃, k₀, k],
          (stepN w j start).isSome := by
        intro j hj
        simp at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl
        · exact hd₁Live
        · exact hd₂Live
        · exact hd₃Live
        · exact hlive _ hk₀
        · exact hlive _ hk
      have hbound := hfour [d₁, d₂, d₃, k₀, k]
        hfiveLive hndFive
      simp at hbound
  · refine ⟨[], by simp, ?_⟩
    intro k hk
    simp only [List.append_nil]
    apply Classical.byContradiction
    intro hkNot
    exact hnew ⟨k, hk, hkNot⟩

/-- The final-return facing early exit costs one fresh vector over any
history containing the protected reflector's activated and pre-return
states. -/
private theorem ManufacturedReflector.return_change_facing_one_novelty
    {w : Wiring} {N g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {contact : Tongues} {approach suffix : List Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState) approach
      (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hp : p % 3 = 0)
    (hswitch : p / 3 = B.preReturn.1 / 3)
    (hreturnChange : B.activatedState (p / 3) ≠
      B.preReturn.2 (p / 3))
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (times : List Nat)
    (hlive : ∀ d ∈ times,
      (stepN w d (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  cases B with
  | stay R => exact (hreturnChange rfl).elim
  | flip R =>
      have hsecondSwitch : R.secondArm / 3 = R.mouth / 3 := by
        have hs := arrive_exit_switch R.returnState R.secondArm
        rw [R.crossed] at hs
        exact hs.symm
      have hmouthStem := R.mouth_is_stem
      have hpmouth : p = R.mouth := by
        change p / 3 = R.secondArm / 3 at hswitch
        omega
      subst p
      have hrouteSimple :=
        A.orientedRoute_simple (ManufacturedReflector.flip R).activatedState
      have happroachSimple : SwitchSimple approach := by
        unfold SwitchSimple at hrouteSimple ⊢
        rw [hrouteSplit] at hrouteSimple
        simp only [List.map_append, List.map_cons] at hrouteSimple
        exact (List.nodup_append.mp hrouteSimple).1
      have hrouteMembership : ∀ passage ∈ approach,
          passage ∈ A.orientedRoute
            (ManufacturedReflector.flip R).activatedState := by
        intro passage hpassage
        rw [hrouteSplit]
        exact List.mem_append_left _ hpassage
      have hphase := A.repair_prefix_two_phase (.flip R) hA hBstart
        happroach happroachSimple hrouteMembership hpaths
      have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
        (.flip R) hA hBstart happroach happroachSimple
          hrouteMembership hpaths
      have hcontactHistorical : VectorCount.restrict N contact ∈ history := by
        rcases hrelation with rfl | rfl
        · exact hinitialHistorical
        · exact hpreHistorical
      have happroachGrooved : PassagesGrooved contact approach :=
        happroach.grooved_of_switchSimple happroachSimple
      have happroachContact : PhysicalTrace w
          (g, contact) approach (R.mouth, contact) :=
        happroach.replay_grooved contact happroachGrooved
      have hforeign : ∀ passage ∈ approach,
          passageSwitch passage ≠ R.actionSwitch := by
        have hsimple :=
          A.orientedRoute_simple
            (ManufacturedReflector.flip R).activatedState
        unfold SwitchSimple at hsimple
        rw [hrouteSplit] at hsimple
        simp only [List.map_append, List.map_cons] at hsimple
        have hparts := List.nodup_append.mp hsimple
        intro passage hpassage hEq
        have hne := hparts.2.2 (passageSwitch passage)
          (List.mem_map.mpr ⟨passage, hpassage, rfl⟩)
          (passageSwitch (R.mouth, x)) (by simp)
        apply hne
        simpa [passageSwitch,
          ManufacturedFlipReflector.actionSwitch] using hEq
      have hall := R.facing_mouth_tail_two_phase
        happroachContact happroachSimple hforeign hpaths
      have htail : ∀ tailTimes : List Nat,
          (∀ d ∈ tailTimes,
            (stepN w d (R.mouth, contact)).isSome) →
          (tailTimes.map
            (restrictedTonguesAt w N (R.mouth, contact))).Nodup →
          tailTimes.length ≤ 2 := by
        intro tailTimes _ htailNodup
        let tailHistory := [VectorCount.restrict N contact,
          VectorCount.restrict N (flipAt contact R.actionSwitch)]
        have hcover : NoveltyCoverOn w N (R.mouth, contact)
            tailTimes [] 2 := by
          refine ⟨tailHistory, by simp [tailHistory], ?_⟩
          intro d hd
          simp only [List.nil_append]
          obtain ⟨port, phase, hrun, hphaseTail⟩ := hall d
          have hvec : restrictedTonguesAt w N (R.mouth, contact) d =
              VectorCount.restrict N phase := by
            simp [restrictedTonguesAt, tonguesAt, hrun]
          rw [hvec]
          rcases hphaseTail with h | h
          · simp [tailHistory, h]
          · simp [tailHistory, h]
        have hcount := noveltyCoverOn_distinct_count hcover htailNodup
        simpa using hcount
      exact two_phase_prefix_then_direct_tail_one_novelty
        happroach.sound hphase rfl history hinitialHistorical
          hcontactHistorical htail times hlive hnd

/-- A backward state-changing protected contact costs one fresh vector over
the activated/pre-return history; otherwise the exact forward merge is
retained. -/
private theorem ManufacturedReflector.protected_changed_contact_one_or_forward
    {w : Wiring} {N g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {u v : Tongues} {approach suffix : List Passage}
    {path : List Passage} {old : Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, x) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState) approach (p, u))
    (hpaths : PathGrooves B.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hpath : path ∈ B.toSupported.paths)
    (hold : old ∈ path)
    (hswitch : passageSwitch old = p / 3)
    (hchanged : v (p / 3) ≠ u (p / 3))
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) times history 1) ∨
      ∃ oriented repaired,
        oriented ∈ B.orientedRoute u ∧
        arrive u oriented.2 = (oriented.1, u) ∧
        passageSwitch oriented = p / 3 ∧
        x = oriented.2 ∧
        arrive v oriented.1 = (oriented.2, repaired) ∧
        arrive repaired oriented.2 = (oriented.1, repaired) := by
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    B.changed_contact_on_orientedRoute u v hpaths
      hpath hold hswitch harrive hchanged
  rcases hdirection with hbackward | hforward
  · obtain ⟨recorded, tail, hBsplit⟩ := List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace u hpaths
    have hBsimple := B.orientedRoute_simple u
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedForeign : ∀ passage ∈ recorded,
        passageSwitch passage ≠ p / 3 := by
      intro passage hp hEq
      apply hprefixData.2 passage hp
      exact hEq.trans horientedSwitch.symm
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hflip : v = flipAt u (p / 3) :=
      changed_arrival_eq_flipAt harrive hchanged
    have hrecordedV : PhysicalTrace w
        (e, v) recorded (oriented.1, v) := by
      rw [hflip]
      exact hrecorded.flip_unvisited hrecordedForeign
    have hrecordedGroovedV : PassagesGrooved v recorded :=
      hrecordedV.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple
      exact (List.nodup_append.mp hrouteSimple).1
    have happroachForeign : ∀ passage ∈ approach,
        passageSwitch passage ≠ p / 3 := by
      unfold SwitchSimple at hrouteSimple
      simp only [List.map_append, List.map_cons] at hrouteSimple
      have hparts := List.nodup_append.mp hrouteSimple
      intro passage hp hEq
      have hne := hparts.2.2 (passageSwitch passage)
        (List.mem_map.mpr ⟨passage, hp, rfl⟩)
        (p / 3) (by simp [passageSwitch])
      exact hne hEq
    have happroachV : PhysicalTrace w
        (g, flipAt B.activatedState (p / 3)) approach (p, v) := by
      rw [hflip]
      exact happroach.flip_unvisited happroachForeign
    have happroachGroovedV : PassagesGrooved v approach :=
      happroachV.grooved_of_switchSimple happroachSimple
    have happroachGroovedU : PassagesGrooved u approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplayU : PhysicalTrace w (g, u) approach (p, u) :=
      happroach.replay_grooved u happroachGroovedU
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
      B hA hBstart happroach happroachSimple happroachRoute hpaths
    have huHistorical : VectorCount.restrict N u ∈ history := by
      rcases hrelation with rfl | rfl
      · exact hinitialHistorical
      · exact hpreHistorical
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes, (stepN w k (p, u)).isSome) →
        (tailTimes.map (restrictedTonguesAt w N (p, u))).Nodup →
        tailTimes.length ≤ 2 := by
      intro tailTimes _ htailNodup
      exact backward_contact_tail_distinct_le_two
        hrecorded hrecordedGroovedV B.entryEdge
        (by simpa [hbackward] using harrive)
        happroachReplayU happroachGroovedV tailTimes htailNodup
    left
    intro times hlive hnd
    exact two_phase_prefix_then_direct_tail_one_novelty
      happroach.sound hphase rfl history hinitialHistorical
        huHistorical htail times hlive hnd
  · right
    obtain ⟨hforwardExit, repaired, hrepair, hgroove⟩ := hforward
    exact ⟨oriented, repaired, horiented, horientedGroove,
      horientedSwitch, hforwardExit, hrepair, hgroove⟩

/-- A backward no-change protected contact costs one fresh vector over the
activated/pre-return history; otherwise the exact facing-forward merge is
retained. -/
private theorem ManufacturedReflector.protected_facing_contact_one_or_forward
    {w : Wiring} {N g e p marker fresh : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    {contact : Tongues} {approach suffix path : List Passage}
    (hrouteSplit : A.orientedRoute B.activatedState =
      approach ++ (p, marker) :: suffix)
    (happroach : PhysicalTrace w (g, B.activatedState) approach
      (p, contact))
    (hpaths : PathGrooves B.toSupported.paths contact)
    (hpath : path ∈ B.toSupported.paths)
    (hold : (fresh, p) ∈ path)
    (harrive : arrive contact p = (fresh, contact))
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) times history 1) ∨
      (p, fresh) ∈ B.orientedRoute contact := by
  obtain ⟨oriented, horiented, horientation⟩ :=
    B.support_passage_on_orientedRoute contact hpath hold
  rcases horientation with hsame | hreverse
  · have horientedEq : oriented = (fresh, p) := hsame
    subst oriented
    obtain ⟨recorded, tail, hBsplit⟩ := List.append_of_mem horiented
    have hBroute := B.orientedRoute_trace contact hpaths
    have hBsimple := B.orientedRoute_simple contact
    have hBgrooved := hBroute.grooved_of_switchSimple hBsimple
    have hprefixData := simple_grooved_trace_prefix_to_occurrence
      hBroute hBsplit hBgrooved hBsimple
    have hrecorded := hprefixData.1
    have hrecordedSimple : SwitchSimple recorded := by
      unfold SwitchSimple at hBsimple ⊢
      rw [hBsplit] at hBsimple
      simp only [List.map_append, List.map_cons] at hBsimple
      exact (List.nodup_append.mp hBsimple).1
    have hrecordedGrooved : PassagesGrooved contact recorded :=
      hrecorded.grooved_of_switchSimple hrecordedSimple
    have hrouteSimple := A.orientedRoute_simple B.activatedState
    rw [hrouteSplit] at hrouteSimple
    have happroachSimple : SwitchSimple approach := by
      unfold SwitchSimple at hrouteSimple ⊢
      simp only [List.map_append, List.map_cons] at hrouteSimple
      exact (List.nodup_append.mp hrouteSimple).1
    have happroachGrooved : PassagesGrooved contact approach :=
      happroach.grooved_of_switchSimple happroachSimple
    have happroachReplay :
        PhysicalTrace w (g, contact) approach (p, contact) :=
      happroach.replay_grooved contact happroachGrooved
    have happroachRoute : ∀ passage ∈ approach,
        passage ∈ A.orientedRoute B.activatedState := by
      intro passage hp
      rw [hrouteSplit]
      exact List.mem_append_left _ hp
    have hphase := A.repair_prefix_two_phase B hA hBstart
      happroach happroachSimple happroachRoute hpaths
    have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
      B hA hBstart happroach happroachSimple happroachRoute hpaths
    have hcontactHistorical : VectorCount.restrict N contact ∈ history := by
      rcases hrelation with rfl | rfl
      · exact hinitialHistorical
      · exact hpreHistorical
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes, (stepN w k (p, contact)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (p, contact))).Nodup →
        tailTimes.length ≤ 2 := by
      intro tailTimes _ htailNodup
      exact backward_contact_tail_distinct_le_two
        hrecorded hrecordedGrooved B.entryEdge harrive
        happroachReplay happroachGrooved tailTimes htailNodup
    left
    intro times hlive hnd
    exact two_phase_prefix_then_direct_tail_one_novelty
      happroach.sound hphase rfl history hinitialHistorical
        hcontactHistorical htail times hlive hnd
  · right
    simpa [hreverse] using horiented

/-- Protected-repair classification with every early exit already charged
by one vector over a history containing the activated and pre-return states. -/
private theorem manufactured_pair_protected_repair_novelty_outcomes
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history) :
    (∀ times : List Nat,
      (∀ k ∈ times,
        (stepN w k (g, B.activatedState)).isSome) →
      (times.map (restrictedTonguesAt w N
        (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) times history 1) ∨
      A.FacingForwardMerge B ∨
      A.ChangedForwardMerge B ∨
      ∃ finalState,
        PhysicalTrace w (g, B.activatedState)
          (A.orientedRoute B.activatedState)
          (A.orientedFinish B.activatedState, finalState) ∧
        PathGrooves A.toSupported.paths finalState ∧
        PathGrooves B.toSupported.paths finalState := by
  rcases A.repair_current_route_preserving_until_conflict
      B.baseState B.activatedState hA hB with hfacing | hrest
  · obtain ⟨before, p, x, after, contact, other,
        hsplit, hprefix, hBcontact, hp, hchange,
        hcontact, harrive, hother⟩ := hfacing
    rcases B.facing_exit_matches_activation_passage
        hchange hcontact hp harrive with hreturn | hexploration
    · left
      intro times hlive hnd
      exact A.return_change_facing_one_novelty B hA hB
        hsplit hprefix hBcontact hp hreturn.1 hreturn.2
        history hinitialHistorical hpreHistorical times hlive hnd
    · obtain ⟨oldApproach, fresh, oldSuffix, oldU, oldV, path,
          _holdSplit, _holdSwitch, _holdTrace, _holdArrive,
          hpath, hold, hotherFresh⟩ := hexploration
      have harriveFresh : arrive contact p = (fresh, contact) := by
        simpa [hotherFresh] using harrive
      rcases A.protected_facing_contact_one_or_forward B hA hB
          hsplit hprefix hBcontact hpath hold harriveFresh history
          hinitialHistorical hpreHistorical with hcount | hforward
      · exact Or.inl hcount
      · exact Or.inr (Or.inl ⟨before, p, x, after,
          contact, fresh, path, hsplit, hprefix, hBcontact, hp,
          hchange, by simpa [passageSwitch] using hcontact,
          hpath, hold, harriveFresh,
          by simpa [hotherFresh] using hother,
          hforward⟩)
  · rcases hrest with hchanged | hcomplete
    · obtain ⟨approach, p, x, suffix, u, v, path, old,
          hsplit, hprefix, hBu, harrive,
          hpath, hold, hswitch, hchange⟩ := hchanged
      rcases A.protected_changed_contact_one_or_forward B hA hB
          hsplit hprefix hBu harrive hpath hold hswitch hchange
          history hinitialHistorical hpreHistorical with hcount | hforward
      · exact Or.inl hcount
      · obtain ⟨oriented, repaired, horiented, horientedGroove,
            horientedSwitch, hforwardExit, hrepair, hgroove⟩ := hforward
        exact Or.inr (Or.inr (Or.inl
          ⟨approach, p, x, suffix, u, v, path, old,
            oriented, repaired, hsplit, hprefix, hBu, harrive,
            hpath, hold, hswitch, hchange, horiented,
            horientedGroove, horientedSwitch, hforwardExit,
            hrepair, hgroove⟩))
    · exact Or.inr (Or.inr (Or.inr hcomplete))

/-- A facing-forward merge has at most one fresh vector over the activated
and pre-return history.  Its eventual two-phase tail consists exactly of
those two protected states; the direct three-state theorem supplies the
finite-sample formulation. -/
private theorem ManufacturedReflector.FacingForwardMerge.one_novelty_of_preReturn
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    (hmerge : A.FacingForwardMerge B)
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  obtain ⟨R, before, p, x, after, contact, fresh,
      hBeq, hrouteSplit, hprefix, hpaths, _hp, _harrive,
      _hfreshNe, hcandyMem, hsecond, _hforward⟩ := hmerge.flip_candy
  subst B
  obtain ⟨candyBefore, candyAfter, hcandySplit⟩ :=
    List.append_of_mem hcandyMem
  have hrouteSimple :=
    A.orientedRoute_simple
      (ManufacturedReflector.flip R).activatedState
  rw [hrouteSplit] at hrouteSimple
  have hbeforeSimple : SwitchSimple before := by
    unfold SwitchSimple at hrouteSimple ⊢
    simp only [List.map_append, List.map_cons] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hbeforeRoute : ∀ passage ∈ before,
      passage ∈ A.orientedRoute
        (ManufacturedReflector.flip R).activatedState := by
    intro passage hpassage
    rw [hrouteSplit]
    exact List.mem_append_left _ hpassage
  have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
    (.flip R) hA hBstart hprefix hbeforeSimple hbeforeRoute hpaths
  have hpreAction :
      (ManufacturedReflector.flip R).preReturn.2 =
        flipAt (ManufacturedReflector.flip R).activatedState
          R.actionSwitch := by
    simpa [ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported, LocalAction.apply] using
        (ManufacturedReflector.flip R).preReturn_eq_action_activated
  have hpreInitNe :
      VectorCount.restrict N (ManufacturedReflector.flip R).preReturn.2 ≠
        VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState := by
    rw [hpreAction]
    exact restrict_flipAt_ne_of_lt (R.action_lt hN)
  have hinitPreNe :
      VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState ≠
        VectorCount.restrict N (ManufacturedReflector.flip R).preReturn.2 :=
    Ne.symm hpreInitNe
  have hrunZero : stepN w 0
      (g, (ManufacturedReflector.flip R).activatedState) =
        some (g, (ManufacturedReflector.flip R).activatedState) := by
    rfl
  have hthree : ∀ samples : List Nat,
      (∀ k ∈ samples,
        (stepN w k
          (g, (ManufacturedReflector.flip R).activatedState)).isSome) →
      (samples.map (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState))).Nodup →
      samples.length ≤ 3 := by
    intro samples hsLive hsNodup
    exact hmerge.distinct_le_three hA hBstart samples hsLive hsNodup
  rcases hrelation with hcontactInitial | hcontactPre
  · obtain ⟨tailTravel, _htailPositive, _htailLe, htailContact,
        _htailAlternate, _htailContactPhase, _htailAlternatePhase⟩ :=
      R.reverse_candy_suffix_absorbs_twoPhases contact hpaths hsecond
        hcandySplit
    let loopSteps := before.length + tailTravel
    have hrunAlternate : stepN w loopSteps
        (g, (ManufacturedReflector.flip R).activatedState) =
          some (g, flipAt contact R.actionSwitch) := by
      dsimp [loopSteps]
      rw [stepN_add, hprefix.sound]
      exact htailContact
    have hAlternatePre : flipAt contact R.actionSwitch =
        (ManufacturedReflector.flip R).preReturn.2 := by
      rw [hcontactInitial]
      exact hpreAction.symm
    apply direct_three_tail_one_novelty_of_two_historical_witnesses
      history hrunZero hrunAlternate hinitialHistorical
        (by simpa [hAlternatePre] using hpreHistorical)
        (by simpa [hAlternatePre] using hinitPreNe)
        hthree times hlive
  · apply direct_three_tail_one_novelty_of_two_historical_witnesses
      history hrunZero hprefix.sound hinitialHistorical
        (by simpa [hcontactPre] using hpreHistorical)
        (by simpa [hcontactPre] using hinitPreNe)
        hthree times hlive

/-- A changed-forward splice into a stay reflector has one fresh tail vector
over the activated/pre-return history. -/
private theorem ManufacturedReflector.ChangedForwardMerge.stay_one_novelty_of_preReturn
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedStayReflector w e g}
    (hA : PathGrooves A.toSupported.paths
      (ManufacturedReflector.stay R).baseState)
    (hBstart : PathGrooves (ManufacturedReflector.stay R).toSupported.paths
      (ManufacturedReflector.stay R).activatedState)
    (hmerge : A.ChangedForwardMerge (.stay R))
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N
      (ManufacturedReflector.stay R).activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N
      (ManufacturedReflector.stay R).preReturn.2 ∈ history)
    (times : List Nat)
    (hlive : ∀ d ∈ times,
      (stepN w d
        (g, (ManufacturedReflector.stay R).activatedState)).isSome)
    (hnd : (times.map (restrictedTonguesAt w N
      (g, (ManufacturedReflector.stay R).activatedState))).Nodup) :
    NoveltyCoverOn w N
      (g, (ManufacturedReflector.stay R).activatedState)
      times history 1 := by
  obtain ⟨approach, returnPort, state, k,
      hActiveApproach, hApproachSimple, hApproachRoute,
      hRpaths, hall⟩ := hmerge.stay_active_precontact_two_phase
  have hphase := A.repair_prefix_two_phase (.stay R) hA hBstart
    hActiveApproach hApproachSimple hApproachRoute hRpaths
  have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn
    (.stay R) hA hBstart hActiveApproach hApproachSimple
      hApproachRoute hRpaths
  have hstateHistorical : VectorCount.restrict N state ∈ history := by
    rcases hrelation with rfl | rfl
    · exact hinitialHistorical
    · exact hpreHistorical
  have htail : ∀ tailTimes : List Nat,
      (∀ d ∈ tailTimes,
        (stepN w d (returnPort, state)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (returnPort, state))).Nodup →
      tailTimes.length ≤ 2 := by
    intro tailTimes _ htailNodup
    let tailHistory := [VectorCount.restrict N state,
      VectorCount.restrict N (flipAt state k)]
    have hcover : NoveltyCoverOn w N (returnPort, state)
        tailTimes [] 2 := by
      refine ⟨tailHistory, by simp [tailHistory], ?_⟩
      intro d hd
      simp only [List.nil_append]
      obtain ⟨port, phase, hrun, hphaseTail⟩ := hall d
      have hvec : restrictedTonguesAt w N (returnPort, state) d =
          VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hrun]
      rw [hvec]
      rcases hphaseTail with h | h
      · simp [tailHistory, h]
      · simp [tailHistory, h]
    have hcount := noveltyCoverOn_distinct_count hcover htailNodup
    simpa using hcount
  exact two_phase_prefix_then_direct_tail_one_novelty
    hActiveApproach.sound hphase rfl history hinitialHistorical
      hstateHistorical htail times hlive hnd

/-- A trailing passage on a reflector's selected outward route is one of
its reusable support passages (possibly with the candy orientation
reversed), hence is traversed without changing any tongue in every state
which grooves that support. -/
private theorem ManufacturedReflector.trailing_orientedRoute_grooved
    {w : Wiring} {g e p x : Nat}
    (A : ManufacturedReflector w g e)
    (selector state : Tongues)
    (hpaths : PathGrooves A.toSupported.paths state)
    (hmem : (p, x) ∈ A.orientedRoute selector)
    (hpBranch : p % 3 ≠ 0) :
    arrive state p = (x, state) := by
  cases A with
  | stay R =>
      change PathGrooves [R.runway, [(R.mouth, R.arm)]] state at hpaths
      change (p, x) ∈ R.runway ++ [(R.mouth, R.arm)] at hmem
      rcases List.mem_append.mp hmem with hrunway | hcore
      · exact groove_forward
          (hpaths R.runway (by simp) (p, x) hrunway)
      · simp only [List.mem_singleton] at hcore
        rcases Prod.mk.inj hcore with ⟨rfl, rfl⟩
        exact groove_forward
          (hpaths [(R.mouth, R.arm)] (by simp)
            (R.mouth, R.arm) (by simp))
  | flip R =>
      change PathGrooves [R.runway, R.candy] state at hpaths
      by_cases hselected : selector R.actionSwitch = bval R.firstArm
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          if_pos] at hmem
        rcases List.mem_append.mp hmem with hrunway | hrest
        · exact groove_forward
            (hpaths R.runway (by simp) (p, x) hrunway)
        · rcases List.mem_cons.mp hrest with hmouth | hcandy
          · have hpMouth : p = R.mouth := congrArg Prod.fst hmouth
            exact (hpBranch (by rw [hpMouth]; exact R.mouth_is_stem)).elim
          · exact groove_forward
              (hpaths R.candy (by simp) (p, x) hcandy)
      · simp only [ManufacturedReflector.orientedRoute, hselected,
          if_false] at hmem
        rcases List.mem_append.mp hmem with hrunway | hrest
        · exact groove_forward
            (hpaths R.runway (by simp) (p, x) hrunway)
        · rcases List.mem_cons.mp hrest with hmouth | hcandy
          · have hpMouth : p = R.mouth := congrArg Prod.fst hmouth
            exact (hpBranch (by rw [hpMouth]; exact R.mouth_is_stem)).elim
          · have hreverse : PassagesGrooved state
                (reversePassages R.candy) :=
              reversePassages_grooved (hpaths R.candy (by simp))
            exact groove_forward (hreverse (p, x) hcandy)

/-- Under the fully protected pre-return hypothesis a changed forward merge
is impossible.  The changed route passage is a reusable passage of `A`, so
`hpre` grooves it in `B.preReturn`.  The same switch is also represented in
`B`'s support.  That support is grooved both at the contact state and at
`B.preReturn`, forcing the two tongue values to agree, while the changed
trailing arrival forces them to be opposite. -/
private theorem ManufacturedReflector.ChangedForwardMerge.impossible_of_preReturn_grooved
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (hBstart : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (hmerge : A.ChangedForwardMerge B) : False := by
  obtain ⟨approach, p, x, suffix, u, v, path, old,
      oriented, repaired, hsplit, _hprefix, hBu, harrive,
      hpath, hold, hswitch, hchanged, _horiented,
      _horientedGroove, _horientedSwitch, _hforward,
      _hrepair, _hrestored⟩ := hmerge
  have hmem : (p, x) ∈ A.orientedRoute B.activatedState := by
    rw [hsplit]
    exact List.mem_append_right approach List.mem_cons_self
  obtain ⟨hpBranch, _hxStem, hvPin, _hback⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hprePassage : arrive B.preReturn.2 p =
      (x, B.preReturn.2) :=
    A.trailing_orientedRoute_grooved B.activatedState
      B.preReturn.2 hpre hmem hpBranch
  have hBpre : PathGrooves B.toSupported.paths B.preReturn.2 := by
    rw [B.preReturn_eq_action_activated]
    exact hBstart.after_avoiding_action B.action_avoids_own_support
  have hupre := pathGrooves_agree_at_support_passage
    hBu hBpre hpath hold
  have hupre' : u (p / 3) = B.preReturn.2 (p / 3) := by
    rw [hswitch] at hupre
    exact hupre
  have hprePin : pin B.preReturn.2 p = B.preReturn.2 := by
    unfold arrive at hprePassage
    rw [if_neg hpBranch] at hprePassage
    exact (Prod.mk.inj hprePassage).2
  have hvValue : v (p / 3) = bval p := by
    rw [hvPin]
    simp [pin]
  have hpreValue : B.preReturn.2 (p / 3) = bval p := by
    have h := congrFun hprePin (p / 3)
    simp only [pin, if_pos] at h
    exact h.symm
  apply hchanged
  calc
    v (p / 3) = bval p := hvValue
    _ = B.preReturn.2 (p / 3) := hpreValue.symm
    _ = u (p / 3) := hupre'.symm

/-- If the first reflector's facing mouth is the first productive event of
the second construction, that event lands on the first reflector's
pre-return vector. -/
theorem ManufacturedFlipReflector.first_action_writer_post_eq_preReturn
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = (ManufacturedReflector.flip R).activatedState)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (hfirst : ∀ j, j < t →
      ¬ RawProductiveAt w N (e, B.baseState) j) :
    restrictedTonguesAt w N (e, B.baseState) (t + 1) =
      VectorCount.restrict N (ManufacturedReflector.flip R).preReturn.2 := by
  have htData := mem_rawFirstWriterTimes_iff.mp ht
  have hprod : RawProductiveAt w N (e, B.baseState) t := htData.2.1
  obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hprod.1
  obtain ⟨atT, hatT⟩ := stepN_prefix_some (d := t) (K := t + 1)
    (by omega) hfinish
  have hquiet : restrictedTonguesAt w N (e, B.baseState) t =
      restrictedTonguesAt w N (e, B.baseState) 0 := by
    have h := restrictedTonguesAt_eq_of_quiet_interval
      (first := 0) (span := t) (by simpa using hatT)
      (fun j _hj0 hjt => hfirst j (by simpa using hjt))
    simpa using h
  have hquietState :
      VectorCount.restrict N (tonguesAt w (e, B.baseState) t) =
        VectorCount.restrict N B.baseState := by
    simpa [restrictedTonguesAt, tonguesAt, stepN] using hquiet
  have hflip := rawProductiveAt_restricted_flip hN hprod
  have hpreAction :
      (ManufacturedReflector.flip R).preReturn.2 =
        flipAt (ManufacturedReflector.flip R).activatedState
          R.actionSwitch := by
    simpa [ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported, LocalAction.apply] using
        (ManufacturedReflector.flip R).preReturn_eq_action_activated
  calc
    restrictedTonguesAt w N (e, B.baseState) (t + 1) =
        VectorCount.restrict N
          (flipAt (tonguesAt w (e, B.baseState) t)
            R.actionSwitch) := by simpa [hwriter] using hflip
    _ = VectorCount.restrict N (flipAt B.baseState R.actionSwitch) :=
      restrict_flipAt_congr hquietState
    _ = VectorCount.restrict N
        (flipAt (ManufacturedReflector.flip R).activatedState
          R.actionSwitch) := by rw [hbase]
    _ = VectorCount.restrict N
        (ManufacturedReflector.flip R).preReturn.2 := by rw [hpreAction]

/-- The protected pair history with both the shared activation boundary and
the first reflector's pre-return duplicate erased from the second history. -/
noncomputable def ManufacturedFlipReflector.firstQuietProtectedHistory
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (N : Nat) : List (List Bool) :=
  (ManufacturedReflector.flip R).sharpHistoryCore N ++
    ((B.writerConstructionHistory N).erase
      (VectorCount.restrict N
        (ManufacturedReflector.flip R).activatedState)).erase
      (VectorCount.restrict N
        (ManufacturedReflector.flip R).preReturn.2)

/-- The doubly compressed history still represents both manufacturing
journeys. -/
theorem ManufacturedFlipReflector.mem_firstQuietProtectedHistory
    {w : Wiring} {N g e : Nat}
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    {x : List Bool}
    (hx : x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N ∨
      x ∈ B.sharpConstructionHistory N) :
    x ∈ R.firstQuietProtectedHistory B N := by
  rcases hx with hA | hB
  · apply List.mem_append_left
    exact (ManufacturedReflector.flip R).mem_sharpHistoryCore_of_mem hA
  · have hBcompressed := B.mem_writerConstructionHistory_of_mem_sharp hB
    by_cases hboundary :
        x = VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState
    · subst x
      apply List.mem_append_left
      exact (ManufacturedReflector.flip R).activated_mem_sharpHistoryCore
    · by_cases hpre :
          x = VectorCount.restrict N
            (ManufacturedReflector.flip R).preReturn.2
      · subst x
        apply List.mem_append_left
        exact (ManufacturedReflector.flip R).preReturn_mem_sharpHistoryCore
      · apply List.mem_append_right
        exact (List.mem_erase_of_ne hpre).mpr
          ((List.mem_erase_of_ne hboundary).mpr hBcompressed)

/-- When the omitted mouth is the first productive writer of the second
construction, the doubly compressed construction cover has size at most
`N+2`. -/
theorem ManufacturedFlipReflector.firstQuietProtectedHistory_length_le_N_add_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = (ManufacturedReflector.flip R).activatedState)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (hfirst : ∀ j, j < t →
      ¬ RawProductiveAt w N (e, B.baseState) j) :
    (R.firstQuietProtectedHistory B N).length ≤ N + 2 := by
  let A : ManufacturedReflector w g e := .flip R
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.writerConstructionHistory N := by
    dsimp [A]
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hpost := R.first_action_writer_post_eq_preReturn
    hN B hbase ht hwriter hfirst
  have hpostMem : VectorCount.restrict N A.preReturn.2 ∈
      B.writerConstructionHistory N := by
    apply List.mem_append_left
    unfold rawFirstWriterHistory
    apply List.mem_cons.mpr
    apply Or.inr
    apply List.mem_map.mpr
    exact ⟨t, ht, hpost⟩
  have htData := mem_rawFirstWriterTimes_iff.mp ht
  have hprod : RawProductiveAt w N (e, B.baseState) t := htData.2.1
  obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hprod.1
  obtain ⟨atT, hatT⟩ := stepN_prefix_some (d := t) (K := t + 1)
    (by omega) hfinish
  have hquiet : restrictedTonguesAt w N (e, B.baseState) t =
      restrictedTonguesAt w N (e, B.baseState) 0 := by
    have h := restrictedTonguesAt_eq_of_quiet_interval
      (first := 0) (span := t) (by simpa using hatT)
      (fun j _hj0 hjt => hfirst j (by simpa using hjt))
    simpa using h
  have hpreNeBoundary :
      VectorCount.restrict N A.preReturn.2 ≠
        VectorCount.restrict N A.activatedState := by
    intro heq
    dsimp [A] at heq
    apply hprod.2
    calc
      restrictedTonguesAt w N (e, B.baseState) (t + 1) =
          VectorCount.restrict N
            (ManufacturedReflector.flip R).preReturn.2 := hpost
      _ = VectorCount.restrict N
          (ManufacturedReflector.flip R).activatedState := heq
      _ = restrictedTonguesAt w N (e, B.baseState) 0 := by
        simp [restrictedTonguesAt, tonguesAt, stepN, hbase]
      _ = restrictedTonguesAt w N (e, B.baseState) t := hquiet.symm
  have hpreAfterBoundary :
      VectorCount.restrict N A.preReturn.2 ∈
        (B.writerConstructionHistory N).erase
          (VectorCount.restrict N A.activatedState) :=
    (List.mem_erase_of_ne hpreNeBoundary).mpr hpostMem
  have hcharge := A.reusable_add_second_first_writers_le
    hN B hbaseGrooves hpreGrooves
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedFlipReflector.firstQuietProtectedHistory
  rw [List.length_append,
    List.length_erase_of_mem hpreAfterBoundary,
    List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

/-- If the first reflector's facing mouth is the last productive event of
the second exploration, flipping that mouth in the second pre-return vector
recovers the historical pre-write vector. -/
theorem ManufacturedFlipReflector.flipped_preReturn_mem_preservedHistory_of_last
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (hlast : ∀ j, t < j → j < B.exploration.length →
      ¬ RawProductiveAt w N (e, B.baseState) j) :
    VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) ∈
      (ManufacturedReflector.flip R).preservedTwoHistoryCore B N := by
  have htData := mem_rawFirstWriterTimes_iff.mp ht
  have hprod : RawProductiveAt w N (e, B.baseState) t := htData.2.1
  let span := B.exploration.length - (t + 1)
  have hsum : t + 1 + span = B.exploration.length := by
    dsimp [span]
    omega
  have hendQuiet :
      restrictedTonguesAt w N (e, B.baseState) B.exploration.length =
        restrictedTonguesAt w N (e, B.baseState) (t + 1) := by
    have h := restrictedTonguesAt_eq_of_quiet_interval
      (first := t + 1) (span := span)
      (by simpa [hsum] using B.exploration_trace.sound)
      (fun j hj hbound => hlast j (by omega) (by
        rw [hsum] at hbound
        exact hbound))
    simpa [hsum] using h
  have hend :
      restrictedTonguesAt w N (e, B.baseState) B.exploration.length =
        VectorCount.restrict N B.preReturn.2 := by
    simp [restrictedTonguesAt, tonguesAt, B.exploration_trace.sound]
  have hpost := rawProductiveAt_restricted_flip hN hprod
  rw [hwriter] at hpost
  have hflipEnd := restrict_flipAt_congr (C := R.actionSwitch)
    (hend.symm.trans hendQuiet)
  have hflipPost := restrict_flipAt_congr (C := R.actionSwitch) hpost
  have hrecover :
      VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) =
        restrictedTonguesAt w N (e, B.baseState) t := by
    calc
      VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) =
          VectorCount.restrict N
            (flipAt (tonguesAt w (e, B.baseState) (t + 1))
              R.actionSwitch) := hflipEnd
      _ = VectorCount.restrict N
          (flipAt
            (flipAt (tonguesAt w (e, B.baseState) t)
              R.actionSwitch)
            R.actionSwitch) := hflipPost
      _ = restrictedTonguesAt w N (e, B.baseState) t := by
        simp [restrictedTonguesAt, flipAt_flipAt]
  have htime : restrictedTonguesAt w N (e, B.baseState) t ∈
      B.sharpConstructionHistory N := by
    unfold ManufacturedReflector.sharpConstructionHistory
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨t, List.mem_range.mpr (by omega), rfl⟩
  rw [hrecover]
  exact (ManufacturedReflector.flip R).mem_preservedTwoHistoryCore B
    (Or.inr htime)

/-- A completed protected repair needs only one fresh vector whenever the
`A`-action applied to `B`'s pre-return vector is historical.  Depending on
which of the two repair phases is final, this historical vector is one of
the two nominally fresh Gray-square corners. -/
theorem ManufacturedReflector.completed_protected_route_one_novelty_of_action_preReturn
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    (history : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (haPreHistorical : VectorCount.restrict N
      (A.toSupported.action.apply B.preReturn.2) ∈ history)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
  obtain ⟨reference, _hreferencePaths, hrouteEq, hfinishEq,
      hreferenceGrooved, _hguard⟩ :=
    A.current_route_reference B.baseState B.activatedState hA
  have hfinalGrooved :
      PassagesGrooved finalState (A.orientedRoute B.activatedState) :=
    hrepair.grooved_of_switchSimple
      (A.orientedRoute_simple B.activatedState)
  have hfinalReferenceGrooved :
      PassagesGrooved finalState (A.orientedRoute reference) := by
    rw [hrouteEq]
    exact hfinalGrooved
  have hreferenceGrooved' :
      PassagesGrooved reference (A.orientedRoute reference) := by
    rw [hrouteEq]
    exact hreferenceGrooved
  have horiented := A.oriented_data_eq_of_route_grooved
    reference finalState hreferenceGrooved' hfinalReferenceGrooved
  have hrouteFinal := A.orientedRoute_trace finalState hAfinal
  have hrouteFinal' : PhysicalTrace w (g, finalState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState) := by
    rw [horiented.1, horiented.2, hrouteEq, hfinishEq] at hrouteFinal
    exact hrouteFinal
  let L := (A.orientedRoute B.activatedState).length
  let endpoint : Nat × Tongues :=
    (A.orientedFinish B.activatedState, finalState)
  have hrepairReach : stepN w L (g, B.activatedState) =
      some endpoint := by
    simpa [L, endpoint] using hrepair.sound
  have hpairReach : stepN w L (g, finalState) = some endpoint := by
    simpa [L, endpoint] using hrouteFinal'.sound
  have hprefixPhase := A.repair_prefix_two_phase B hA hB
    hrepair (A.orientedRoute_simple B.activatedState)
    (by intro passage hp; exact hp) hBfinal
  have hrelation := A.completed_repair_initial_action_relation
    B hA hB hrepair hBfinal
  have hpreAction :
      B.preReturn.2 = B.toSupported.action.apply B.activatedState :=
    B.preReturn_eq_action_activated
  have hfinalHistorical :
      VectorCount.restrict N finalState ∈ history := by
    rcases hrelation with heq | haction
    · simpa [heq] using hinitialHistorical
    · have hpreFinal : B.preReturn.2 = finalState := by
        calc
          B.preReturn.2 =
              B.toSupported.action.apply B.activatedState := hpreAction
          _ = finalState := by
            rw [haction, B.toSupported.action.involutive]
      simpa [hpreFinal] using hpreHistorical
  have hBfinalHistorical : VectorCount.restrict N
      (B.toSupported.action.apply finalState) ∈ history := by
    rcases hrelation with heq | haction
    · have hpreB : B.preReturn.2 =
          B.toSupported.action.apply finalState := by
        rw [hpreAction, heq]
      simpa [hpreB] using hpreHistorical
    · simpa [haction] using hinitialHistorical
  have hAorBAHistorical :
      VectorCount.restrict N
          (A.toSupported.action.apply finalState) ∈ history ∨
        VectorCount.restrict N
          (B.toSupported.action.apply
            (A.toSupported.action.apply finalState)) ∈ history := by
    rcases hrelation with heq | haction
    · right
      have hpreB : B.preReturn.2 =
          B.toSupported.action.apply finalState := by
        rw [hpreAction, heq]
      have hcorner :
          B.toSupported.action.apply
              (A.toSupported.action.apply finalState) =
            A.toSupported.action.apply B.preReturn.2 := by
        calc
          B.toSupported.action.apply
              (A.toSupported.action.apply finalState) =
              A.toSupported.action.apply
                (B.toSupported.action.apply finalState) :=
            (A.toSupported.action.commute B.toSupported.action
              finalState).symm
          _ = A.toSupported.action.apply B.preReturn.2 := by rw [hpreB]
      simpa [hcorner] using haPreHistorical
    · left
      have hpreFinal : B.preReturn.2 = finalState := by
        calc
          B.preReturn.2 =
              B.toSupported.action.apply B.activatedState := hpreAction
          _ = finalState := by
            rw [haction, B.toSupported.action.involutive]
      simpa [hpreFinal] using haPreHistorical
  have closeWithOne
      (freshState : Tongues)
      (hAcovered : VectorCount.restrict N
        (A.toSupported.action.apply finalState) ∈
          history ++ [VectorCount.restrict N freshState])
      (hBAcovered : VectorCount.restrict N
        (B.toSupported.action.apply
          (A.toSupported.action.apply finalState)) ∈
          history ++ [VectorCount.restrict N freshState]) :
      NoveltyCoverOn w N (g, B.activatedState) times history 1 := by
    have hcornerCover : ∀ phase ∈
        manufacturedPairActionCorners A B finalState,
        VectorCount.restrict N phase ∈
          history ++ [VectorCount.restrict N freshState] := by
      intro phase hp
      simp only [manufacturedPairActionCorners, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact List.mem_append_left _ hfinalHistorical
      · exact hAcovered
      · exact List.mem_append_left _ hBfinalHistorical
      · exact hBAcovered
    refine ⟨[VectorCount.restrict N freshState], by simp, ?_⟩
    intro k hk
    by_cases hkpre : k ≤ L
    · obtain ⟨port, phase, hrun, hphase⟩ := hprefixPhase k hkpre
      have hvec : restrictedTonguesAt w N (g, B.activatedState) k =
          VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hrun]
      rw [hvec]
      rcases hphase with h | h
      · apply List.mem_append_left
        simpa [h] using hinitialHistorical
      · apply List.mem_append_left
        simpa [h] using hfinalHistorical
    · let d := k - L
      have hkEq : k = L + d := by
        dsimp [d]
        omega
      have hkLive := hlive k hk
      have htailLive : ∃ finish, stepN w d endpoint = some finish := by
        rw [hkEq, stepN_add, hrepairReach] at hkLive
        simp only [Option.bind_some] at hkLive
        cases htail : stepN w d endpoint with
        | none => simp [htail] at hkLive
        | some finish => exact ⟨finish, rfl⟩
      have hmem := manufactured_pair_reached_action_corners_tongues
        A B finalState hAfinal hBfinal hpairReach htailLive
      have hshift := tonguesAt_add_of_reaches hrepairReach htailLive
      have hvector : restrictedTonguesAt w N
          (g, B.activatedState) k =
            VectorCount.restrict N (tonguesAt w endpoint d) := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      have hcovered := hcornerCover (tonguesAt w endpoint d) hmem
      simpa [hvector] using hcovered
  rcases hAorBAHistorical with hAHistorical | hBAHistorical
  · apply closeWithOne
      (B.toSupported.action.apply
        (A.toSupported.action.apply finalState))
    · exact List.mem_append_left _ hAHistorical
    · simp
  · apply closeWithOne (A.toSupported.action.apply finalState)
    · simp
    · exact List.mem_append_left _ hBAHistorical

/-- In the completed-repair outcome, making the old action mouth the last
productive writer therefore lowers the repair tail from two fresh vectors
to one. -/
theorem ManufacturedFlipReflector.completed_protected_route_one_novelty_of_last
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      ((ManufacturedReflector.flip R).orientedRoute B.activatedState)
      ((ManufacturedReflector.flip R).orientedFinish B.activatedState,
        finalState))
    (hAfinal : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (hlast : ∀ j, t < j → j < B.exploration.length →
      ¬ RawProductiveAt w N (e, B.baseState) j)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times
      ((ManufacturedReflector.flip R).preservedTwoHistoryCore B N) 1 := by
  refine (ManufacturedReflector.flip R).completed_protected_route_one_novelty_of_action_preReturn
    B hA hB hrepair hAfinal hBfinal
      ((ManufacturedReflector.flip R).preservedTwoHistoryCore B N)
      ?_ ?_ ?_ times hlive
  · apply (ManufacturedReflector.flip R).mem_preservedTwoHistoryCore B
    right
    simp [ManufacturedReflector.sharpConstructionHistory]
  · exact (ManufacturedReflector.flip R).preReturn_mem_preservedTwoHistoryCore B
  · simpa [ManufacturedReflector.toSupported,
      ManufacturedFlipReflector.toSupported, LocalAction.apply] using
        R.flipped_preReturn_mem_preservedHistory_of_last
          hN B ht hwriter hlast

/-- The completed protected repair has one-vector novelty as soon as the
old action switch is productively written by the second construction.  The
physical endpoint-groove argument above supplies the former `hlast`
hypothesis. -/
theorem ManufacturedFlipReflector.completed_protected_route_one_novelty_of_action_writer
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      ((ManufacturedReflector.flip R).orientedRoute B.activatedState)
      ((ManufacturedReflector.flip R).orientedFinish B.activatedState,
        finalState))
    (hAfinal : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    {t : Nat}
    (ht : t ∈ rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length)
    (hwriter : rawWriterAt w (e, B.baseState) t = R.actionSwitch)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    NoveltyCoverOn w N (g, B.activatedState) times
      ((ManufacturedReflector.flip R).preservedTwoHistoryCore B N) 1 := by
  apply R.completed_protected_route_one_novelty_of_last
    hN B hA hB hrepair hAfinal hBfinal ht hwriter
  · exact R.action_writer_is_last_productive
      hN B hA hpre ht hwriter
  · exact hlive

private theorem protectedPair_nodup_map_filter
    {α : Type} [BEq α] [LawfulBEq α]
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            apply hnd.1
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

/-- Generic two-journey bookkeeping over an arbitrary shared history.
The two manufacturing journeys contribute no vector outside `history`; a
tail novelty cover over the same history therefore gives the exact sum
`history.length + budget`.  The tail callback receives the shifted sample's
`Nodup` certificate, derived here from the original one. -/
theorem ManufacturedReflector.two_journeys_then_shared_history_novelty_count
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (history : List (List Bool))
    (hhistory : ∀ x,
      x ∈ A.sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N → x ∈ history)
    (budget : Nat)
    (htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
      NoveltyCoverOn w N (g, B.activatedState) tailTimes
        history budget)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ history.length + budget := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let localTimes :=
    (times.filter (fun k => decide (totalTravel < k))).map
      (fun k => k - totalTravel)
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hApaths
  have hreachB : stepN w secondTravel (e, A.activatedState) =
      some (g, B.activatedState) := by
    have h := B.manufacturing_journey_reaches_activated hBpaths
    simpa [secondTravel, hbase] using h
  have hreachTotal : stepN w totalTravel (g, A.baseState) =
      some (g, B.activatedState) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hprefixCover : ∀ d, d ≤ totalTravel →
      restrictedTonguesAt w N (g, A.baseState) d ∈ history := by
    intro d hd
    by_cases hfirst : d ≤ firstTravel
    · apply hhistory
      left
      exact A.manufacturing_journey_mem_sharpHistory
        hApaths (by simpa [firstTravel] using hfirst)
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q ≤ secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift := tonguesAt_add_of_reaches hreachA hliveQ
      have hm := B.manufacturing_journey_mem_sharpHistory
        (N := N) hBpaths (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm' : restrictedTonguesAt w N (e, A.activatedState) q ∈
          B.sharpConstructionHistory N := by
        simpa [hbase] using hm
      have heq : restrictedTonguesAt w N (g, A.baseState) d =
          restrictedTonguesAt w N (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      exact hhistory _ (Or.inr hm')
  have hlocalLive : ∀ d ∈ localTimes,
      (stepN w d (g, B.activatedState)).isSome := by
    intro d hd
    obtain ⟨k, hkFiltered, rfl⟩ := List.mem_map.mp hd
    have hk := (List.mem_filter.mp hkFiltered).1
    have hkGt : totalTravel < k := by
      have := (List.mem_filter.mp hkFiltered).2
      simpa using this
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hk
    rw [hkEq, stepN_add, hreachTotal] at hkLive
    exact hkLive
  have hlocalVector : localTimes.map
      (restrictedTonguesAt w N (g, B.activatedState)) =
      (times.filter (fun k => decide (totalTravel < k))).map
        (restrictedTonguesAt w N (g, A.baseState)) := by
    dsimp [localTimes]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
    have hkGt : totalTravel < k := by
      have := (List.mem_filter.mp hk).2
      simpa using this
    have hkEq : k = totalTravel + (k - totalTravel) := by omega
    have hkLive := hlive k hkTimes
    cases htailRun : stepN w (k - totalTravel)
        (g, B.activatedState) with
    | none =>
        have hglobalNone : stepN w k (g, A.baseState) = none := by
          rw [hkEq, stepN_add, hreachTotal]
          simp [htailRun]
        rw [hglobalNone] at hkLive
        simp at hkLive
    | some finish =>
        have hshift := tonguesAt_add_of_reaches
          hreachTotal ⟨finish, htailRun⟩
        have hstartEq : tonguesAt w (g, A.baseState)
            (totalTravel + (k - totalTravel)) =
            tonguesAt w (g, A.baseState) k := by
          rw [← hkEq]
        unfold restrictedTonguesAt
        exact congrArg (VectorCount.restrict N)
          (hshift.symm.trans hstartEq)
  have hfilteredNodup :
      ((times.filter (fun k => decide (totalTravel < k))).map
        (restrictedTonguesAt w N (g, A.baseState))).Nodup :=
    protectedPair_nodup_map_filter _ hnd
  have hlocalNodup :
      (localTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup := by
    rw [hlocalVector]
    exact hfilteredNodup
  have hlocalCover : NoveltyCoverOn w N
      (g, B.activatedState) localTimes history budget :=
    htail localTimes hlocalLive hlocalNodup
  obtain ⟨fresh, hfresh, hlocalMem⟩ := hlocalCover
  have hglobalCover : NoveltyCoverOn w N (g, A.baseState)
      times history budget := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hprefix : k ≤ totalTravel
    · exact List.mem_append_left _ (hprefixCover k hprefix)
    · have hkGt : totalTravel < k := by omega
      let d := k - totalTravel
      have hkEq : k = totalTravel + d := by
        dsimp [d]
        omega
      have hkFiltered : k ∈
          times.filter (fun t => decide (totalTravel < t)) := by
        apply List.mem_filter.mpr
        exact ⟨hk, by simp [hkGt]⟩
      have hdMem : d ∈ localTimes := by
        dsimp [localTimes]
        exact List.mem_map.mpr ⟨k, hkFiltered, rfl⟩
      have hlocalReach : ∃ finish,
          stepN w d (g, B.activatedState) = some finish :=
        Option.isSome_iff_exists.mp (hlocalLive d hdMem)
      have hshift := tonguesAt_add_of_reaches hreachTotal hlocalReach
      have hvector : restrictedTonguesAt w N (g, A.baseState) k =
          restrictedTonguesAt w N (g, B.activatedState) d := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [hvector]
      exact hlocalMem d hdMem
  exact noveltyCoverOn_distinct_count hglobalCover hnd

/-- Generic two-journey bookkeeping for a direct finite tail bound.  The
tail's time-zero vector is already represented by the second construction
history, so a direct `cap`-state tail spends only `cap - 1` vectors beyond
the supplied shared history. -/
theorem ManufacturedReflector.two_journeys_then_shared_history_direct_count
    {w : Wiring} {N g e cap : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (history : List (List Bool))
    (hhistory : ∀ x,
      x ∈ A.sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N → x ∈ history)
    (htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
      tailTimes.length ≤ cap)
    (hcap : 0 < cap)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ history.length + (cap - 1) := by
  let firstTravel := A.exploration.length + A.runway.length + 1
  let secondTravel := B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  have hreachA : stepN w firstTravel (g, A.baseState) =
      some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hApaths
  have hreachB : stepN w secondTravel (e, A.activatedState) =
      some (g, B.activatedState) := by
    have h := B.manufacturing_journey_reaches_activated hBpaths
    simpa [secondTravel, hbase] using h
  have hreachTotal : stepN w totalTravel (g, A.baseState) =
      some (g, B.activatedState) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hprefixCover : ∀ d, d ≤ totalTravel →
      restrictedTonguesAt w N (g, A.baseState) d ∈ history := by
    intro d hd
    by_cases hfirst : d ≤ firstTravel
    · apply hhistory
      left
      exact A.manufacturing_journey_mem_sharpHistory
        hApaths (by simpa [firstTravel] using hfirst)
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q ≤ secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift := tonguesAt_add_of_reaches hreachA hliveQ
      have hm := B.manufacturing_journey_mem_sharpHistory
        (N := N) hBpaths (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm' : restrictedTonguesAt w N (e, A.activatedState) q ∈
          B.sharpConstructionHistory N := by
        simpa [hbase] using hm
      have heq : restrictedTonguesAt w N (g, A.baseState) d =
          restrictedTonguesAt w N (e, A.activatedState) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      exact hhistory _ (Or.inr hm')
  have hboundary : VectorCount.restrict N B.activatedState ∈ history := by
    apply hhistory
    right
    simp [ManufacturedReflector.sharpConstructionHistory]
  have hcover := boundary_history_then_direct_tail_cover
    hreachTotal history hprefixCover hboundary htail hcap
      times hlive hnd
  exact noveltyCoverOn_distinct_count hcover hnd

/-- A stay reflector pays no omitted-mouth surcharge, so the ordinary
protected history already has size `N+2`. -/
theorem ManufacturedStayReflector.protectedHistory_length_le_N_add_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = (ManufacturedReflector.stay R).activatedState)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2) :
    ((ManufacturedReflector.stay R).preservedTwoHistoryCore B N).length ≤
      N + 2 := by
  let A : ManufacturedReflector w g e := .stay R
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.writerConstructionHistory N := by
    dsimp [A]
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge := A.reusable_add_second_first_writers_le
    hN B hbaseGrooves hpreGrooves
  have heq : A.exploration.length = A.reusableSwitches.length := by
    simp [A, ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length, B.writerConstructionHistory_length]
  omega

/-- **Unconditional protected-history dichotomy.**

Either both manufacturing journeys have a cover of size `N+2`, or the
first reflector is a flip reflector and its omitted facing mouth is a
productive first writer of the second construction with a strictly earlier
productive event.  Thus the residual is not an unspecified cardinality
gap: it is exactly an interior writer-order obstruction. -/
theorem protected_pair_history_N_add_two_or_prior_action_writer
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves A.toSupported.paths B.preReturn.2) :
    (∃ history : List (List Bool),
      history.length ≤ N + 2 ∧
      ∀ x, x ∈ A.sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N → x ∈ history) ∨
    (∃ (R : ManufacturedFlipReflector w g e) (t j : Nat),
      A = .flip R ∧
      t ∈ rawFirstWriterTimes w N (e, B.baseState)
        B.exploration.length ∧
      rawWriterAt w (e, B.baseState) t = R.actionSwitch ∧
      j < t ∧ RawProductiveAt w N (e, B.baseState) j) := by
  cases hkind : A with
  | stay R =>
      apply Or.inl
      refine ⟨A.preservedTwoHistoryCore B N, ?_, ?_⟩
      · have hlen := R.protectedHistory_length_le_N_add_two
          hN B (by simpa [hkind] using hbase)
          (by simpa [hkind] using hbaseGrooves)
          (by simpa [hkind] using hpreGrooves)
        simpa [hkind] using hlen
      · intro x hx
        have hm := (ManufacturedReflector.stay R).mem_preservedTwoHistoryCore
          B hx
        simpa [hkind] using hm
  | flip R =>
      have hbaseR :
          B.baseState = (ManufacturedReflector.flip R).activatedState := by
        simpa [hkind] using hbase
      have hbaseGroovesR : PathGrooves
          (ManufacturedReflector.flip R).toSupported.paths B.baseState := by
        simpa [hkind] using hbaseGrooves
      have hpreGroovesR : PathGrooves
          (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2 := by
        simpa [hkind] using hpreGrooves
      by_cases haction : R.actionSwitch ∈
          B.constructionFirstWriterSwitches N
      · unfold ManufacturedReflector.constructionFirstWriterSwitches at haction
        obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp haction
        by_cases hprior : ∃ j, j < t ∧
            RawProductiveAt w N (e, B.baseState) j
        · obtain ⟨j, hj, hprod⟩ := hprior
          exact Or.inr ⟨R, t, j, rfl, ht, hwriter, hj, hprod⟩
        · apply Or.inl
          refine ⟨R.firstQuietProtectedHistory B N, ?_, ?_⟩
          · exact R.firstQuietProtectedHistory_length_le_N_add_two
              hN B hbaseR hbaseGroovesR hpreGroovesR ht hwriter
                (fun j hj hprod => hprior ⟨j, hj, hprod⟩)
          · intro x hx
            simpa [hkind] using R.mem_firstQuietProtectedHistory B hx
      · apply Or.inl
        refine ⟨A.preservedTwoHistoryCore B N, ?_, ?_⟩
        · have hlen := (ManufacturedReflector.flip R).preservedTwoHistoryCore_length_le_N_add_two_of_reserved
              hN B hbaseR hbaseGroovesR hpreGroovesR
                (R.action_lt hN)
                (fun hmem => R.action_not_mem_reusable hmem)
                (fun hmem => haction hmem)
          simpa [hkind] using hlen
        · intro x hx
          have hm := (ManufacturedReflector.flip R).mem_preservedTwoHistoryCore
            B hx
          simpa [hkind] using hm

/-- **Completed protected pair, exact `N+4`.**

This is the requested coefficient-one combination.  If the two construction
histories compress to `N+2`, the existing two-vector protected tail closes
the count.  Otherwise the first reflector is a flip whose action switch is
written during the second construction.  The physical retrace theorem makes
that write last, so the completed tail has only one fresh vector over the
ordinary `N+3` history. -/
theorem ManufacturedReflector.completed_protected_pair_all_run_distinct_le_N_add_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 4 := by
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  rcases protected_pair_history_N_add_two_or_prior_action_writer
      hN A B hbase hAatBase hpre with hsmall | haction
  · obtain ⟨history, hhistoryLen, hhistory⟩ := hsmall
    have hinitialHistorical :
        VectorCount.restrict N B.activatedState ∈ history := by
      apply hhistory
      right
      simp [ManufacturedReflector.sharpConstructionHistory]
    have hpreHistorical :
        VectorCount.restrict N B.preReturn.2 ∈ history := by
      apply hhistory
      right
      unfold ManufacturedReflector.sharpConstructionHistory
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨B.exploration.length,
        List.mem_range.mpr (by omega), ?_⟩
      simp [restrictedTonguesAt, tonguesAt,
        B.exploration_trace.sound]
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (g, B.activatedState)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
        NoveltyCoverOn w N (g, B.activatedState) tailTimes
          history 2 := by
      intro tailTimes htailLive _htailNodup
      exact A.completed_protected_route_two_novelty_of_preReturn
        B hAatBase hBpaths hrepair hAfinal hBfinal history
        hinitialHistorical hpreHistorical tailTimes htailLive
    have hcount := A.two_journeys_then_shared_history_novelty_count
      B hbase hApaths hBpaths history hhistory 2 htail
        times hlive hnd
    omega
  · obtain ⟨R, t, _prior, hAeq, ht, hwriter,
        _hprior, _hpriorProd⟩ := haction
    subst A
    let history :=
      (ManufacturedReflector.flip R).preservedTwoHistoryCore B N
    have hhistory : ∀ x,
        x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N ∨
          x ∈ B.sharpConstructionHistory N → x ∈ history := by
      intro x hx
      dsimp [history]
      exact (ManufacturedReflector.flip R).mem_preservedTwoHistoryCore B hx
    have hhistoryLen : history.length ≤ N + 3 := by
      dsimp [history]
      exact (ManufacturedReflector.flip R).preservedTwoHistoryCore_length_le_N_add_three
        hN B hbase hAatBase hpre
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (g, B.activatedState)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
        NoveltyCoverOn w N (g, B.activatedState) tailTimes
          history 1 := by
      intro tailTimes htailLive _htailNodup
      dsimp [history]
      exact R.completed_protected_route_one_novelty_of_action_writer
        hN B hAatBase hpre hBpaths hrepair hAfinal hBfinal
          ht hwriter tailTimes htailLive
    have hcount :=
      (ManufacturedReflector.flip R).two_journeys_then_shared_history_novelty_count
        B hbase hApaths hBpaths history hhistory 1 htail
          times hlive hnd
    omega

/-- **Fully protected opposite-reflector pair, exact raw `N+4`.**

This theorem covers every constructor of
`manufactured_pair_protected_repair_constant_outcomes`.  The strengthened
classifier charges every early count or facing outcome by one vector.  A
changed-forward outcome is incompatible with `hpre`; a completed repair
uses two vectors over an `N+2` history, or one vector over the `N+3`
prior-action-writer history. -/
theorem ManufacturedReflector.preReturn_grooved_protected_pair_all_run_distinct_le_N_add_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 4 := by
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  rcases protected_pair_history_N_add_two_or_prior_action_writer
      hN A B hbase hAatBase hpre with hsmall | haction
  · obtain ⟨history, hhistoryLen, hhistory⟩ := hsmall
    have hinitialHistorical :
        VectorCount.restrict N B.activatedState ∈ history := by
      apply hhistory
      right
      simp [ManufacturedReflector.sharpConstructionHistory]
    have hpreHistorical :
        VectorCount.restrict N B.preReturn.2 ∈ history := by
      apply hhistory
      right
      unfold ManufacturedReflector.sharpConstructionHistory
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨B.exploration.length,
        List.mem_range.mpr (by omega), ?_⟩
      simp [restrictedTonguesAt, tonguesAt,
        B.exploration_trace.sound]
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (g, B.activatedState)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
        NoveltyCoverOn w N (g, B.activatedState) tailTimes
          history 2 := by
      intro tailTimes htailLive htailNodup
      rcases manufactured_pair_protected_repair_novelty_outcomes
          A B hAatBase hBpaths history hinitialHistorical
            hpreHistorical with hone | hfacing | hchanged | hcomplete
      · obtain ⟨fresh, hfresh, hmem⟩ :=
          hone tailTimes htailLive htailNodup
        exact ⟨fresh, by omega, hmem⟩
      · obtain ⟨fresh, hfresh, hmem⟩ :=
          hfacing.one_novelty_of_preReturn hN hAatBase hBpaths
            history hinitialHistorical hpreHistorical
              tailTimes htailLive
        exact ⟨fresh, by omega, hmem⟩
      · exact (hchanged.impossible_of_preReturn_grooved
          hBpaths hpre).elim
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact A.completed_protected_route_two_novelty_of_preReturn
          B hAatBase hBpaths hrepair hAfinal hBfinal history
            hinitialHistorical hpreHistorical tailTimes htailLive
    have hcount := A.two_journeys_then_shared_history_novelty_count
      B hbase hApaths hBpaths history hhistory 2 htail
        times hlive hnd
    omega
  · obtain ⟨R, t, _prior, hAeq, ht, hwriter,
        _hprior, _hpriorProd⟩ := haction
    subst A
    let history :=
      (ManufacturedReflector.flip R).preservedTwoHistoryCore B N
    have hhistory : ∀ x,
        x ∈ (ManufacturedReflector.flip R).sharpConstructionHistory N ∨
          x ∈ B.sharpConstructionHistory N → x ∈ history := by
      intro x hx
      dsimp [history]
      exact (ManufacturedReflector.flip R).mem_preservedTwoHistoryCore B hx
    have hhistoryLen : history.length ≤ N + 3 := by
      dsimp [history]
      exact (ManufacturedReflector.flip R).preservedTwoHistoryCore_length_le_N_add_three
        hN B hbase hAatBase hpre
    have hinitialHistorical :
        VectorCount.restrict N B.activatedState ∈ history := by
      apply hhistory
      right
      simp [ManufacturedReflector.sharpConstructionHistory]
    have hpreHistorical :
        VectorCount.restrict N B.preReturn.2 ∈ history := by
      apply hhistory
      right
      unfold ManufacturedReflector.sharpConstructionHistory
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨B.exploration.length,
        List.mem_range.mpr (by omega), ?_⟩
      simp [restrictedTonguesAt, tonguesAt,
        B.exploration_trace.sound]
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (g, B.activatedState)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
        NoveltyCoverOn w N (g, B.activatedState) tailTimes
          history 1 := by
      intro tailTimes htailLive htailNodup
      rcases manufactured_pair_protected_repair_novelty_outcomes
          (ManufacturedReflector.flip R) B hAatBase hBpaths
            history hinitialHistorical hpreHistorical with
        hone | hfacing | hchanged | hcomplete
      · exact hone tailTimes htailLive htailNodup
      · exact hfacing.one_novelty_of_preReturn
          hN hAatBase hBpaths history hinitialHistorical
            hpreHistorical tailTimes htailLive
      · exact (hchanged.impossible_of_preReturn_grooved
          hBpaths hpre).elim
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        dsimp [history]
        exact R.completed_protected_route_one_novelty_of_action_writer
          hN B hAatBase hpre hBpaths hrepair hAfinal hBfinal
            ht hwriter tailTimes htailLive
    have hcount :=
      (ManufacturedReflector.flip R).two_journeys_then_shared_history_novelty_count
        B hbase hApaths hBpaths history hhistory 1 htail
          times hlive hnd
    omega

/-- The literal fully-protected residual exposed by the known-edge probe is
bounded by the direct protected-pair theorem above. -/
theorem KnownEdgeFullyProtectedPair.all_run_distinct_le_N_add_four
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (D : KnownEdgeFullyProtectedPair w e start)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 4 := by
  have hliveA : ∀ k ∈ times,
      (stepN w k (start.1, D.pair.A.baseState)).isSome := by
    simpa [D.pair.A_base] using hlive
  have hndA : (times.map
      (restrictedTonguesAt w N
        (start.1, D.pair.A.baseState))).Nodup := by
    simpa [D.pair.A_base] using hnd
  exact D.pair.A.preReturn_grooved_protected_pair_all_run_distinct_le_N_add_four
    hN D.pair.B D.pair.B_base D.pair.A_grooves
      D.pair.B_grooves D.preGrooves times hliveA hndA

/-- **Unconditional known-edge protected-pair law, exact raw `N+4`.**
Broken pre-return support is the already-closed changed-contact branch;
fully protected support is the theorem above. -/
theorem knownEdgeProtectedPairNAddFourLaw :
    KnownEdgeProtectedPairNAddFourLaw := by
  intro w N e hN start D times hlive hnd
  by_cases hpre : PathGrooves D.A.toSupported.paths D.B.preReturn.2
  · let F : KnownEdgeFullyProtectedPair w e start := {
      pair := D
      preGrooves := hpre
    }
    exact F.all_run_distinct_le_N_add_four hN times hlive hnd
  · have htrace : PhysicalTrace w (e, D.A.activatedState)
        D.B.exploration D.B.preReturn := by
      simpa [D.B_base] using D.B.exploration_trace
    obtain ⟨S⟩ := D.A.simpleContinuationChangedContact
      D.A_grooves htrace D.B.exploration_simple hpre
    let C := S.toSharpChangedContact
    have hliveA : ∀ k ∈ times,
        (stepN w k (start.1, D.A.baseState)).isSome := by
      simpa [D.A_base] using hlive
    have hndA : (times.map
        (restrictedTonguesAt w N
          (start.1, D.A.baseState))).Nodup := by
      simpa [D.A_base] using hnd
    exact C.all_run_distinct_le_N_add_four
      hN D.A_grooves times hliveA hndA

end GeneralN
