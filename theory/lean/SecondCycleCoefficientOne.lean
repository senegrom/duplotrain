import StateLawCoefficientOneTop
import TraceRetainingFirstRevisit
import TraceRetainingBABASecondRepeat
import PointwiseSimpleCycleTail
import MellitDynamicResidual
import FirstChangedSupportTail
import OldContactContinuation
import OneReflectorContinuation

/-!
# Coefficient-one accounting for the second stable-cycle branch

After one completed manufactured reflector, the sharp second first-revisit
certificate consists of a switch-simple lead followed by a stable
switch-simple cycle.  If the lead is switch-disjoint from the first
reflector's exploration, the existing compressed first-history argument
gives an `N + 3` all-time bound.  If it is not disjoint, simplicity of the
lead rules out an internal fresh repeat: the canonical union repeat is an
actual old-support contact, retained as `UnionOldTrackedShrink`.

The final theorem below is deliberately honest about that remaining contact.
It is coefficient one on the closed branch and exposes the exact physical
residual on the open branch; it does not fall back to a coefficient-two
estimate.
-/

namespace GeneralN

/-- A switch-simple fresh trace cannot have an internal union repeat. -/
theorem UnionFirstRepeat.internal_false_of_fresh_simple
    {old fresh : List Passage}
    (R : UnionFirstRepeat old fresh)
    (hfresh : SwitchSimple fresh)
    (hinternal : passageSwitch R.repeated ∈
      R.before.map passageSwitch) : False := by
  unfold SwitchSimple at hfresh
  rw [R.split] at hfresh
  simp only [List.map_append, List.map_cons] at hfresh
  have hparts := List.nodup_append.mp hfresh
  have hrepeated : List.Mem (passageSwitch R.repeated)
      (passageSwitch R.repeated :: R.after.map passageSwitch) := by
    exact List.mem_cons_self
  exact (hparts.2.2 _ hinternal _ hrepeated) rfl

/-- If the old exploration and a switch-simple fresh trace are not jointly
simple, their canonical first union repeat is a concrete old-support contact
with the tracked strict shrink retained. -/
theorem ManufacturedReflector.old_shrink_of_fresh_simple_union_nonsimple
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage} {finish : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (htrace : PhysicalTrace w (e, A.activatedState) fresh finish)
    (hfresh : SwitchSimple fresh)
    (hunion : ¬ SwitchSimple (A.exploration ++ fresh)) :
    Nonempty (UnionOldTrackedShrink w N A fresh finish) := by
  obtain ⟨R⟩ := first_repeat_against_union
    A.exploration fresh A.exploration_simple hunion
  rcases R.old_or_internal with hold | hinternal
  · have hRange : ∀ passage, passage ∈ A.exploration →
        passageSwitch passage < N := by
      intro passage hpassage
      exact A.exploration_trace.switch_lt hN passage hpassage
    obtain ⟨S⟩ := htrace.union_old_contact_shrink R hRange hold
    exact ⟨{
      selection := R
      raw := S
    }⟩
  · exact (R.internal_false_of_fresh_simple hfresh hinternal).elim

/-- Joint simplicity makes every passage of the second lead foreign to each
reusable support passage of the first reflector. -/
theorem ManufacturedReflector.support_grooves_after_jointly_simple_fresh
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage} {finish : Nat × Tongues}
    (htrace : PhysicalTrace w (e, A.activatedState) fresh finish)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hjoint : SwitchSimple (A.exploration ++ fresh)) :
    PathGrooves A.toSupported.paths finish.2 := by
  have hparts := List.nodup_append.mp (by
    simpa only [SwitchSimple, List.map_append] using hjoint)
  have hforeign : ∀ newPassage ∈ fresh,
      ∀ path ∈ A.toSupported.paths, ∀ oldPassage ∈ path,
        passageSwitch newPassage ≠ passageSwitch oldPassage := by
    intro newPassage hnew path hpath oldPassage hold hEq
    have hOld : passageSwitch oldPassage ∈
        A.exploration.map passageSwitch :=
      A.support_switch_mem_exploration hpath hold
    have hNew : passageSwitch newPassage ∈
        fresh.map passageSwitch :=
      List.mem_map.mpr ⟨newPassage, hnew, rfl⟩
    exact (hparts.2.2 _ hOld _ hNew) hEq.symm
  exact pathGrooves_preserved_by_foreign_trace
    htrace hA hforeign

/-- **Second stable-cycle coefficient-one dichotomy.**

Start at the base of a completed first reflector `A`.  Let `C` be the
trace-retained stable-cycle outcome of the second first-revisit search.  For
every live list of pairwise-distinct raw tongue vectors, either the complete
run has at most `N + 3` vectors, or the second lead has a concrete first
contact with the old exploration and carries the strict tracked shrink.

Thus the stable-cycle branch itself costs only a constant after the shared
coefficient-one construction history.  The only unclosed case is the
physical old-support continuation, not a coefficient-two counting loss. -/
theorem FirstActivatedCycleOutcome.second_cycle_distinct_le_N_add_three_or_old_shrink
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (C : FirstActivatedCycleOutcome w (e, A.activatedState) N)
    (times : List Nat)
    (hlive : ∀ k, k ∈ times →
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 3 ∨
      Nonempty (UnionOldTrackedShrink w N A C.lead C.atRepeat) := by
  by_cases hjoint : SwitchSimple (A.exploration ++ C.lead)
  · left
    have hend : PathGrooves A.toSupported.paths C.atRepeat.2 :=
      A.support_grooves_after_jointly_simple_fresh
        C.lead_trace hA hjoint
    exact C.preserved_all_run_distinct_le_N_add_three
      hN A hA hend times hlive hnd
  · right
    exact A.old_shrink_of_fresh_simple_union_nonsimple
      hN C.lead_trace C.lead_simple hjoint

/-! ## Arbitrary partial forward contact

The completed-reflector forward-splice theorem only uses simplicity of the
trace before the changing passage.  The following record and theorem expose
the same physical lobe for an arbitrary simple continuation.
-/

structure SimpleForwardActiveLead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A) : Type where
  entry : Nat
  mouth : Nat
  returnPort : Nat
  outside : Nat
  oldPrefix : List Passage
  oldTail : List Passage
  candy : List Passage
  tailSteps : Nat
  entryOld :
    List.Mem (entry, mouth) (A.orientedRoute C.contactState)
  routeSplit :
    A.orientedRoute C.contactState =
      oldPrefix ++ (entry, mouth) :: oldTail
  oldTailTrace :
    PhysicalTrace w (outside, C.contactState) oldTail
      (A.orientedFinish C.contactState, C.contactState)
  approachReplay :
    PhysicalTrace w (e, C.contactState) C.approach
      (returnPort, C.contactState)
  approachSimple : SwitchSimple C.approach
  approachGrooved : PassagesGrooved C.contactState C.approach
  approachForeign : forall passage,
    List.Mem passage C.approach ->
      Not (passageSwitch passage = mouth / 3)
  candyEq : candy = reversePassages oldPrefix ++ C.approach
  entryBranch : Not (entry % 3 = 0)
  mouthStem : mouth % 3 = 0
  mouthLink : w.link mouth = some outside
  armsNe : Not (entry = returnPort)
  fullGrooved :
    PassagesGrooved C.contactState ((mouth, entry) :: candy)
  fullTrace :
    PhysicalTrace w (mouth, C.contactState)
      ((mouth, entry) :: candy) (returnPort, C.contactState)
  crossed :
    arrive C.contactState returnPort =
      (mouth, flipAt C.contactState (mouth / 3))
  oldPaths : PathGrooves A.toSupported.paths C.contactState
  candyGrooved : PassagesGrooved C.contactState candy
  candyForeign : forall passage, List.Mem passage candy ->
    Not (passageSwitch passage = mouth / 3)
  lobe :
    IsReflector w mouth outside (candy.length + 2)
      (fun state => PassagesGrooved state candy)
      (fun state => flipAt state (mouth / 3))
  reach :
    stepN w (C.approach.length + 1) (e, A.activatedState) =
      some (outside, flipAt C.contactState (mouth / 3))
  complete :
    stepN w tailSteps (outside, C.contactState) =
      some (e, A.toSupported.action.apply C.contactState)

theorem SimpleContinuationChangedContact.forward_active_lead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (hforward : C.x = C.oriented.2) :
    Nonempty (SimpleForwardActiveLead C) := by
  let a := C.oriented.1
  let s := C.oriented.2
  have horiented :
      List.Mem (a, s) (A.orientedRoute C.contactState) := by
    change List.Mem C.oriented (A.orientedRoute C.contactState)
    exact C.oriented_mem
  have horientedGroove :
      arrive C.contactState s = (a, C.contactState) := by
    simpa [a, s] using C.oriented_groove
  have horientedSwitch :
      passageSwitch (a, s) = C.p / 3 := by
    simpa [a, s] using C.oriented_switch
  have harrive :
      arrive C.contactState C.p = (s, C.nextState) := by
    rw [C.arrive_eq, hforward]
  have htrail := changed_arrival_is_trailing harrive C.changed
  have hpBranch := htrail.1
  have hsEq := htrail.2.1
  have hsStem : s % 3 = 0 := by
    rw [hsEq]
    omega
  have hsp : s / 3 = C.p / 3 := by
    rw [hsEq]
    omega
  have hsa : s / 3 = a / 3 := by
    have hswitch := arrive_exit_switch C.contactState s
    rw [horientedGroove] at hswitch
    exact hswitch.symm
  have haBranch : Not (a % 3 = 0) := by
    have haEq :
        branchPort (s / 3) (C.contactState (s / 3)) = a := by
      unfold arrive at horientedGroove
      rw [if_pos hsStem] at horientedGroove
      exact congrArg Prod.fst horientedGroove
    intro haStem
    cases hu : C.contactState (s / 3) <;>
      simp [branchPort, hu] at haEq <;> omega
  have hap : Not (a = C.p) := by
    intro hEq
    have holdForward := groove_forward horientedGroove
    rw [hEq, harrive] at holdForward
    have huv : C.nextState = C.contactState :=
      congrArg Prod.snd holdForward
    apply C.changed
    rw [huv]
  obtain ⟨oldPrefix, oldTail, hrouteSplit⟩ :=
    List.append_of_mem horiented
  have hroute :=
    A.orientedRoute_trace C.contactState C.old_grooves
  have hrouteSimple :=
    A.orientedRoute_simple C.contactState
  have hrouteGrooved :=
    hroute.grooved_of_switchSimple hrouteSimple
  have hOldPrefixData :=
    simple_grooved_trace_prefix_to_occurrence
      hroute hrouteSplit hrouteGrooved hrouteSimple
  have hOldPrefixGrooved :
      PassagesGrooved C.contactState oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hrouteSplit]
      exact List.mem_append_left _ hp)
  have hApproachSimple : SwitchSimple C.approach :=
    C.approach_simple
  have hApproachGrooved :
      PassagesGrooved C.contactState C.approach :=
    C.approach_trace.grooved_of_switchSimple hApproachSimple
  have hApproachForeign : forall passage,
      List.Mem passage C.approach ->
        Not (passageSwitch passage = C.p / 3) := by
    have hsimple := C.full_simple
    unfold SwitchSimple at hsimple
    rw [C.split] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr (Exists.intro passage (And.intro hp rfl)))
      (passageSwitch (C.p, C.x)) (by simp)
    exact hne (by simpa [passageSwitch] using hEq)
  let candy := reversePassages oldPrefix ++ C.approach
  have hCandyGrooved :
      PassagesGrooved C.contactState candy := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    case inl =>
      exact reversePassages_grooved
        hOldPrefixGrooved passage hold
    case inr =>
      exact hApproachGrooved passage hnew
  have hCandyForeign : forall passage, List.Mem passage candy ->
      Not (passageSwitch passage = s / 3) := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    case inl =>
      have hmapped : List.Mem (passageSwitch passage)
          ((reversePassages oldPrefix).map passageSwitch) :=
        List.mem_map.mpr (Exists.intro passage (And.intro hold rfl))
      have hmap :=
        map_passageSwitch_reversePassages hOldPrefixData.1
      rw [hmap] at hmapped
      have horiginal : List.Mem (passageSwitch passage)
          (oldPrefix.map passageSwitch) :=
        List.mem_reverse.mp hmapped
      obtain ⟨old, holdMem, holdEq⟩ := List.mem_map.mp horiginal
      intro hmouth
      apply hOldPrefixData.2 old holdMem
      exact holdEq.trans (hmouth.trans hsa)
    case inr =>
      intro hmouth
      apply hApproachForeign passage hnew
      exact hmouth.trans hsp
  have hback := physicalTrace_contact_retraces_prefix
    hOldPrefixData.1 hOldPrefixGrooved A.entryEdge horientedGroove
  have hforwardTrace :=
    C.approach_trace.replay_grooved
      C.contactState hApproachGrooved
  have hsplice :
      PhysicalTrace w (s, C.contactState)
        ((s, a) :: candy) (C.p, C.contactState) := by
    simpa [candy, List.append_assoc] using
      hback.append hforwardTrace
  have hSpliceGrooved :
      PassagesGrooved C.contactState ((s, a) :: candy) := by
    intro passage hpassage
    rcases List.mem_cons.mp hpassage with hhead | htail
    case inl =>
      simpa [hhead] using groove_forward horientedGroove
    case inr =>
      exact hCandyGrooved passage htail
  have hroute' := hroute
  rw [hrouteSplit] at hroute'
  obtain ⟨middle, hOldBefore, hOldAfter⟩ := hroute'.split_append
  have hMiddle : middle = (a, C.contactState) := by
    have h1 := hOldBefore.sound
    have h2 := hOldPrefixData.1.sound
    rw [h2] at h1
    exact (Option.some.inj h1).symm
  subst middle
  cases hOldAfter with
  | @cons _ _ outside _ oldAfter _ _ hOldArrive hmouth hOldRest =>
      have hOldAfterState : oldAfter = C.contactState := by
        have hforwardOld := groove_forward horientedGroove
        rw [hOldArrive] at hforwardOld
        exact congrArg Prod.snd hforwardOld
      subst oldAfter
      have hcontactTrace :
          PhysicalTrace w (a, C.contactState) [(a, s)]
            (outside, C.contactState) :=
        PhysicalTrace.cons (groove_forward horientedGroove)
          hmouth (PhysicalTrace.nil _)
      have hlead := hOldPrefixData.1.append hcontactTrace
      have hleadSplit : A.orientedRoute C.contactState =
          (oldPrefix ++ [(a, s)]) ++ oldTail := by
        rw [hrouteSplit]
        simp [List.append_assoc]
      obtain ⟨tailSteps, _hlen, hcomplete⟩ :=
        A.complete_after_oriented_prefix C.contactState
          C.old_grooves hleadSplit hlead
      have hflip :
          C.nextState = flipAt C.contactState (s / 3) := by
        have hv :=
          changed_arrival_eq_flipAt C.arrive_eq C.changed
        simpa [hsp] using hv
      have hone :
          stepN w 1 (C.p, C.contactState) =
            some (outside, C.nextState) := by
        simp [stepN, step, harrive, hmouth]
      have hreach :
          stepN w (C.approach.length + 1)
              (e, A.activatedState) =
            some (outside, flipAt C.contactState (s / 3)) := by
        rw [stepN_add, C.approach_trace.sound]
        simp only [Option.bind_some]
        rw [hone, hflip]
      have hcrossed :
          arrive C.contactState C.p =
            (s, flipAt C.contactState (s / 3)) := by
        rw [harrive, hflip]
      exact Nonempty.intro {
        entry := a
        mouth := s
        returnPort := C.p
        outside := outside
        oldPrefix := oldPrefix
        oldTail := oldTail
        candy := candy
        tailSteps := tailSteps
        entryOld := horiented
        routeSplit := hrouteSplit
        oldTailTrace := hOldRest
        approachReplay := hforwardTrace
        approachSimple := hApproachSimple
        approachGrooved := hApproachGrooved
        approachForeign := by
          intro passage hpassage
          simpa [hsp] using hApproachForeign passage hpassage
        candyEq := rfl
        entryBranch := haBranch
        mouthStem := hsStem
        mouthLink := hmouth
        armsNe := hap
        fullGrooved := hSpliceGrooved
        fullTrace := hsplice
        crossed := hcrossed
        oldPaths := C.old_grooves
        candyGrooved := hCandyGrooved
        candyForeign := hCandyForeign
        lobe := stem_lobe_isReflector_foreign w candy
          hsStem haBranch hpBranch hsa hsp hap hCandyForeign
          hsplice.linked hsplice.last_link hmouth
        reach := hreach
        complete := hcomplete
      }

/-- A forward-changing partial continuation into a flip reflector has at
most two vectors outside its coefficient-one compressed lead. -/
theorem SimpleContinuationChangedContact.forward_flip_all_time_two_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.flip R))
    (hforward : C.x = C.oriented.2)
    (times : List Nat) :
    NoveltyCoverOn w N (e,
      (ManufacturedReflector.flip R).activatedState)
      times (C.compressedLead N) 2 := by
  let L := Classical.choice (C.forward_active_lead hforward)
  let K := C.approach.length + 1
  let state := C.contactState
  let alternate := flipAt state (L.mouth / 3)
  have hreach' :
      stepN w K (e,
        (ManufacturedReflector.flip R).activatedState) =
        some (L.outside, alternate) := by
    simpa [K, state, alternate] using L.reach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈
        C.compressedLead N := by
    simpa [hnextAlternate] using
      C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N state ∈
        C.compressedLead N := by
    simpa [state] using C.contact_mem_compressedLead (N := N)
  have hleadHistorical : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N
          (e, (ManufacturedReflector.flip R).activatedState) j ∈
        C.compressedLead N := by
    intro j _hj hjK
    exact C.mem_compressedLead_of_approach (N := N) (by
      dsimp [K] at hjK
      omega)
  by_cases hrunway :
      List.Mem (L.entry, L.mouth) R.runway
  case pos =>
    obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨D, _hDAction, hEntryOldNe, hDpaths,
        hNewAvoidsDRaw, _htravel⟩ :=
      R.suffix_after_runway_passage_with_travel state L.oldPaths
        hrunwaySplit L.mouthLink
    have hentrySwitch : L.entry / 3 = L.mouth / 3 := by
      have hheadGroove :
          arrive state L.entry = (L.mouth, state) :=
        L.fullGrooved (L.mouth, L.entry) List.mem_cons_self
      have hswitch := arrive_exit_switch state L.entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe :
        Not (L.mouth / 3 = D.actionSwitch) := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsD :
        (LocalAction.flip (L.mouth / 3)).Avoids
          D.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsDRaw
    by_cases hcontact : exists passage,
        And (List.Mem passage L.candy)
          (passageSwitch passage = D.actionSwitch)
    case pos =>
      apply manufactured_flip_arbitrary_lobe_absolute_two_novelty
        D state hDpaths hNewAvoidsD L.entryBranch hentrySwitch
        L.fullGrooved L.fullTrace L.crossed L.candyForeign L.lobe
        L.mouthLink hcontact hreach' times (C.compressedLead N)
        hentryHistorical hstateHistorical
      exact hleadHistorical
    case neg =>
      have hCandyForeignOld : forall passage,
          List.Mem passage L.candy ->
            Not (passageSwitch passage = D.actionSwitch) := by
        intro passage hp hEq
        exact hcontact (Exists.intro passage (And.intro hp hEq))
      apply manufactured_suffix_explicit_lobe_absolute_two_novelty
        D state hDpaths hNewAvoidsD hActionsNe L.entryBranch
        hentrySwitch L.fullGrooved L.fullTrace L.crossed
        L.candyForeign hCandyForeignOld L.lobe L.mouthLink
        hreach' times (C.compressedLead N) hentryHistorical
        hstateHistorical
      exact hleadHistorical
  case neg =>
    obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        L.entryOld hrunway L.entryBranch
    have hentryGrooved :
        arrive state L.entry = (L.mouth, state) :=
      L.fullGrooved (L.mouth, L.entry) List.mem_cons_self
    have hone :=
      manufactured_flip_candy_splice_absolute_one_novelty
        R state L.oldPaths L.routeSplit L.oldTailTrace
        hrunway L.entryBranch hold horientation hentryGrooved
        L.approachReplay L.approachGrooved L.approachForeign
        L.crossed L.mouthLink L.armsNe hreach' N
        (C.compressedLead N) hentryHistorical times
        hleadHistorical
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩
private theorem secondCycle_twoPhase_concat
    {w : Wiring} {start middle : Nat × Tongues}
    {left right : Nat} {u v : Tongues}
    (hleft : stepN w left start = some middle)
    (hleftPhase : ∀ d, d ≤ left → ∃ port phase,
      stepN w d start = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (hrightPhase : ∀ d, d ≤ right → ∃ port phase,
      stepN w d middle = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (d : Nat) (hd : d ≤ left + right) :
    ∃ port phase, stepN w d start = some (port, phase) ∧
      (phase = u ∨ phase = v) := by
  by_cases hdl : d ≤ left
  · exact hleftPhase d hdl
  · let r := d - left
    have hr : r ≤ right := by
      dsimp [r]
      omega
    have hdecomp : d = left + r := by
      dsimp [r]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hrightPhase r hr
    refine ⟨port, phase, ?_, hphase⟩
    rw [hdecomp, stepN_add, hleft]
    simpa using hrun

/-- The generic forward contact into a stay reflector has an exact two-phase
all-time tail. -/
theorem SimpleContinuationChangedContact.forward_stay_two_phase_tail
    {w : Wiring} {g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.stay R))
    (hforward : C.x = C.oriented.2) :
    ∃ outside mouth,
      stepN w (C.approach.length + 1)
          (e, (ManufacturedReflector.stay R).activatedState) =
        some (outside,
          flipAt C.contactState (mouth / 3)) ∧
      ∀ d, ∃ port phase,
        stepN w d
          (outside, flipAt C.contactState (mouth / 3)) =
            some (port, phase) ∧
        (phase = flipAt C.contactState (mouth / 3) ∨
          phase = C.contactState) := by
  let L := Classical.choice (C.forward_active_lead hforward)
  let k := L.mouth / 3
  let alternate := flipAt C.contactState k
  have hCandyFlip :
      PassagesGrooved alternate L.candy := by
    dsimp [alternate, k]
    exact grooved_after_flip_other
      L.candyGrooved L.candyForeign
  have hOldRoute :=
    (ManufacturedReflector.stay R).orientedRoute_trace
      C.contactState L.oldPaths
  have hOldSimple :=
    (ManufacturedReflector.stay R).orientedRoute_simple
      C.contactState
  have hOldGrooved :=
    hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward :
      arrive C.contactState L.entry =
        (L.mouth, C.contactState) :=
    groove_forward
      (hOldGrooved (L.entry, L.mouth) L.entryOld)
  have hentryMouthSwitch :
      L.entry / 3 = L.mouth / 3 := by
    have hswitch :=
      arrive_exit_switch C.contactState L.entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  have hallAfter : ∀ d, ∃ port phase,
      stepN w d (L.outside, alternate) =
        some (port, phase) ∧
      (phase = alternate ∨ phase = C.contactState) := by
    have hentryOld := L.entryOld
    change (L.entry, L.mouth) ∈
      R.runway ++ [(R.mouth, R.arm)] at hentryOld
    rcases List.mem_append.mp hentryOld with hrunway | hcore
    · obtain ⟨before, after, hsplit⟩ :=
        List.append_of_mem hrunway
      obtain ⟨D, hDpaths, hAvoid⟩ :=
        R.suffix_after_runway_passage
          C.contactState L.oldPaths hsplit L.mouthLink
      have hAvoid' :
          (LocalAction.flip k).Avoids D.toSupported.paths := by
        dsimp [k]
        simpa [hentryMouthSwitch] using hAvoid
      have hDalt :
          PathGrooves D.toSupported.paths alternate := by
        dsimp [alternate]
        exact hDpaths.after_avoiding_action hAvoid'
      let dTravel := D.toSupported.travel
      let lTravel := L.candy.length + 2
      have hDaltEnd :
          stepN w dTravel (L.outside, alternate) =
            some (L.mouth, alternate) := by
        dsimp [dTravel]
        exact (D.toSupported.run alternate hDalt).1
      have hDstateEnd :
          stepN w dTravel (L.outside, C.contactState) =
            some (L.mouth, C.contactState) := by
        dsimp [dTravel]
        exact (D.toSupported.run C.contactState hDpaths).1
      have hDaltPhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (L.outside, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          D.travel_state_stepN alternate hDalt (by
            simpa [dTravel, ManufacturedReflector.toSupported,
              ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, alternate, hrun, Or.inl rfl⟩
      have hDstatePhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (L.outside, C.contactState) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          D.travel_state_stepN C.contactState hDpaths (by
            simpa [dTravel, ManufacturedReflector.toSupported,
              ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, C.contactState, hrun, Or.inr rfl⟩
      have hReverseEnd :
          stepN w lTravel (L.mouth, alternate) =
            some (L.outside, C.contactState) := by
        have h := (L.lobe alternate hCandyFlip).1
        change stepN w lTravel (L.mouth, alternate) =
          some (L.outside, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd :
          stepN w lTravel (L.mouth, C.contactState) =
            some (L.outside, alternate) := by
        have h := (L.lobe C.contactState L.candyGrooved).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (L.mouth, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          L.entryBranch hentryMouthSwitch L.fullGrooved
          L.fullTrace L.crossed L.candyForeign L.mouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (L.mouth, C.contactState) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase
            L.fullGrooved L.fullTrace L.crossed L.mouthLink
            (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let half := dTravel + lTravel
      have hHalfAlt :
          stepN w half (L.outside, alternate) =
            some (L.outside, C.contactState) := by
        dsimp [half]
        rw [stepN_add, hDaltEnd]
        exact hReverseEnd
      have hHalfState :
          stepN w half (L.outside, C.contactState) =
            some (L.outside, alternate) := by
        dsimp [half]
        rw [stepN_add, hDstateEnd]
        exact hForwardEnd
      have hHalfAltPhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (L.outside, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact secondCycle_twoPhase_concat
          hDaltEnd hDaltPhase hReversePhase d
          (by simpa [half] using hd)
      have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (L.outside, C.contactState) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact secondCycle_twoPhase_concat
          hDstateEnd hDstatePhase hForwardPhase d
          (by simpa [half] using hd)
      let period := half + half
      have hperiod :
          stepN w period (L.outside, alternate) =
            some (L.outside, alternate) := by
        dsimp [period]
        rw [stepN_add, hHalfAlt]
        exact hHalfState
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (L.outside, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact secondCycle_twoPhase_concat
          hHalfAlt hHalfAltPhase hHalfStatePhase d
          (by simpa [period] using hd)
      have hpositive : 0 < period := by
        have hdpos :=
          (ManufacturedReflector.stay D).travel_pos
        dsimp [period, half, dTravel, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow
    · simp only [List.mem_singleton] at hcore
      have hentryEq : L.entry = R.mouth :=
        congrArg Prod.fst hcore
      have hmouthEq : L.mouth = R.arm :=
        congrArg Prod.snd hcore
      have houtsideEq : L.outside = R.arm := by
        have hlink := L.mouthLink
        rw [hmouthEq, R.selfLink] at hlink
        exact (Option.some.inj hlink).symm
      have hmouthOutside : L.mouth = L.outside :=
        hmouthEq.trans houtsideEq.symm
      let lTravel := L.candy.length + 2
      have hReverseEnd :
          stepN w lTravel (L.outside, alternate) =
            some (L.outside, C.contactState) := by
        have h := (L.lobe alternate hCandyFlip).1
        change stepN w lTravel (L.mouth, alternate) =
          some (L.outside, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [hmouthOutside, flipAt_flipAt] using h
      have hForwardEnd :
          stepN w lTravel (L.outside, C.contactState) =
            some (L.outside, alternate) := by
        have h := (L.lobe C.contactState L.candyGrooved).1
        simpa [hmouthOutside, lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (L.outside, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        simpa [hmouthOutside] using
          (explicit_lobe_reverse_travel_two_phase
            L.entryBranch hentryMouthSwitch L.fullGrooved
            L.fullTrace L.crossed L.candyForeign L.mouthLink
            (by simpa [lTravel] using hd))
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (L.outside, C.contactState) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase
            L.fullGrooved L.fullTrace L.crossed L.mouthLink
            (by simpa [lTravel] using hd)
        refine ⟨port, phase, by simpa [hmouthOutside] using hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let period := lTravel + lTravel
      have hperiod :
          stepN w period (L.outside, alternate) =
            some (L.outside, alternate) := by
        dsimp [period]
        rw [stepN_add, hReverseEnd]
        exact hForwardEnd
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (L.outside, alternate) =
            some (port, phase) ∧
          (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact secondCycle_twoPhase_concat
          hReverseEnd hReversePhase hForwardPhase d
          (by simpa [period] using hd)
      have hpositive : 0 < period := by
        dsimp [period, lTravel]
        omega
      have hall :=
        periodic_two_phase_prefix_tongues
          hpositive hperiod hwindow
      exact hall
  exact ⟨L.outside, L.mouth,
    by simpa [alternate, k] using L.reach,
    by simpa [alternate] using hallAfter⟩
/-- For a stay reflector, both forward-contact phases are already present
in the compressed lead, so the partial continuation has zero later novelty. -/
theorem SimpleContinuationChangedContact.forward_stay_all_time_zero_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedStayReflector w g e}
    (C : SimpleContinuationChangedContact w
      (ManufacturedReflector.stay R))
    (hforward : C.x = C.oriented.2)
    (times : List Nat) :
    NoveltyCoverOn w N
      (e, (ManufacturedReflector.stay R).activatedState)
      times (C.compressedLead N) 0 := by
  obtain ⟨outside, mouth, hreach, hall⟩ :=
    C.forward_stay_two_phase_tail hforward
  let K := C.approach.length + 1
  let alternate := flipAt C.contactState (mouth / 3)
  have hreach' :
      stepN w K
          (e, (ManufacturedReflector.stay R).activatedState) =
        some (outside, alternate) := by
    simpa [K, alternate] using hreach
  obtain ⟨postPort, hpost⟩ := C.post_reaches
  have hnextAlternate : C.nextState = alternate := by
    rw [hreach'] at hpost
    have hpairs := Option.some.inj hpost
    exact (congrArg Prod.snd hpairs).symm
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.compressedLead N := by
    simpa [hnextAlternate] using
      C.next_mem_compressedLead (N := N)
  have hstateHistorical :
      VectorCount.restrict N C.contactState ∈
        C.compressedLead N :=
    C.contact_mem_compressedLead
  refine ⟨[], by simp, ?_⟩
  intro j _hj
  simp only [List.append_nil]
  by_cases hjK : j < K
  · exact C.mem_compressedLead_of_approach (N := N) (by
      dsimp [K] at hjK
      omega)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hall d
    have hglobal :
        stepN w j
            (e, (ManufacturedReflector.stay R).activatedState) =
          some (port, phase) := by
      rw [hjEq, stepN_add, hreach']
      exact hrun
    have hvector :
        restrictedTonguesAt w N
            (e, (ManufacturedReflector.stay R).activatedState) j =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [alternate, h] using hentryHistorical
    · simpa [h] using hstateHistorical

/-- Every arbitrary simple continuation after one reflector is covered by
its coefficient-one compressed lead plus at most two post-contact vectors
once its first support damage is exposed. -/
theorem SimpleContinuationChangedContact.changed_all_time_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (times : List Nat) :
    NoveltyCoverOn w N (e, A.activatedState)
      times (C.compressedLead N) 2 := by
  rcases C.direction with hbackward |
      ⟨hforward, repaired, hrepair, hrestored⟩
  · obtain ⟨fresh, hfresh, hmem⟩ :=
      C.backward_all_time_zero_novelty
        (N := N) hbackward times
    exact ⟨fresh, by omega, hmem⟩
  · cases A with
    | stay R =>
        obtain ⟨fresh, hfresh, hmem⟩ :=
          C.forward_stay_all_time_zero_novelty
            hforward times
        exact ⟨fresh, by omega, hmem⟩
    | flip R =>
        exact C.forward_flip_all_time_two_novelty
          hforward times
/-- The complete raw run through an arbitrary first damaging partial
continuation has coefficient one: the compressed lead costs at most N+3 and
the forward splice costs at most two further vectors. -/
theorem SimpleContinuationChangedContact.changed_all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : SimpleContinuationChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  let firstTravel :=
    A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - firstTravel)
  have hreach :
      stepN w firstTravel (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  obtain ⟨fresh, hfresh, hlocal⟩ :=
    C.changed_all_time_two_novelty
      (N := N) localTimes
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times (C.compressedLead N) 2 := by
    refine ⟨fresh, hfresh, ?_⟩
    intro k hk
    by_cases hfirst : k ≤ firstTravel
    · apply List.mem_append_left
      unfold SimpleContinuationChangedContact.compressedLead
      apply List.mem_append_left
      apply A.mem_sharpHistoryCore_of_mem
      exact A.manufacturing_journey_mem_sharpHistory hA (by
        simpa [firstTravel] using hfirst)
    · let d := k - firstTravel
      have hdMem : d ∈ localTimes := by
        dsimp [d, localTimes]
        exact List.mem_map.mpr ⟨k, hk, rfl⟩
      have hm := hlocal d hdMem
      have hshift := restrictedTonguesAt_sub_of_reach
        (N := N) hreach (by omega) (hlive k hk)
      rw [hshift]
      exact hm
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength := C.compressedLead_length_le hN hA
  omega

/-- **Stable-cycle known-edge branch, coefficient one.**

After one completed manufactured reflector, every trace-retained second
stable-cycle outcome has at most N+5 distinct raw tongue vectors.  The
support-preserving case is N+3.  If the simple lead damages old support, its
first changing passage creates the generic lobe above; that lobe contributes
at most two vectors beyond the same N+3 compressed first history. -/
theorem FirstActivatedCycleOutcome.second_cycle_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (C : FirstActivatedCycleOutcome
      w (e, A.activatedState) N)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  by_cases hend :
      PathGrooves A.toSupported.paths C.atRepeat.2
  · have hsharp :=
      C.preserved_all_run_distinct_le_N_add_three
        hN A hA hend times hlive hnd
    omega
  · obtain ⟨D⟩ :=
      A.simpleContinuationChangedContact
        hA C.lead_trace C.lead_simple hend
    exact D.changed_all_run_distinct_le_N_add_five
      hN hA times hlive hnd

/-- Requested N+6 interface.  The proved stable-cycle estimate is N+5. -/
theorem FirstActivatedCycleOutcome.second_cycle_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (C : FirstActivatedCycleOutcome
      w (e, A.activatedState) N)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 6 := by
  have hsharp :=
    C.second_cycle_distinct_le_N_add_five
      hN A hA times hlive hnd
  omega
end GeneralN
