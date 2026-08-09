import RecursiveSerialRepair
import FiveFrameObstruction

/-!
# Extracting recursive serial returns inside an arbitrary wiring

`two_switch_fork_trap_or_exact_input_frame` is deliberately *not* used in
this file.  Its hypothesis bounds every linked port by `6`, so it describes a
whole wiring with two switches, not a two-switch-looking region embedded in an
arbitrary `N`-switch track.

The local theorem below instead starts from the actual `PhysicalTrace` at the
first repeated switch.  It applies `first_revisit_fork` directly, without a
port bound or relabelling assumption.  The exact alternatives are:

* the train has entered a tongue-stable simple cycle; or
* it returns through the physical edge attached to the region's input.

The return can be composed recursively.  The only premise left in the
recursive region is an explicit continuation for the configuration that the
physical return really produces.  Thus no global two-switch assumption is
hidden in the extraction.
-/

namespace GeneralN

/-- An exact return through the input edge of a region embedded in an
arbitrary wiring.  Unlike `RawExactInputReturnFrame`, the lead and return
lengths are not bounded by `2` and `3`: those bounds are properties of a whole
two-switch wiring and are unavailable for a general local region. -/
structure RawLocalInputReturnFrame
    (w : Wiring) (entry returned : Nat × Tongues) where
  atRepeat : Nat × Tongues
  lead : Nat
  back : Nat
  reaches_repeat : stepN w lead entry = some atRepeat
  input_link : w.link entry.1 = some returned.1
  returns_through_input :
    stepN w back atRepeat =
      (w.link entry.1).map (fun ell => (ell, returned.2))

/-- A local input-return frame executes exactly from its entry configuration
to its returned configuration. -/
theorem RawLocalInputReturnFrame.run
    {w : Wiring} {entry returned : Nat × Tongues}
    (F : RawLocalInputReturnFrame w entry returned) :
    stepN w (F.lead + F.back) entry = some returned := by
  rw [stepN_add, F.reaches_repeat]
  simpa [F.input_link] using F.returns_through_input

/-- The old bounded frame is recovered only when its two extra numerical
hypotheses are supplied explicitly.  This theorem records the exact boundary
between the isolated two-switch theorem and the arbitrary-`N` local theorem. -/
def RawLocalInputReturnFrame.toBounded
    {w : Wiring} {entry returned : Nat × Tongues}
    (F : RawLocalInputReturnFrame w entry returned)
    (hlead : F.lead ≤ 2) (hback : F.back ≤ 3) :
    RawExactInputReturnFrame w entry returned where
  atRepeat := F.atRepeat
  lead := F.lead
  back := F.back
  lead_le_two := hlead
  back_le_three := hback
  reaches_repeat := F.reaches_repeat
  input_link := F.input_link
  returns_through_input := F.returns_through_input

/-- The fully local data at a first repeated switch.

`prefix` reaches the first occurrence, `old :: loop` reaches the repeated
occurrence, and `repeated :: suffix` is the continuation whose head records
the next local passage.  This is a thin package around three raw
`PhysicalTrace`s. -/
structure RawLocalFirstRevisitRegion
    (w : Wiring) (entry : Nat × Tongues) where
  runwayPrefix : List Passage
  oldPort : Nat
  oldExit : Nat
  excursionTail : List Passage
  repeatPort : Nat
  repeatExit : Nat
  suffix : List Passage
  oldState : Tongues
  repeatState : Tongues
  finish : Nat × Tongues
  prefix_trace :
    PhysicalTrace w entry runwayPrefix (oldPort, oldState)
  excursion_trace :
    PhysicalTrace w (oldPort, oldState)
      ((oldPort, oldExit) :: excursionTail) (repeatPort, repeatState)
  tail_trace :
    PhysicalTrace w (repeatPort, repeatState)
      ((repeatPort, repeatExit) :: suffix) finish
  simple :
    SwitchSimple (runwayPrefix ++ (oldPort, oldExit) :: excursionTail)
  same_switch : oldPort / 3 = repeatPort / 3

def RawLocalFirstRevisitRegion.atRepeat
    {w : Wiring} {entry : Nat × Tongues}
    (R : RawLocalFirstRevisitRegion w entry) : Nat × Tongues :=
  (R.repeatPort, R.repeatState)

def RawLocalFirstRevisitRegion.lead
    {w : Wiring} {entry : Nat × Tongues}
    (R : RawLocalFirstRevisitRegion w entry) : Nat :=
  (R.runwayPrefix ++
    (R.oldPort, R.oldExit) :: R.excursionTail).length

/-- The local trace reaches its named repeated-switch configuration. -/
theorem RawLocalFirstRevisitRegion.reaches_repeat
    {w : Wiring} {entry : Nat × Tongues}
    (R : RawLocalFirstRevisitRegion w entry) :
    stepN w R.lead entry = some R.atRepeat := by
  simpa [RawLocalFirstRevisitRegion.lead,
    RawLocalFirstRevisitRegion.atRepeat] using
    (R.prefix_trace.append R.excursion_trace).sound

/-- Retracing the runway takes no more steps than reaching the first revisit. -/
theorem RawLocalFirstRevisitRegion.back_le_lead
    {w : Wiring} {entry : Nat × Tongues}
    (R : RawLocalFirstRevisitRegion w entry) :
    R.runwayPrefix.length + 1 ≤ R.lead := by
  simp [RawLocalFirstRevisitRegion.lead]

/-- **Arbitrary-`N` local first-revisit fork.**

No port bound appears.  A first repeated switch inside any larger wiring
either starts a stable simple cycle or returns through the region's actual
input edge. -/
theorem RawLocalFirstRevisitRegion.cycle_or_input_return
    {w : Wiring} {entry : Nat × Tongues}
    (R : RawLocalFirstRevisitRegion w entry) :
    SettlesOnSimpleCycle w R.atRepeat ∨
      ∃ back settled,
        back ≤ R.lead ∧
        stepN w back R.atRepeat =
          (w.link entry.1).map (fun ell => (ell, settled)) := by
  obtain ⟨nextState, hrepeat⟩ := R.tail_trace.head_arrive.2
  rcases first_revisit_fork R.prefix_trace R.excursion_trace
      R.simple R.same_switch hrepeat with hcycle | hreturn
  · obtain ⟨period, settled, hpos, honce, hfixed⟩ := hcycle
    left
    exact ⟨period, settled, hpos, honce, hfixed⟩
  · obtain ⟨settled, hreturn⟩ := hreturn
    right
    exact ⟨R.runwayPrefix.length + 1, settled,
      R.back_le_lead, hreturn⟩

/-- If the region's input edge is attached, the local fork produces either a
non-falling trap or an exact composable input-return frame. -/
theorem RawLocalFirstRevisitRegion.trap_or_input_frame
    {w : Wiring} {entry : Nat × Tongues}
    (R : RawLocalFirstRevisitRegion w entry)
    {inputMate : Nat} (hinput : w.link entry.1 = some inputMate) :
    (∃ lead atRepeat,
        stepN w lead entry = some atRepeat ∧
        (∀ n, (stepN w n atRepeat).isSome)) ∨
      (∃ returned,
        Nonempty (RawLocalInputReturnFrame w entry returned)) := by
  rcases R.cycle_or_input_return with hcycle | hreturn
  · left
    exact ⟨R.lead, R.atRepeat, R.reaches_repeat,
      hcycle.never_falls⟩
  · obtain ⟨back, settled, _hback, hreturn⟩ := hreturn
    let returned : Nat × Tongues := (inputMate, settled)
    right
    refine ⟨returned, ⟨{
      atRepeat := R.atRepeat
      lead := R.lead
      back := back
      reaches_repeat := R.reaches_repeat
      input_link := ?_
      returns_through_input := ?_
    }⟩⟩
    · simpa [returned] using hinput
    · simpa [returned] using hreturn

/-- Extract the structured local first-revisit region from the list-level
certificate returned by `first_revisit_split`. -/
theorem rawLocalFirstRevisitRegion_of_first_repeat
    {w : Wiring} {entry finish : Nat × Tongues}
    {runway : List Passage} {repeated : Passage} {suffix : List Passage}
    (htrace : PhysicalTrace w entry
      (runway ++ repeated :: suffix) finish)
    (hsimple : SwitchSimple runway)
    (hrepeated : passageSwitch repeated ∈ runway.map passageSwitch) :
    ∃ R : RawLocalFirstRevisitRegion w entry,
      R.lead = runway.length := by
  obtain ⟨old, hold, hsame⟩ := List.mem_map.mp hrepeated
  obtain ⟨pre, inner, hrunway⟩ := List.append_of_mem hold
  have htrace' : PhysicalTrace w entry
      ((pre ++ old :: inner) ++ repeated :: suffix) finish := by
    simpa [hrunway, List.append_assoc] using htrace
  obtain ⟨atRepeat, hbefore, htail⟩ := htrace'.split_append
  obtain ⟨atOld, hprefix, hexcursion⟩ := hbefore.split_append
  rcases old with ⟨oldPort, oldExit⟩
  rcases repeated with ⟨repeatPort, repeatExit⟩
  have holdPort : atOld.1 = oldPort := hexcursion.head_arrive.1
  rcases atOld with ⟨atOldPort, oldState⟩
  simp only at holdPort
  subst atOldPort
  have hrepeatPort : atRepeat.1 = repeatPort := htail.head_arrive.1
  rcases atRepeat with ⟨atRepeatPort, repeatState⟩
  simp only at hrepeatPort
  subst atRepeatPort
  let R : RawLocalFirstRevisitRegion w entry := {
    runwayPrefix := pre
    oldPort := oldPort
    oldExit := oldExit
    excursionTail := inner
    repeatPort := repeatPort
    repeatExit := repeatExit
    suffix := suffix
    oldState := oldState
    repeatState := repeatState
    finish := finish
    prefix_trace := hprefix
    excursion_trace := hexcursion
    tail_trace := htail
    simple := by
      rw [← hrunway]
      exact hsimple
    same_switch := by
      simpa [passageSwitch] using hsame
  }
  refine ⟨R, ?_⟩
  simpa [R, RawLocalFirstRevisitRegion.lead] using
    (congrArg List.length hrunway).symm

/-! ## Recursive composition of genuinely local returns -/

/-- The arbitrary-`N` analogue of `RawRecursiveRepairOutcome`.  Its frames
are local physical input returns and therefore carry no false global
two-switch bound. -/
inductive RawLocalRecursiveRepairOutcome (w : Wiring) :
    (Nat × Tongues) → Nat → Nat → Option (Nat × Tongues) → Prop
  | done (c : Nat × Tongues) :
      RawLocalRecursiveRepairOutcome w c 0 0 (some c)
  | trap {entry : Nat × Tongues}
      (region : RawLocalFirstRevisitRegion w entry)
      (cycle : SettlesOnSimpleCycle w region.atRepeat) :
      RawLocalRecursiveRepairOutcome w entry 1 region.lead none
  | cons {entry returned : Nat × Tongues}
      {depth tailSteps : Nat} {result : Option (Nat × Tongues)}
      (frame : RawLocalInputReturnFrame w entry returned)
      (tail : RawLocalRecursiveRepairOutcome w returned depth tailSteps result) :
      RawLocalRecursiveRepairOutcome w entry (depth + 1)
        (frame.lead + frame.back + tailSteps) result

/-- The generalized recursive outcome has exactly its claimed raw dynamics. -/
theorem RawLocalRecursiveRepairOutcome.sound
    {w : Wiring} {entry : Nat × Tongues}
    {depth total : Nat} {result : Option (Nat × Tongues)}
    (H : RawLocalRecursiveRepairOutcome w entry depth total result) :
    match result with
      | some root => stepN w total entry = some root
      | none => ∀ n, (stepN w (total + n) entry).isSome := by
  induction H with
  | done c => rfl
  | @trap entry region cycle =>
      intro n
      rw [stepN_add, region.reaches_repeat]
      exact cycle.never_falls n
  | @cons entry returned depth tailSteps result frame tail ih =>
      cases result with
      | none =>
          simp only at ih ⊢
          intro n
          rw [show frame.lead + frame.back + tailSteps + n =
              (frame.lead + frame.back) + (tailSteps + n) by omega,
            stepN_add, frame.run]
          exact ih n
      | some root =>
          simp only at ih ⊢
          rw [show frame.lead + frame.back + tailSteps =
              (frame.lead + frame.back) + tailSteps by omega,
            stepN_add, frame.run]
          exact ih

/-- Raw recursive serial-region data.  Each local first-revisit is physical.
If it returns, `tail` supplies the next region for the *actual* returned
tongue state.  Establishing this continuation from a proposed global serial
counter is now the sole extraction premise; no result or return frame is
assumed in the definition. -/
inductive RawRecursiveSerialRegion (w : Wiring) :
    (Nat × Tongues) → Nat → Prop
  | done (c : Nat × Tongues) : RawRecursiveSerialRegion w c 0
  | cons {entry : Nat × Tongues} {inputMate depth : Nat}
      (region : RawLocalFirstRevisitRegion w entry)
      (input_link : w.link entry.1 = some inputMate)
      (tail : ∀ (back : Nat) (settled : Tongues),
        back ≤ region.lead →
        stepN w back region.atRepeat =
          (w.link entry.1).map (fun ell => (ell, settled)) →
        RawRecursiveSerialRegion w (inputMate, settled) depth) :
      RawRecursiveSerialRegion w entry (depth + 1)

/-- **Recursive serial extraction.**  A region assembled from actual local
first-revisit traces supplies the exact-root/non-falling outcome. -/
theorem RawRecursiveSerialRegion.extract
    {w : Wiring} {entry : Nat × Tongues} {depth : Nat}
    (H : RawRecursiveSerialRegion w entry depth) :
    ∃ usedDepth total result,
      usedDepth ≤ depth ∧
      RawLocalRecursiveRepairOutcome w entry usedDepth total result := by
  induction H with
  | done c =>
      exact ⟨0, 0, some c, Nat.le_refl _,
        RawLocalRecursiveRepairOutcome.done c⟩
  | @cons entry inputMate depth region input_link tail ih =>
      rcases region.cycle_or_input_return with hcycle | hreturn
      · exact ⟨1, region.lead, none, by omega,
          RawLocalRecursiveRepairOutcome.trap region hcycle⟩
      · obtain ⟨back, settled, hback, hreturn⟩ := hreturn
        obtain ⟨usedDepth, tailSteps, result, hused, houtcome⟩ :=
          ih back settled hback hreturn
        let returned : Nat × Tongues := (inputMate, settled)
        let frame : RawLocalInputReturnFrame w entry returned := {
          atRepeat := region.atRepeat
          lead := region.lead
          back := back
          reaches_repeat := region.reaches_repeat
          input_link := by simpa [returned] using input_link
          returns_through_input := by simpa [returned] using hreturn
        }
        exact ⟨usedDepth + 1,
          frame.lead + frame.back + tailSteps, result, by omega,
          RawLocalRecursiveRepairOutcome.cons frame (by
            simpa [returned] using houtcome)⟩

/-- Operational form of recursive extraction: either the stack returns to one
exact root configuration or it reaches a tail which can never fall. -/
theorem RawRecursiveSerialRegion.extract_dichotomy
    {w : Wiring} {entry : Nat × Tongues} {depth : Nat}
    (H : RawRecursiveSerialRegion w entry depth) :
    ∃ total result,
      match result with
        | some root => stepN w total entry = some root
        | none => ∀ n, (stepN w (total + n) entry).isSome := by
  obtain ⟨_usedDepth, total, result, _hused, houtcome⟩ := H.extract
  cases result with
  | none =>
      exact ⟨total, none, houtcome.sound⟩
  | some root =>
      exact ⟨total, some root, houtcome.sound⟩

/-! ## Direct bridge from the five serial closing frames -/

/-- The serial alternative for five raw closing frames yields a genuinely
local arbitrary-`N` first-revisit region and its cycle/input-return fork.

This is the promised bridge from `RawNovelClosingFrame`; the old global
`p,q < 6` hypothesis does not appear. -/
theorem five_serial_novelties_extract_local_return
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (H₀ : RawRepeatedWriterNovelAt w N start z₀)
    (H₁ : RawRepeatedWriterNovelAt w N start z₁)
    (H₂ : RawRepeatedWriterNovelAt w N start z₂)
    (H₃ : RawRepeatedWriterNovelAt w N start z₃)
    (H₄ : RawRepeatedWriterNovelAt w N start z₄)
    {a₀ q₀ a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄ : Nat}
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hserial : FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄) :
    ∃ before, ∃ R : RawLocalFirstRevisitRegion w before,
      stepN w a₀ start = some before ∧
      R.lead ≤ z₀ - a₀ ∧
      (SettlesOnSimpleCycle w R.atRepeat ∨
        ∃ back settled,
          back ≤ R.lead ∧
          stepN w back R.atRepeat =
            (w.link before.1).map (fun ell => (ell, settled))) := by
  obtain ⟨before, close, passages, runway, repeated, suffix,
      hbefore, _hclose, hlength, htrace, hsplit, hsimple, hrepeat⟩ :=
    five_serial_novelties_force_first_repeated_switch hN
      H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  have hlocalTrace : PhysicalTrace w before
      (runway ++ repeated :: suffix) close := by
    rw [← hsplit]
    exact htrace
  obtain ⟨R, hlead⟩ :=
    rawLocalFirstRevisitRegion_of_first_repeat
      hlocalTrace hsimple hrepeat
  have hrunwayLe : runway.length ≤ passages.length := by
    rw [hsplit]
    simp
  refine ⟨before, R, hbefore, ?_, R.cycle_or_input_return⟩
  calc
    R.lead = runway.length := hlead
    _ ≤ passages.length := hrunwayLe
    _ = z₀ - a₀ := hlength

end GeneralN
