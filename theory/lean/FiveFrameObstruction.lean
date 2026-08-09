import RepeatedNoveltyDecomposition
import SelfEpochAmortization
import TrackTrace
import TripleInterlacementObstruction
import UnlinkedCounterObstruction

/-!
# Five closing frames reduce to a triple obstruction

This file is a raw-`Wiring` order reduction for the remaining finite
alternation problem. It does not assume periodicity and it does not assert
`FiveRepeatedWriterNovelty`.

The live decomposition and triple-obstruction libraries are imported
together. Their curve relations have distinct names, so the raw endpoint
order below can be consumed directly by the certified `ABCABC` programme.

Every repeated-writer novelty is packaged with the proved
fresh-or-interlacing rerouter supplied by
`RawRepeatedWriterNovelAt.open_rerouting_decomposition`. For five such
events in increasing closing-time order, their last-writer openings are
pairwise distinct. Consequently either a later frame starts after the
first close (a genuine serial break), or the five overlapping openings
contain a monotone triple. The increasing triple is the endpoint order
`ABCABC`; the decreasing triple is a strict three-frame nest.
-/

namespace GeneralN

/-- A repeated novelty's parity-chosen open rerouting frame. The shape is
the proved fresh-or-interlacing dichotomy; the chosen rerouter has no
nested alternative. -/
structure RawNovelClosingFrame
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (left reroute right : Nat) : Prop where
  outer : RawLastWriterFrame w N start left right
  reroute_productive : RawProductiveAt w N start reroute
  different_writer :
    rawWriterAt w start reroute ≠ rawWriterAt w start right
  no_same_rerouter_before : ∀ j, left < j → j < reroute →
    RawProductiveAt w N start j →
    rawWriterAt w start j ≠ rawWriterAt w start reroute
  shape : RawOpenReroutingShape w N start left reroute right

/-- Package the open-frame decomposition as one existential witness. -/
theorem RawRepeatedWriterNovelAt.novelClosingFrame
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right) :
    ∃ left reroute, RawNovelClosingFrame w N start left reroute right := by
  obtain ⟨left, reroute, outer, productive, different,
      noEarlier, shape⟩ := h.open_rerouting_decomposition hN
  exact ⟨left, reroute, {
    outer := outer
    reroute_productive := productive
    different_writer := different
    no_same_rerouter_before := noEarlier
    shape := shape
  }⟩

/-- Last-writer frames with strictly ordered closing times cannot share an
opening. If they did, the first close would be a forbidden intervening
write in the second frame. -/
theorem rawLastWriterFrame_open_ne_of_close_lt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {leftA rightA leftB rightB : Nat}
    (hclose : rightA < rightB)
    (A : RawLastWriterFrame w N start leftA rightA)
    (B : RawLastWriterFrame w N start leftB rightB) :
    leftA ≠ leftB := by
  intro heq
  have hwriter : rawWriterAt w start rightA =
      rawWriterAt w start rightB := by
    calc
      rawWriterAt w start rightA = rawWriterAt w start leftA :=
        A.same_writer.symm
      _ = rawWriterAt w start leftB := by rw [heq]
      _ = rawWriterAt w start rightB := B.same_writer
  have hopen : leftB < rightA := by
    rw [← heq]
    exact A.order
  exact B.no_same_writer_between rightA hopen hclose
    A.close_productive hwriter

/-! ## The adversarial serial `C,D,C` module -/

/-- A successful trailing traversal leaves over its switch's immutable stem
edge. This is the configuration-level form of the fixed-successor law. -/
private theorem successful_trailing_stem_link
    {w : Wiring} {p q : Nat} {u v : Tongues}
    (hstep : step w (p, u) = some (q, v))
    (hbranch : p % 3 ≠ 0) :
    w.link (3 * (p / 3)) = some q := by
  have hparts := step_some_parts hstep
  simpa [exitPort, arrive, hbranch] using hparts.1

/-- **Exact obstruction to concatenating the proposed one-shot module.**

Suppose three consecutive successful passages visit switches `C,D,C`, with
the two `C` entries trailing and `D ≠ C`. Both `C` passages leave through the
same immutable stem edge, so the state after the second `C` is at the same
entry port as the state after the first. The intervening `D,C` route is
switch-simple. It has therefore grooved both of its passages, and the raw
dynamics repeats it forever without another tongue change.

The conclusion is an exact configuration period, not merely equality of
the represented `N`-switch vector. No bound on `N`, recurrence assumption,
or finite-system enumeration is used. -/
theorem consecutive_CDC_absorbs
    {w : Wiring}
    {p₀ p₁ p₂ p₃ : Nat} {u₀ u₁ u₂ u₃ : Tongues}
    (h₀ : step w (p₀, u₀) = some (p₁, u₁))
    (h₁ : step w (p₁, u₁) = some (p₂, u₂))
    (h₂ : step w (p₂, u₂) = some (p₃, u₃))
    (hC₀ : p₀ % 3 ≠ 0)
    (hC₂ : p₂ % 3 ≠ 0)
    (hsameC : p₀ / 3 = p₂ / 3)
    (hDC : p₁ / 3 ≠ p₂ / 3) :
    stepN w 2 (p₃, u₃) = some (p₃, u₃) := by
  have hlink₀ := successful_trailing_stem_link h₀ hC₀
  have hlink₂ := successful_trailing_stem_link h₂ hC₂
  rw [hsameC] at hlink₀
  have hp₁₃ : p₁ = p₃ := by
    rw [hlink₀] at hlink₂
    injection hlink₂
  subst p₃
  let x₁ := exitPort (p₁, u₁)
  let x₂ := exitPort (p₂, u₂)
  have hparts₁ := step_some_parts h₁
  have hparts₂ := step_some_parts h₂
  have harrive₁ : arrive u₁ p₁ = (x₁, u₂) := by
    apply Prod.ext
    · rfl
    · exact hparts₁.2.symm
  have harrive₂ : arrive u₂ p₂ = (x₂, u₃) := by
    apply Prod.ext
    · rfl
    · exact hparts₂.2.symm
  have htrace : PhysicalTrace w (p₁, u₁)
      [(p₁, x₁), (p₂, x₂)] (p₁, u₃) :=
    PhysicalTrace.cons harrive₁ hparts₁.1
      (PhysicalTrace.cons harrive₂ hparts₂.1
        (PhysicalTrace.nil (p₁, u₃)))
  have hsimple : SwitchSimple [(p₁, x₁), (p₂, x₂)] := by
    simp [SwitchSimple, passageSwitch, hDC]
  simpa using htrace.simple_return_period hsimple

/-- A same-successor call which genuinely changes on its next invocation
cannot have been switch-simple. This is the general raw obstruction behind
the concrete `C,D,C` trap. -/
theorem changed_same_successor_call_not_switchSimple
    {w : Wiring} {p x : Nat} {u v : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hchanged :
      stepN w ((p, x) :: body).length (p, v) ≠ some (p, v)) :
    ¬ SwitchSimple ((p, x) :: body) := by
  intro hsimple
  exact hchanged (simple_same_mouth_call_fixed htrace hsimple)

/-- The same non-idempotent call has an explicit repair witness: one of its
own passages is no longer grooved for reverse traversal in the returned
state. Thus every proposed serial handoff must pay a concrete repeated-track
repair; it cannot be a concatenation of independent one-shot modules. -/
theorem changed_same_successor_call_has_repair
    {w : Wiring} {p x : Nat} {u v : Tongues} {body : List Passage}
    (htrace : PhysicalTrace w (p, u) ((p, x) :: body) (p, v))
    (hchanged :
      stepN w ((p, x) :: body).length (p, v) ≠ some (p, v)) :
    ∃ passage ∈ ((p, x) :: body),
      arrive v passage.2 ≠ (passage.1, v) :=
  changed_same_mouth_call_has_broken_groove htrace hchanged

/-- **General isolated-module obstruction to serial concatenation.**

Assume all linked ports belong to the represented `N` switches and the
module's incoming edge is left open.  Any run that survives `N+1` switch
passages has already revisited a switch.  At that first revisit it either
settles on a tongue-stable simple cycle, or retraces to the incoming edge
and falls through it.  In particular there is no third, fresh-output branch
which could feed an independent next module.

This is a raw-`Wiring`, general-`N` theorem.  It neither assumes
`IrreflexiveLinks` nor enumerates finite wirings. -/
theorem isolated_module_first_repeat_cycle_or_input_fall
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hinputOpen : w.link start.1 = none)
    (hlive : stepN w (N + 1) start = some finish) :
    ∃ (atRepeat : Nat × Tongues) (visited : Nat),
      stepN w visited start = some atRepeat ∧ visited ≤ N ∧
      (SettlesOnSimpleCycle w atRepeat ∨
        ∃ (backSteps : Nat),
          backSteps ≤ N + 1 ∧
          stepN w backSteps atRepeat = none) := by
  obtain ⟨atRepeat, visited, hat, hvisited, hcycle | hreturn⟩ :=
    first_repeat_outcome_of_long_run hN hlive
  · exact ⟨atRepeat, visited, hat, hvisited, Or.inl hcycle⟩
  · obtain ⟨backSteps, settled, hback, hreturn⟩ := hreturn
    refine ⟨atRepeat, visited, hat, hvisited, Or.inr
      ⟨backSteps, hback, ?_⟩⟩
    simpa [hinputOpen] using hreturn

/-! ## Switch-simple traces cannot hide a later serial frame -/

/-- A linked list of grooves is not merely executable: it is an exact
`PhysicalTrace` whose tongue state is constant throughout. -/
private theorem grooved_passages_physicalTrace
    (w : Wiring) (u : Tongues) (p x q : Nat) (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hfinal : w.link (lastPassageExit x rest) = some q) :
    PhysicalTrace w (p, u) ((p, x) :: rest) (q, u) := by
  induction rest generalizing p x with
  | nil =>
      have hhead := hgrooved (p, x) (by simp)
      have hfwd := groove_forward hhead
      exact PhysicalTrace.cons hfwd
        (by simpa [lastPassageExit] using hfinal)
        (PhysicalTrace.nil (q, u))
  | cons passage rest ih =>
      rcases passage with ⟨r, y⟩
      have hxy : w.link x = some r := hlinked.1
      have htailLinked : LinkedPassages w ((r, y) :: rest) :=
        hlinked.2
      have htailGrooved : PassagesGrooved u ((r, y) :: rest) := by
        intro passage hp
        exact hgrooved passage (List.mem_cons_of_mem _ hp)
      have htailFinal : w.link (lastPassageExit y rest) = some q := by
        simpa [lastPassageExit] using hfinal
      have htail := ih r y htailLinked htailGrooved htailFinal
      have hhead := hgrooved (p, x) (by simp)
      exact PhysicalTrace.cons (groove_forward hhead) hxy htail

/-- The raw writer at an offset of a physical trace is one of the switches
recorded by that trace. -/
private theorem PhysicalTrace.rawWriterAt_add_mem
    {w : Wiring} {global start finish : Nat × Tongues}
    {base : Nat} {passages : List Passage}
    (hbase : stepN w base global = some start)
    (htrace : PhysicalTrace w start passages finish) :
    ∀ {d : Nat}, d < passages.length →
      rawWriterAt w global (base + d) ∈ passages.map passageSwitch := by
  induction htrace generalizing base with
  | nil =>
      intro d hd
      simp at hd
  | @cons p x q u v passages finish harrive hlink tail ih =>
      intro d hd
      have hstep : step w (p, u) = some (q, v) := by
        simp [step, harrive, hlink]
      have hbaseNext : stepN w (base + 1) global = some (q, v) := by
        rw [stepN_add, hbase]
        simp [stepN, hstep]
      cases d with
      | zero =>
          have hwriter : rawWriterAt w global base = p / 3 := by
            simp [rawWriterAt, rawEntryAt, hbase]
          simp [hwriter, passageSwitch]
      | succ d =>
          have hdTail : d < passages.length := by
            simpa using hd
          have hmem := ih hbaseNext hdTail
          have htime : base + (d + 1) = (base + 1) + d := by omega
          rw [htime]
          exact List.mem_cons_of_mem _ hmem

/-- During a switch-simple trace, two offsets with the same raw writer are
the same offset.  This is the exact first-lap uniqueness fact needed below. -/
private theorem PhysicalTrace.rawWriterAt_add_injective
    {w : Wiring} {global start finish : Nat × Tongues}
    {base : Nat} {passages : List Passage}
    (hbase : stepN w base global = some start)
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    ∀ {i j : Nat}, i < passages.length → j < passages.length →
      rawWriterAt w global (base + i) =
        rawWriterAt w global (base + j) → i = j := by
  induction htrace generalizing base with
  | nil =>
      intro i j hi
      simp at hi
  | @cons p x q u v passages finish harrive hlink tail ih =>
      unfold SwitchSimple at hsimple
      simp only [List.map_cons, List.nodup_cons] at hsimple
      have hstep : step w (p, u) = some (q, v) := by
        simp [step, harrive, hlink]
      have hbaseNext : stepN w (base + 1) global = some (q, v) := by
        rw [stepN_add, hbase]
        simp [stepN, hstep]
      have hhead : rawWriterAt w global base = passageSwitch (p, x) := by
        simp [rawWriterAt, rawEntryAt, hbase, passageSwitch]
      intro i j hi hj heq
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              have hjTail : j < passages.length := by simpa using hj
              have hmem := tail.rawWriterAt_add_mem hbaseNext hjTail
              have htime : base + (j + 1) = (base + 1) + j := by omega
              have heq' : passageSwitch (p, x) =
                  rawWriterAt w global ((base + 1) + j) := by
                rw [← hhead, ← htime]
                simpa using heq
              exact (hsimple.1 (by simpa [heq'] using hmem)).elim
      | succ i =>
          cases j with
          | zero =>
              have hiTail : i < passages.length := by simpa using hi
              have hmem := tail.rawWriterAt_add_mem hbaseNext hiTail
              have htime : base + (i + 1) = (base + 1) + i := by omega
              have heq' : rawWriterAt w global ((base + 1) + i) =
                  passageSwitch (p, x) := by
                rw [← htime, ← hhead]
                simpa using heq
              exact (hsimple.1 (by simpa [← heq'] using hmem)).elim
          | succ j =>
              have hiTail : i < passages.length := by simpa using hi
              have hjTail : j < passages.length := by simpa using hj
              have htimeI : base + (i + 1) = (base + 1) + i := by omega
              have htimeJ : base + (j + 1) = (base + 1) + j := by omega
              apply congrArg Nat.succ
              apply ih hbaseNext hsimple.2 hiTail hjTail
              simpa [htimeI, htimeJ] using heq

/-- Every prefix of a linked grooved passage list is live and preserves the
complete tongue state. -/
private theorem grooved_passages_prefix_state
    (w : Wiring) (u : Tongues) (p x q : Nat) (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hfinal : w.link (lastPassageExit x rest) = some q) :
    ∀ {d : Nat}, d ≤ ((p, x) :: rest).length →
      ∃ q, stepN w d (p, u) = some (q, u) := by
  induction rest generalizing p x with
  | nil =>
      intro d hd
      have hhead := hgrooved (p, x) (by simp)
      have hfwd := groove_forward hhead
      cases d with
      | zero => exact ⟨p, by simp [stepN]⟩
      | succ d =>
          have hd0 : d = 0 := by simpa using hd
          subst d
          exact ⟨q, by
            simpa [stepN, step, lastPassageExit, hfwd] using hfinal⟩
  | cons passage rest ih =>
      rcases passage with ⟨r, y⟩
      intro d hd
      cases d with
      | zero => exact ⟨p, by simp [stepN]⟩
      | succ d =>
          have hxy : w.link x = some r := hlinked.1
          have hhead := hgrooved (p, x) (by simp)
          have hone : stepN w 1 (p, u) = some (r, u) := by
            simp [stepN, step, groove_forward hhead, hxy]
          have htailLinked : LinkedPassages w ((r, y) :: rest) :=
            hlinked.2
          have htailGrooved : PassagesGrooved u ((r, y) :: rest) := by
            intro passage hp
            exact hgrooved passage (List.mem_cons_of_mem _ hp)
          have hdTail : d ≤ ((r, y) :: rest).length := by
            simpa using hd
          have htailFinal :
              w.link (lastPassageExit y rest) = some q := by
            simpa [lastPassageExit] using hfinal
          obtain ⟨next, htail⟩ :=
            ih r y htailLinked htailGrooved htailFinal hdTail
          refine ⟨next, ?_⟩
          have hlen : d + 1 = 1 + d := by omega
          rw [hlen, stepN_add, hone]
          exact htail

/-- Repeating a nonempty grooved cycle keeps the complete tongue state
constant at every future time, not only at period boundaries. -/
private theorem grooved_cycle_forever_state
    (w : Wiring) (u : Tongues) (p x : Nat) (rest : List Passage)
    (hlinked : LinkedPassages w ((p, x) :: rest))
    (hgrooved : PassagesGrooved u ((p, x) :: rest))
    (hfinal : w.link (lastPassageExit x rest) = some p) :
    ∀ d, ∃ q, stepN w d (p, u) = some (q, u) := by
  intro d
  apply Nat.strongRecOn (motive := fun d =>
    ∃ q, stepN w d (p, u) = some (q, u)) d
  intro d ih
  let period := ((p, x) :: rest).length
  have hperiodPos : 0 < period := by simp [period]
  by_cases hshort : d ≤ period
  · exact grooved_passages_prefix_state w u p x p rest
      hlinked hgrooved hfinal hshort
  · let remaining := d - period
    have hperiodLt : period < d := Nat.lt_of_not_ge hshort
    have hremainingLt : remaining < d := by
      dsimp [remaining]
      omega
    have hsplit : d = period + remaining := by
      dsimp [remaining]
      omega
    have hround : stepN w period (p, u) = some (p, u) := by
      dsimp [period]
      exact run_grooved_passages w u p x p rest
        hlinked hgrooved hfinal
    obtain ⟨q, htail⟩ := ih remaining hremainingLt
    refine ⟨q, ?_⟩
    rw [hsplit, stepN_add, hround]
    exact htail

/-- Strengthening of `simple_same_exit_enters_period`: the transient lap and
the stable lap are returned as exact physical traces over the same
switch-simple passage list. -/
private theorem PhysicalTrace.simple_same_exit_cycle_traces
    {w : Wiring} {p x q : Nat} {u₀ u v : Tongues}
    {rest : List Passage}
    (htrace : PhysicalTrace w (p, u₀) ((p, x) :: rest) (q, u))
    (hsimple : SwitchSimple ((p, x) :: rest))
    (hnext : arrive u q = (x, v)) :
    PhysicalTrace w (q, u) ((q, x) :: rest) (q, v) ∧
      PhysicalTrace w (q, v) ((q, x) :: rest) (q, v) ∧
      SwitchSimple ((q, x) :: rest) := by
  have holdGrooved := htrace.grooved_of_switchSimple hsimple
  have holdLinked := htrace.linked
  have hfinal : w.link (lastPassageExit x rest) = some q :=
    htrace.last_link
  have hheadOld : arrive u x = (p, u) :=
    holdGrooved (p, x) (by simp)
  have hpx : p / 3 = x / 3 := by
    have hs := arrive_exit_switch u x
    rw [hheadOld] at hs
    exact hs
  have hqx : x / 3 = q / 3 := by
    have hs := arrive_exit_switch u q
    rw [hnext] at hs
    exact hs
  unfold SwitchSimple at hsimple
  simp only [List.map_cons, List.nodup_cons] at hsimple
  have hrestGrooved : PassagesGrooved v rest := by
    intro passage hp
    have hold := holdGrooved passage (List.mem_cons_of_mem _ hp)
    have hpassageSwitch : passageSwitch passage ≠ p / 3 := by
      intro hEq
      apply hsimple.1
      apply List.mem_map.mpr
      exact ⟨passage, hp, hEq⟩
    have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
      have hs := arrive_exit_switch u passage.2
      rw [hold] at hs
      exact hs.symm
    have hforeign : passage.2 / 3 ≠ q / 3 := by
      rw [hexitSwitch, ← hqx, ← hpx]
      exact hpassageSwitch
    have hsame : v (passage.2 / 3) = u (passage.2 / 3) :=
      arrive_preserves_other hnext hforeign
    exact groove_transfer hold hsame
  have hheadNew : arrive v x = (q, v) := by
    have hb := arrive_back u q
    rw [hnext] at hb
    exact hb
  have hnewGrooved : PassagesGrooved v ((q, x) :: rest) := by
    intro passage hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadNew
    · exact hrestGrooved passage htail
  have hnewLinked : LinkedPassages w ((q, x) :: rest) := by
    cases rest with
    | nil => trivial
    | cons passage rest =>
        simpa [LinkedPassages] using holdLinked
  have hstable : PhysicalTrace w (q, v) ((q, x) :: rest) (q, v) :=
    grooved_passages_physicalTrace w v q x q rest
      hnewLinked hnewGrooved hfinal
  have htransient : PhysicalTrace w (q, u) ((q, x) :: rest) (q, v) := by
    cases rest with
    | nil =>
        exact PhysicalTrace.cons hnext
          (by simpa [lastPassageExit] using hfinal)
          (PhysicalTrace.nil (q, v))
    | cons passage rest =>
        rcases passage with ⟨r, y⟩
        have hxy : w.link x = some r := holdLinked.1
        have htailLinked : LinkedPassages w ((r, y) :: rest) :=
          hnewLinked.2
        have htailGrooved : PassagesGrooved v ((r, y) :: rest) := by
          intro passage hp
          exact hnewGrooved passage (List.mem_cons_of_mem _ hp)
        have htailFinal : w.link (lastPassageExit y rest) = some q := by
          simpa [lastPassageExit] using hfinal
        exact PhysicalTrace.cons hnext hxy
          (grooved_passages_physicalTrace w v r y q rest
            htailLinked htailGrooved htailFinal)
  have hsimpleCycle : SwitchSimple ((q, x) :: rest) := by
    unfold SwitchSimple
    simp only [List.map_cons, passageSwitch]
    have hpq : p / 3 = q / 3 := hpx.trans hqx
    constructor
    · intro a ha hEq
      apply hsimple.1
      have hheadEq : passageSwitch (p, x) = a := by
        calc
          passageSwitch (p, x) = p / 3 := rfl
          _ = q / 3 := hpq
          _ = a := hEq
      rw [hheadEq]
      exact ha
    · exact hsimple.2
  exact ⟨htransient, hstable, hsimpleCycle⟩

/-- In the crossed first-revisit branch, the contact can only change the
revisited switch.  Since that switch does not occur on the simple caller
runway, every caller passage remains grooved in the contact state. -/
private theorem PhysicalTrace.caller_grooved_after_cross_contact
    {w : Wiring}
    {start : Nat × Tongues} {runway body : List Passage}
    {p x q : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hbody : PhysicalTrace w (p, u₀) ((p, x) :: body) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: body))
    (hsame : p / 3 = q / 3)
    (hcontact : arrive u q = (p, v)) :
    PassagesGrooved v runway := by
  have hfull := hrunway.append hbody
  have hfullGrooved := hfull.grooved_of_switchSimple hsimple
  unfold SwitchSimple at hsimple
  simp only [List.map_append, List.map_cons] at hsimple
  have hparts := List.nodup_append.mp hsimple
  have hpNotPrefix : p / 3 ∉ runway.map passageSwitch := by
    intro hp
    have hne := hparts.2.2 (p / 3) hp
      (p / 3) (by simp [passageSwitch])
    exact hne rfl
  intro passage hp
  have hold := hfullGrooved passage
    (List.mem_append_left _ hp)
  have hpassageNe : passageSwitch passage ≠ q / 3 := by
    intro hEq
    apply hpNotPrefix
    apply List.mem_map.mpr
    exact ⟨passage, hp, hEq.trans hsame.symm⟩
  have hexitSwitch : passage.2 / 3 = passageSwitch passage := by
    have hs := arrive_exit_switch u passage.2
    rw [hold] at hs
    exact hs.symm
  have hforeign : passage.2 / 3 ≠ q / 3 := by
    rw [hexitSwitch]
    exact hpassageNe
  exact groove_transfer hold
    (arrive_preserves_other hcontact hforeign)

/-- Strengthened first-revisit fork retaining the exact switch-simple cycle
trace in the absorbing branch.  This extra data is what lets a later raw
novelty rule that branch out, rather than treating `SettlesOnSimpleCycle` as
an opaque eventual-periodicity certificate. -/
private theorem PhysicalTrace.first_revisit_cycle_traces_or_retrace
    {w : Wiring}
    {start : Nat × Tongues} {runway body : List Passage}
    {p x q y : Nat} {u₀ u v : Tongues}
    (hrunway : PhysicalTrace w start runway (p, u₀))
    (hbody : PhysicalTrace w (p, u₀) ((p, x) :: body) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: body))
    (hsame : p / 3 = q / 3)
    (hrepeat : arrive u q = (y, v)) :
    (∃ cycle settled,
        cycle ≠ [] ∧
        PhysicalTrace w (q, u) cycle (q, settled) ∧
        PhysicalTrace w (q, settled) cycle (q, settled) ∧
        SwitchSimple cycle) ∨
      (∃ settled,
        PassagesGrooved settled runway ∧
        arrive u q = (p, settled) ∧
        stepN w (runway.length + 1) (q, u) =
          (w.link start.1).map (fun ell => (ell, settled))) := by
  have hsimpleBody : SwitchSimple ((p, x) :: body) := by
    unfold SwitchSimple at hsimple ⊢
    simp only [List.map_append] at hsimple
    exact (List.nodup_append.mp hsimple).2.1
  have holdStem :
      p = 3 * passageSwitch (p, x) ∨
        x = 3 * passageSwitch (p, x) :=
    hbody.passage_stem_endpoint (p, x) List.mem_cons_self
  have hrepeatStem :
      q = 3 * passageSwitch (q, y) ∨
        y = 3 * passageSwitch (q, y) := by
    have hs := arrive_stem_endpoint u q
    rw [hrepeat] at hs
    exact hs
  have hsame' : passageSwitch (p, x) = passageSwitch (q, y) := by
    simpa [passageSwitch] using hsame
  have hshare : p = q ∨ p = y ∨ x = q ∨ x = y :=
    recorded_passages_share_port holdStem hrepeatStem hsame'
  rcases hshare with hpq | hpy | hxq | hxy
  · subst q
    have hgrooved := hbody.grooved_of_switchSimple hsimpleBody
    have hlinked := hbody.linked
    have hfinal : w.link (lastPassageExit x body) = some p :=
      hbody.last_link
    have hstable :
        PhysicalTrace w (p, u) ((p, x) :: body) (p, u) :=
      grooved_passages_physicalTrace w u p x p body
        hlinked hgrooved hfinal
    exact Or.inl ⟨(p, x) :: body, u, by simp,
      hstable, hstable, hsimpleBody⟩
  · subst y
    have hgrooved := hrunway.caller_grooved_after_cross_contact
      hbody hsimple hsame hrepeat
    exact Or.inr ⟨v, hgrooved, hrepeat,
      hrunway.simple_cross_exit_retraces_prefix
        hbody hsimple hrepeat⟩
  · subst q
    have hfull := hrunway.append hbody
    have hgrooved := hfull.grooved_of_switchSimple hsimple
    have hold : arrive u x = (p, u) :=
      hgrooved (p, x) (by
        apply List.mem_append_right runway
        exact List.mem_cons_self)
    have hcontact₀ : arrive u x = (p, u) := hold
    rw [hrepeat] at hold
    injection hold with hyp huv
    subst y
    subst v
    have hcontact : arrive u x = (p, u) := hcontact₀
    have hgrooved := hrunway.caller_grooved_after_cross_contact
      hbody hsimple hsame hcontact
    exact Or.inr ⟨u, hgrooved, hcontact,
      hrunway.simple_cross_exit_retraces_prefix
        hbody hsimple (by simpa using hrepeat)⟩
  · subst y
    obtain ⟨htransient, hstable, hsimpleCycle⟩ :=
      hbody.simple_same_exit_cycle_traces hsimpleBody hrepeat
    exact Or.inl ⟨(q, x) :: body, v, by simp,
      htransient, hstable, hsimpleCycle⟩

/-- Once a switch-simple cycle has been entered, no serially later globally
novel repeated-writer frame can exist.  Before the first lap closes, writer
identity is injective along the simple trace.  From the end of that lap on,
all tongues are grooved and the complete tongue vector is constant. -/
private theorem serial_repeated_novel_after_simple_cycle_trace_false
    {w : Wiring} {N : Nat} {global : Nat × Tongues}
    {base laterOpen laterClose p : Nat} {u settled : Tongues}
    {cycle : List Passage}
    (hbase : stepN w base global = some (p, u))
    (htransient : PhysicalTrace w (p, u) cycle (p, settled))
    (hstable : PhysicalTrace w (p, settled) cycle (p, settled))
    (hsimple : SwitchSimple cycle)
    (hnonempty : cycle ≠ [])
    (G : RawLastWriterFrame w N global laterOpen laterClose)
    (H : RawRepeatedWriterNovelAt w N global laterClose)
    (hserial : base ≤ laterOpen) : False := by
  cases hcycle : cycle with
  | nil => exact hnonempty hcycle
  | cons passage rest =>
      rcases passage with ⟨head, x⟩
      have htransient' :
          PhysicalTrace w (p, u) ((head, x) :: rest) (p, settled) := by
        simpa [hcycle] using htransient
      have hstable' :
          PhysicalTrace w (p, settled) ((head, x) :: rest)
            (p, settled) := by
        simpa [hcycle] using hstable
      have hsimple' : SwitchSimple ((head, x) :: rest) := by
        simpa [hcycle] using hsimple
      have hhead : p = head := htransient'.head_arrive.1
      subst head
      let period := ((p, x) :: rest).length
      have hsettledAt :
          stepN w (base + period) global = some (p, settled) := by
        rw [stepN_add, hbase]
        simpa [period] using htransient'.sound
      have hcycleGrooved :
          PassagesGrooved settled ((p, x) :: rest) :=
        hstable'.grooved_of_switchSimple hsimple'
      have hcycleLinked : LinkedPassages w ((p, x) :: rest) :=
        hstable'.linked
      have hcycleFinal :
          w.link (lastPassageExit x rest) = some p :=
        hstable'.last_link
      have hbaseOpen : base ≤ laterOpen := hserial
      have hopenClose : laterOpen < laterClose := G.order
      by_cases hbeforeStable : laterClose < base + period
      · let i := laterOpen - base
        let j := laterClose - base
        have hi : i < period := by
          dsimp [i]
          omega
        have hj : j < period := by
          dsimp [j]
          omega
        have htimeI : base + i = laterOpen := by
          dsimp [i]
          omega
        have htimeJ : base + j = laterClose := by
          dsimp [j]
          omega
        have hsameWriter :
            rawWriterAt w global (base + i) =
              rawWriterAt w global (base + j) := by
          rw [htimeI, htimeJ]
          exact G.same_writer
        have hij := htransient'.rawWriterAt_add_injective
          hbase hsimple' hi hj hsameWriter
        have hopenClose : laterOpen = laterClose := by omega
        exact (Nat.ne_of_lt G.order) hopenClose
      · have hge : base + period ≤ laterClose :=
          Nat.le_of_not_gt hbeforeStable
        let d := laterClose + 1 - (base + period)
        have hsplit :
            laterClose + 1 = base + period + d := by
          dsimp [d]
          omega
        obtain ⟨port, hfuture⟩ :=
          grooved_cycle_forever_state w settled p x rest
            hcycleLinked hcycleGrooved hcycleFinal d
        have hpostAt : stepN w (laterClose + 1) global =
            some (port, settled) := by
          rw [hsplit, stepN_add, hsettledAt]
          exact hfuture
        have hvector :
            restrictedTonguesAt w N global (laterClose + 1) =
              restrictedTonguesAt w N global (base + period) := by
          simp [restrictedTonguesAt, tonguesAt, hpostAt, hsettledAt]
        apply H.2.2
        apply List.mem_map.mpr
        exact ⟨base + period, List.mem_range.mpr (by omega),
          hvector.symm⟩

/-- **Concrete elimination of the independent serial-frame case.**

Let `[left,right]` be a repeated productive-writer frame.  If its complete
physical trace is switch-simple, the closing visit starts one explicit
switch-simple transient lap and then the same route is permanently grooved.
No later globally novel repeated-writer frame can open at or after `right`:
its two equal writers would either repeat inside the first simple lap, or its
post-vector would occur after the stable tongue state had already appeared.

Thus a serially separated novelty is possible only when the earlier frame's
actual passage trace is non-simple.  This consumes the global novelty of the
later close; it is not a conditional module specification. -/
theorem serial_novel_frame_forces_earlier_trace_nonsimple
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {global : Nat × Tongues}
    {left right laterOpen laterClose : Nat}
    (F : RawLastWriterFrame w N global left right)
    (G : RawLastWriterFrame w N global laterOpen laterClose)
    (H : RawRepeatedWriterNovelAt w N global laterClose)
    (hserial : right ≤ laterOpen)
    {before close : Nat × Tongues} {passages : List Passage}
    (hbeforeAt : stepN w left global = some before)
    (hcloseAt : stepN w right global = some close)
    (hlength : passages.length = right - left)
    (htrace : PhysicalTrace w before passages close) :
    ¬ SwitchSimple passages := by
  intro hsimple
  obtain ⟨openCfg, openNext, C, hC, hopenCfg, _hopenNext,
      _hopenStep, _hopenEntry, hopenExit, _hopenFlip, _hopenBack⟩ :=
    rawProductiveAt_is_endpoint_pivot hN F.open_productive
  obtain ⟨closeCfg, closeNext, D, hD, hcloseCfg, _hcloseNext,
      hcloseStep, _hcloseEntry, hcloseExit, _hcloseFlip, _hcloseBack⟩ :=
    rawProductiveAt_is_endpoint_pivot hN F.close_productive
  have hopenEq : openCfg = before :=
    Option.some.inj (hopenCfg.symm.trans hbeforeAt)
  have hcloseEq : closeCfg = close :=
    Option.some.inj (hcloseCfg.symm.trans hcloseAt)
  have hCD : C = D :=
    hC.trans (F.same_writer.trans hD.symm)
  have hbaseTrace : PhysicalTrace w openCfg passages closeCfg := by
    simpa [hopenEq, hcloseEq] using htrace
  cases hpassages : passages with
  | nil =>
      have hzero : right - left = 0 := by
        simpa [hpassages] using hlength.symm
      have horder := F.order
      omega
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace' :
          PhysicalTrace w openCfg ((p, x) :: rest) closeCfg := by
        simpa [hpassages] using hbaseTrace
      have hsimple' : SwitchSimple ((p, x) :: rest) := by
        simpa [hpassages] using hsimple
      have hp : openCfg.1 = p := htrace'.head_arrive.1
      obtain ⟨afterOpen, harriveOpen⟩ := htrace'.head_arrive.2
      have hx : exitPort openCfg = x := by
        unfold exitPort
        rw [hp]
        exact congrArg Prod.fst harriveOpen
      have hxStem : x = 3 * C := by
        rw [← hx]
        exact hopenExit
      have hpartsClose := step_some_parts hcloseStep
      have harriveClose : arrive closeCfg.2 closeCfg.1 =
          (3 * D, closeNext.2) := by
        apply Prod.ext
        · exact hcloseExit
        · exact hpartsClose.2.symm
      have hnext : arrive closeCfg.2 closeCfg.1 =
          (x, closeNext.2) := by
        simpa [hxStem, hCD] using harriveClose
      have hopenPair : openCfg = (p, openCfg.2) := by
        apply Prod.ext
        · exact hp
        · rfl
      have hclosePair :
          closeCfg = (closeCfg.1, closeCfg.2) := Prod.eta _
      have htracePair : PhysicalTrace w (p, openCfg.2)
          ((p, x) :: rest) (closeCfg.1, closeCfg.2) := by
        rw [← hopenPair, ← hclosePair]
        exact htrace'
      obtain ⟨htransient, hstable, hsimpleCycle⟩ :=
        htracePair.simple_same_exit_cycle_traces hsimple' hnext
      let cycle : List Passage := (closeCfg.1, x) :: rest
      have hcycleLength : cycle.length = right - left := by
        dsimp [cycle]
        simpa [hpassages] using hlength
      have hsettledAt :
          stepN w (right + cycle.length) global =
            some (closeCfg.1, closeNext.2) := by
        rw [stepN_add, hcloseCfg]
        exact htransient.sound
      have hcycleGrooved : PassagesGrooved closeNext.2 cycle := by
        exact hstable.grooved_of_switchSimple hsimpleCycle
      have hcycleLinked : LinkedPassages w cycle := hstable.linked
      have hcycleFinal :
          w.link (lastPassageExit x rest) = some closeCfg.1 :=
        hstable.last_link
      have hlaterBeforeStable : laterClose < right + cycle.length := by
        by_cases hlt : laterClose < right + cycle.length
        · exact hlt
        · exfalso
          have hge : right + cycle.length ≤ laterClose :=
            Nat.le_of_not_gt hlt
          let d := laterClose + 1 - (right + cycle.length)
          have hsplit :
              laterClose + 1 = right + cycle.length + d := by
            dsimp [d]
            omega
          obtain ⟨port, hfuture⟩ :=
            grooved_cycle_forever_state w closeNext.2
              closeCfg.1 x rest hcycleLinked hcycleGrooved hcycleFinal d
          have hpostAt : stepN w (laterClose + 1) global =
              some (port, closeNext.2) := by
            rw [hsplit, stepN_add, hsettledAt]
            exact hfuture
          have hvector :
              restrictedTonguesAt w N global (laterClose + 1) =
                restrictedTonguesAt w N global
                  (right + cycle.length) := by
            simp [restrictedTonguesAt, tonguesAt, hpostAt, hsettledAt]
          apply H.2.2
          apply List.mem_map.mpr
          exact ⟨right + cycle.length,
            List.mem_range.mpr (by omega), hvector.symm⟩
      let i := laterOpen - right
      let j := laterClose - right
      have hlaterOrder := G.order
      have hopenBound : laterOpen < right + cycle.length :=
        Nat.lt_trans hlaterOrder hlaterBeforeStable
      have hrightLaterClose : right ≤ laterClose :=
        Nat.le_trans hserial (Nat.le_of_lt hlaterOrder)
      have hi : i < cycle.length := by
        dsimp [i]
        omega
      have hj : j < cycle.length := by
        dsimp [j]
        omega
      have htimeI : right + i = laterOpen := by
        dsimp [i]
        omega
      have htimeJ : right + j = laterClose := by
        dsimp [j]
        omega
      have hsameWriter :
          rawWriterAt w global (right + i) =
            rawWriterAt w global (right + j) := by
        rw [htimeI, htimeJ]
        exact G.same_writer
      have hij := htransient.rawWriterAt_add_injective
        hcloseCfg hsimpleCycle hi hj hsameWriter
      have hopenClose : laterOpen = laterClose := by omega
      exact (Nat.ne_of_lt G.order) hopenClose

/-- At least one later frame begins after the first frame has closed. -/
def FiveFrameSerialBreak
    (z₀ a₁ a₂ a₃ a₄ : Nat) : Prop :=
  z₀ ≤ a₁ ∨ z₀ ≤ a₂ ∨ z₀ ≤ a₃ ∨ z₀ ≤ a₄

/-- **Five-frame serial case closed to a physical first revisit.**

Given five actual globally novel repeated-writer events and their five raw
closing frames, the `FiveFrameSerialBreak` alternative cannot be a chain of
independent switch-simple modules.  The complete passage trace of the first
frame has a concrete first repeated switch: a switch-simple prefix followed
by a passage whose switch already occurs in that prefix.

This theorem consumes the five novelty proofs and the serial disjunction
itself.  Its conclusion is the interlacing/repair contact required by the
remaining curve argument, not another conditional closure predicate. -/
theorem five_serial_novelties_force_first_repeated_switch
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
    ∃ before close passages runway repeated suffix,
      stepN w a₀ start = some before ∧
      stepN w z₀ start = some close ∧
      passages.length = z₀ - a₀ ∧
      PhysicalTrace w before passages close ∧
      passages = runway ++ repeated :: suffix ∧
      SwitchSimple runway ∧
      passageSwitch repeated ∈ runway.map passageSwitch := by
  obtain ⟨before, _afterOpen, _C, _hC, hbeforeAt, _hafterOpen,
      _hstepOpen, _hentryOpen, _hexitOpen, _hflipOpen, _hbackOpen⟩ :=
    rawProductiveAt_is_endpoint_pivot hN F₀.outer.open_productive
  obtain ⟨close, _afterClose, _D, _hD, hcloseAt, _hafterClose,
      _hstepClose, _hentryClose, _hexitClose, _hflipClose, _hbackClose⟩ :=
    rawProductiveAt_is_endpoint_pivot hN H₀.1
  let span := z₀ - a₀
  have hsum : a₀ + span = z₀ := by
    dsimp [span]
    exact Nat.add_sub_of_le (Nat.le_of_lt F₀.outer.order)
  have hinterval : stepN w span before = some close := by
    have hsplit := stepN_add w a₀ span start
    rw [hbeforeAt] at hsplit
    simp only [Option.bind_some] at hsplit
    rw [hsum, hcloseAt] at hsplit
    exact hsplit.symm
  obtain ⟨passages, hlength, htrace⟩ :=
    physicalTrace_of_stepN w hinterval
  have hnonsimple : ¬ SwitchSimple passages := by
    rcases hserial with h₁ | h₂ | h₃ | h₄
    · exact serial_novel_frame_forces_earlier_trace_nonsimple
        hN F₀.outer F₁.outer H₁ h₁ hbeforeAt hcloseAt
          (by simpa [span] using hlength) htrace
    · exact serial_novel_frame_forces_earlier_trace_nonsimple
        hN F₀.outer F₂.outer H₂ h₂ hbeforeAt hcloseAt
          (by simpa [span] using hlength) htrace
    · exact serial_novel_frame_forces_earlier_trace_nonsimple
        hN F₀.outer F₃.outer H₃ h₃ hbeforeAt hcloseAt
          (by simpa [span] using hlength) htrace
    · exact serial_novel_frame_forces_earlier_trace_nonsimple
        hN F₀.outer F₄.outer H₄ h₄ hbeforeAt hcloseAt
          (by simpa [span] using hlength) htrace
  obtain ⟨runway, repeated, suffix, hsplit, hsimple, hrepeat⟩ :=
    first_revisit_split hnonsimple
  exact ⟨before, close, passages, runway, repeated, suffix,
    hbeforeAt, hcloseAt, by simpa [span] using hlength,
    htrace, hsplit, hsimple, hrepeat⟩

/-- **The serial branch has only the backward outcome.**

For five actual globally novel repeated-writer frames, a serial break forces
the first repeated switch in the first frame to retrace its complete caller
runway.  The absorbing branch of the first-revisit fork is impossible:
the selected later frame would repeat a writer either within the
switch-simple first lap (contradicting switch simplicity), or after the
cycle is grooved (contradicting global novelty).

The conclusion exposes the exact raw `stepN` return through the edge by
which the first frame was entered.  It does not assume a recursively
certified repair module and does not assume `IrreflexiveLinks`. -/
theorem five_serial_novelties_force_exact_caller_retrace
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
    ∃ before atRepeat repeatTime backSteps settled,
      stepN w a₀ start = some before ∧
      stepN w repeatTime start = some atRepeat ∧
      a₀ ≤ repeatTime ∧ repeatTime < z₀ ∧
      0 < backSteps ∧ backSteps ≤ N + 1 ∧
      stepN w backSteps atRepeat =
        (w.link before.1).map (fun ell => (ell, settled)) := by
  obtain ⟨before, close, passages, runway, repeated, suffix,
      hbefore, _hclose, hlength, htrace, hsplit, hsimple,
      hrepeatMem⟩ :=
    five_serial_novelties_force_first_repeated_switch
      hN H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  rw [hsplit] at htrace
  obtain ⟨atRepeat, hprefix, hafter⟩ := htrace.split_append
  obtain ⟨old, hold, hsameSwitch⟩ := List.mem_map.mp hrepeatMem
  obtain ⟨caller, body, hrunway⟩ := List.append_of_mem hold
  rw [hrunway] at hprefix
  obtain ⟨atOld, hcaller, hbody⟩ := hprefix.split_append
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  have hatOldPort : atOld.1 = p := hbody.head_arrive.1
  rcases atOld with ⟨oldPort, u₀⟩
  simp only at hatOldPort
  subst oldPort
  have hatRepeatPort : atRepeat.1 = q := hafter.head_arrive.1
  rcases atRepeat with ⟨repeatPort, u⟩
  simp only at hatRepeatPort
  subst repeatPort
  obtain ⟨v, hrepeat⟩ := hafter.head_arrive.2
  have hsimpleFrame :
      SwitchSimple (caller ++ (p, x) :: body) := by
    simpa [hrunway] using hsimple
  have hswitch : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  have hprefixSound :
      stepN w runway.length before = some (q, u) := by
    simpa [hrunway] using hprefix.sound
  let repeatTime := a₀ + runway.length
  have hrepeatAt :
      stepN w repeatTime start = some (q, u) := by
    dsimp [repeatTime]
    rw [stepN_add, hbefore]
    exact hprefixSound
  have hrunwayShort : runway.length < passages.length := by
    rw [hsplit]
    simp
  have hrepeatBeforeClose : repeatTime < z₀ := by
    dsimp [repeatTime]
    have hframeOrder := F₀.outer.order
    omega
  rcases hcaller.first_revisit_cycle_traces_or_retrace
      hbody hsimpleFrame hswitch hrepeat with hcycle | hretrace
  · obtain ⟨cycle, cycleState, hnonempty, htransient,
        hstable, hcycleSimple⟩ := hcycle
    rcases hserial with hs | hs | hs | hs
    · exact (serial_repeated_novel_after_simple_cycle_trace_false
        hrepeatAt htransient hstable hcycleSimple hnonempty
          F₁.outer H₁ (by omega)).elim
    · exact (serial_repeated_novel_after_simple_cycle_trace_false
        hrepeatAt htransient hstable hcycleSimple hnonempty
          F₂.outer H₂ (by omega)).elim
    · exact (serial_repeated_novel_after_simple_cycle_trace_false
        hrepeatAt htransient hstable hcycleSimple hnonempty
          F₃.outer H₃ (by omega)).elim
    · exact (serial_repeated_novel_after_simple_cycle_trace_false
        hrepeatAt htransient hstable hcycleSimple hnonempty
          F₄.outer H₄ (by omega)).elim
  · obtain ⟨settled, _hgrooved, _hcontact, hback⟩ := hretrace
    have hcallerSimple : SwitchSimple caller := by
      unfold SwitchSimple at hsimpleFrame ⊢
      simp only [List.map_append, List.map_cons] at hsimpleFrame
      exact (List.nodup_append.mp hsimpleFrame).1
    have hcallerLe : caller.length ≤ N :=
      hcaller.simple_length_le hN hcallerSimple
    exact ⟨before, (q, u), repeatTime, caller.length + 1, settled,
      hbefore, hrepeatAt, by omega, hrepeatBeforeClose,
      by omega, by omega, hback⟩

/-- Every reached configuration has an actual incoming edge when the initial
configuration has one.  At positive time that edge is the preceding
configuration's immutable exit connection. -/
private theorem reached_configuration_has_entry_edge
    {w : Wiring} {start reached : Nat × Tongues}
    {initialEdge k : Nat}
    (hentry : w.link initialEdge = some start.1)
    (hreach : stepN w k start = some reached) :
    ∃ edge, w.link edge = some reached.1 := by
  cases k with
  | zero =>
      have hreached : reached = start := by
        simpa [stepN] using Option.some.inj hreach.symm
      subst reached
      exact ⟨initialEdge, hentry⟩
  | succ k =>
      obtain ⟨before, hbefore⟩ := stepN_prefix_some
        (d := k) (K := k + 1) (by omega) hreach
      have hsplit := stepN_add w k 1 start
      rw [hreach, hbefore] at hsplit
      simp only [Option.bind_some] at hsplit
      have hone : stepN w 1 before = some reached := hsplit.symm
      have hstep : step w before = some reached := by
        simpa [stepN] using hone
      exact ⟨exitPort before, (step_some_parts hstep).1⟩

/-- **Pointwise serial-retrace certificate.**

The exact caller retrace forced by five serial novelties retains all data
needed by the novelty calculus:

* the caller's actual `PhysicalTrace`;
* the fact that every caller passage is grooved in the contact state;
* the contact equation at the repeated switch;
* the exact incoming edge and exact re-entry configuration; and
* a pointwise statement saying depth zero has the contact's old vector and
  every positive depth through the completed retrace has the one settled
  vector.

Consequently any sample contained in this backward segment has a
`NoveltyCoverOn ... 1` over any history already containing the contact's old
vector.  This is an unconditional conclusion from the five raw serial
frames, not a recursively assumed return certificate. -/
theorem five_serial_novelties_completed_retrace_one_novelty
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
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
    ∃ g base oldEntry mouthState q u settled edge repeatTime caller,
      stepN w a₀ start = some (g, base) ∧
      PhysicalTrace w (g, base) caller (oldEntry, mouthState) ∧
      SwitchSimple caller ∧
      PassagesGrooved settled caller ∧
      caller.length ≤ N ∧
      w.link edge = some g ∧
      stepN w repeatTime start = some (q, u) ∧
      a₀ ≤ repeatTime ∧ repeatTime < z₀ ∧
      repeatTime + caller.length + 1 ≤ z₀ ∧
      arrive u q = (oldEntry, settled) ∧
      stepN w (caller.length + 1) (q, u) = some (edge, settled) ∧
      (∀ d, d ≤ caller.length + 1 →
        ∃ port, stepN w d (q, u) =
          some (port, if d = 0 then u else settled)) ∧
      (∀ history times,
        VectorCount.restrict N u ∈ history →
        (∀ j, j ∈ times →
          repeatTime ≤ j ∧ j ≤ repeatTime + caller.length + 1) →
        NoveltyCoverOn w N start times history 1) := by
  obtain ⟨before, close, passages, runway, repeated, suffix,
      hbefore, _hclose, hlength, htrace, hsplit, hsimple,
      hrepeatMem⟩ :=
    five_serial_novelties_force_first_repeated_switch
      hN H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  rcases before with ⟨g, base⟩
  rw [hsplit] at htrace
  obtain ⟨atRepeat, hprefix, hafter⟩ := htrace.split_append
  obtain ⟨old, hold, hsameSwitch⟩ := List.mem_map.mp hrepeatMem
  obtain ⟨caller, body, hrunway⟩ := List.append_of_mem hold
  rw [hrunway] at hprefix
  obtain ⟨atOld, hcaller, hbody⟩ := hprefix.split_append
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  have hatOldPort : atOld.1 = p := hbody.head_arrive.1
  rcases atOld with ⟨oldPort, mouthState⟩
  simp only at hatOldPort
  subst oldPort
  have hatRepeatPort : atRepeat.1 = q := hafter.head_arrive.1
  rcases atRepeat with ⟨repeatPort, u⟩
  simp only at hatRepeatPort
  subst repeatPort
  obtain ⟨v, hrepeat⟩ := hafter.head_arrive.2
  have hsimpleFrame :
      SwitchSimple (caller ++ (p, x) :: body) := by
    simpa [hrunway] using hsimple
  have hcallerSimple : SwitchSimple caller := by
    unfold SwitchSimple at hsimpleFrame ⊢
    simp only [List.map_append, List.map_cons] at hsimpleFrame
    exact (List.nodup_append.mp hsimpleFrame).1
  have hcallerLe : caller.length ≤ N :=
    hcaller.simple_length_le hN hcallerSimple
  have hswitch : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  have hprefixSound :
      stepN w runway.length (g, base) = some (q, u) := by
    simpa [hrunway] using hprefix.sound
  let repeatTime := a₀ + runway.length
  have hrepeatAt :
      stepN w repeatTime start = some (q, u) := by
    dsimp [repeatTime]
    rw [stepN_add, hbefore]
    exact hprefixSound
  have hrunwayShort : runway.length < passages.length := by
    rw [hsplit]
    simp
  have hrepeatBeforeClose : repeatTime < z₀ := by
    dsimp [repeatTime]
    have hframeOrder := F₀.outer.order
    omega
  rcases hcaller.first_revisit_cycle_traces_or_retrace
      hbody hsimpleFrame hswitch hrepeat with hcycle | hretrace
  · obtain ⟨cycle, cycleState, hnonempty, htransient,
        hstable, hcycleSimple⟩ := hcycle
    rcases hserial with hs | hs | hs | hs
    · exact (serial_repeated_novel_after_simple_cycle_trace_false
        hrepeatAt htransient hstable hcycleSimple hnonempty
          F₁.outer H₁ (by omega)).elim
    · exact (serial_repeated_novel_after_simple_cycle_trace_false
        hrepeatAt htransient hstable hcycleSimple hnonempty
          F₂.outer H₂ (by omega)).elim
    · exact (serial_repeated_novel_after_simple_cycle_trace_false
        hrepeatAt htransient hstable hcycleSimple hnonempty
          F₃.outer H₃ (by omega)).elim
    · exact (serial_repeated_novel_after_simple_cycle_trace_false
        hrepeatAt htransient hstable hcycleSimple hnonempty
          F₄.outer H₄ (by omega)).elim
  · obtain ⟨settled, hgrooved, hcontact, hback⟩ := hretrace
    obtain ⟨edge, hedge⟩ :=
      reached_configuration_has_entry_edge hentry hbefore
    have hreverse : w.link g = some edge := w.symm _ _ hedge
    have hreturn :
        stepN w (caller.length + 1) (q, u) =
          some (edge, settled) := by
      simpa [hreverse] using hback
    have hpointwise : ∀ d, d ≤ caller.length + 1 →
        ∃ port, stepN w d (q, u) =
          some (port, if d = 0 then u else settled) :=
      (physicalTrace_contact_retraces_prefix_pointwise
        hcaller hgrooved hedge hcontact).2
    have hreturnBeforeClose :
        repeatTime + caller.length + 1 ≤ z₀ := by
      apply Classical.byContradiction
      intro hnot
      have hpostLe : z₀ + 1 ≤ repeatTime + caller.length + 1 := by
        omega
      let d := z₀ + 1 - repeatTime
      have hdPositive : 0 < d := by
        dsimp [d]
        omega
      have hdLe : d ≤ caller.length + 1 := by
        dsimp [d]
        omega
      have htimeD : repeatTime + d = z₀ + 1 := by
        dsimp [d]
        omega
      obtain ⟨portOne, hlocalOne⟩ := hpointwise 1 (by omega)
      have hglobalOne :
          stepN w (repeatTime + 1) start =
            some (portOne, settled) := by
        rw [stepN_add, hrepeatAt]
        simpa using hlocalOne
      obtain ⟨portPost, hlocalPost⟩ := hpointwise d hdLe
      have hglobalPost :
          stepN w (z₀ + 1) start =
            some (portPost, settled) := by
        rw [← htimeD, stepN_add, hrepeatAt]
        simpa [Nat.ne_of_gt hdPositive] using hlocalPost
      have hvector :
          restrictedTonguesAt w N start (repeatTime + 1) =
            restrictedTonguesAt w N start (z₀ + 1) := by
        simp [restrictedTonguesAt, tonguesAt,
          hglobalOne, hglobalPost]
      apply H₀.2.2
      apply List.mem_map.mpr
      exact ⟨repeatTime + 1,
        List.mem_range.mpr (by omega), hvector⟩
    have hcover : ∀ history times,
        VectorCount.restrict N u ∈ history →
        (∀ j, j ∈ times →
          repeatTime ≤ j ∧ j ≤ repeatTime + caller.length + 1) →
        NoveltyCoverOn w N start times history 1 := by
      intro history times hu htimes
      exact completed_retrace_at_one_novelty_cover
        hcaller hgrooved hedge hcontact hrepeatAt
          N history hu times htimes
    exact ⟨g, base, p, mouthState, q, u, settled, edge,
      repeatTime, caller, hbefore, hcaller, hcallerSimple,
      hgrooved, hcallerLe, hedge, hrepeatAt, by omega,
      hrepeatBeforeClose, hreturnBeforeClose, hcontact,
      hreturn, hpointwise, hcover⟩

/-! ## The later serial frame is an actual suffix frame -/

/-- A productive raw event rebases to any earlier reached configuration.
This is the exact time-shift operation needed after a completed caller
retrace. -/
private theorem rawProductiveAt_rebase
    {w : Wiring} {N shift time : Nat}
    {start middle : Nat × Tongues}
    (hshift : shift ≤ time)
    (hreach : stepN w shift start = some middle)
    (hprod : RawProductiveAt w N start time) :
    RawProductiveAt w N middle (time - shift) := by
  let d := time - shift
  have htime : shift + d = time := by
    dsimp [d]
    omega
  have hlocalPost : ∃ finish,
      stepN w (d + 1) middle = some finish := by
    obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hprod.1
    refine ⟨finish, ?_⟩
    rw [stepN_shift_eq hreach]
    have hsum : shift + (d + 1) = time + 1 := by omega
    rw [hsum]
    exact hfinish
  have hiff := RawProductiveAt.shift_iff (N := N) hreach hlocalPost
  rw [htime] at hiff
  exact hiff.mpr hprod

/-- Writer names rebase literally at a productive event. -/
private theorem rawWriterAt_rebase
    {w : Wiring} {N shift time : Nat}
    {start middle : Nat × Tongues}
    (hshift : shift ≤ time)
    (hreach : stepN w shift start = some middle)
    (hprod : RawProductiveAt w N start time) :
    rawWriterAt w middle (time - shift) =
      rawWriterAt w start time := by
  let d := time - shift
  have htime : shift + d = time := by
    dsimp [d]
    omega
  have hlocalProd := rawProductiveAt_rebase hshift hreach hprod
  obtain ⟨post, hpost⟩ := Option.isSome_iff_exists.mp hlocalProd.1
  obtain ⟨current, hcurrent⟩ := stepN_prefix_some
    (d := d) (K := d + 1) (by omega) hpost
  have hwriter := rawWriterAt_shift_eq hreach ⟨current, hcurrent⟩
  rw [htime] at hwriter
  exact hwriter

/-- A last-writer frame whose opening is after a reached suffix boundary is
still a last-writer frame in local suffix time. -/
private theorem RawLastWriterFrame.rebase
    {w : Wiring} {N shift left right : Nat}
    {start middle : Nat × Tongues}
    (F : RawLastWriterFrame w N start left right)
    (hshift : shift ≤ left)
    (hreach : stepN w shift start = some middle) :
    RawLastWriterFrame w N middle
      (left - shift) (right - shift) := by
  let localLeft := left - shift
  let localRight := right - shift
  have hleftTime : shift + localLeft = left := by
    dsimp [localLeft]
    omega
  have hrightTime : shift + localRight = right := by
    dsimp [localRight]
    have hright := F.order
    omega
  have hopen := rawProductiveAt_rebase hshift hreach F.open_productive
  have hshiftRight : shift ≤ right := by omega
  have hclose := rawProductiveAt_rebase
    hshiftRight hreach F.close_productive
  have hwriterOpen := rawWriterAt_rebase
    hshift hreach F.open_productive
  have hwriterClose := rawWriterAt_rebase
    hshiftRight hreach F.close_productive
  refine {
    order := by
      have hsum : shift + localLeft < shift + localRight := by
        rw [hleftTime, hrightTime]
        exact F.order
      omega
    open_productive := by simpa [localLeft] using hopen
    close_productive := by simpa [localRight] using hclose
    same_writer := ?_
    no_same_writer_between := ?_
  }
  · simpa [localLeft, localRight] using
      hwriterOpen.trans (F.same_writer.trans hwriterClose.symm)
  · intro j hjLeft hjRight hjProd
    have hjPost : ∃ finish,
        stepN w (j + 1) middle = some finish :=
      Option.isSome_iff_exists.mp hjProd.1
    have hjGlobalProd :
        RawProductiveAt w N start (shift + j) :=
      (RawProductiveAt.shift_iff hreach hjPost).mp hjProd
    have hjCurrent : ∃ current,
        stepN w j middle = some current := by
      obtain ⟨finish, hfinish⟩ := hjPost
      exact stepN_prefix_some (d := j) (K := j + 1)
        (by omega) hfinish
    have hjWriter := rawWriterAt_shift_eq hreach hjCurrent
    have hno := F.no_same_writer_between (shift + j)
      (by omega) (by omega) hjGlobalProd
    intro heq
    apply hno
    calc
      rawWriterAt w start (shift + j) =
          rawWriterAt w middle j := hjWriter.symm
      _ = rawWriterAt w middle localRight := by
        simpa [localRight] using heq
      _ = rawWriterAt w start right := by
        simpa [localRight] using hwriterClose

/-- A globally novel repeated close remains a novel repeated close after
rebasing at any boundary before its certified last-writer opening.  The
opening itself supplies the earlier local occurrence, and the local history
is a suffix of the global history. -/
private theorem RawRepeatedWriterNovelAt.rebase_after_frame
    {w : Wiring} {N shift left right : Nat}
    {start middle : Nat × Tongues}
    (H : RawRepeatedWriterNovelAt w N start right)
    (F : RawLastWriterFrame w N start left right)
    (hshift : shift ≤ left)
    (hreach : stepN w shift start = some middle) :
    RawRepeatedWriterNovelAt w N middle (right - shift) := by
  let localLeft := left - shift
  let localRight := right - shift
  have hleftTime : shift + localLeft = left := by
    dsimp [localLeft]
    omega
  have hrightTime : shift + localRight = right := by
    dsimp [localRight]
    have hright := F.order
    omega
  have hpostTime : shift + (localRight + 1) = right + 1 := by
    calc
      shift + (localRight + 1) = (shift + localRight) + 1 :=
        (Nat.add_assoc shift localRight 1).symm
      _ = right + 1 := congrArg (fun t => t + 1) hrightTime
  have localFrame := F.rebase hshift hreach
  refine ⟨localFrame.close_productive, ?_, ?_⟩
  · intro hfirst
    have hne := hfirst.2 localLeft localFrame.order
      localFrame.open_productive
    exact hne localFrame.same_writer
  · intro hseen
    obtain ⟨j, hj, hvector⟩ := List.mem_map.mp hseen
    have hjLt : j < localRight + 1 := List.mem_range.mp hj
    obtain ⟨post, hpost⟩ :=
      Option.isSome_iff_exists.mp localFrame.close_productive.1
    obtain ⟨earlier, hearlier⟩ := stepN_prefix_some
      (d := j) (K := localRight + 1) (by omega) hpost
    have hpostShift := restrictedTonguesAt_shift_eq
      (N := N) hreach ⟨post, hpost⟩
    have hearlierShift := restrictedTonguesAt_shift_eq
      (N := N) hreach ⟨earlier, hearlier⟩
    apply H.2.2
    apply List.mem_map.mpr
    refine ⟨shift + j, List.mem_range.mpr (by omega), ?_⟩
    calc
      restrictedTonguesAt w N start (shift + j) =
          restrictedTonguesAt w N middle j := hearlierShift.symm
      _ = restrictedTonguesAt w N middle (localRight + 1) := hvector
      _ = restrictedTonguesAt w N start
          (shift + (localRight + 1)) := hpostShift
      _ = restrictedTonguesAt w N start (right + 1) := by rw [hpostTime]

/-- **Serial continuation is extracted, not assumed.**

The pointwise completed retrace ends by `z₀`.  Whichever later frame witnesses
`FiveFrameSerialBreak` opens at or after `z₀`, hence after the exact return.
After rebasing at that return configuration, the later close is still a
globally novel repeated-writer event with its complete `RawLastWriterFrame`.
This is the actual suffix datum required for recursive serial composition. -/
theorem five_serial_novelties_reenter_before_rebased_later_frame
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
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
    ∃ edge settled returnTime laterOpen laterClose,
      stepN w returnTime start = some (edge, settled) ∧
      returnTime ≤ z₀ ∧ z₀ ≤ laterOpen ∧ laterOpen < laterClose ∧
      RawLastWriterFrame w N start laterOpen laterClose ∧
      RawRepeatedWriterNovelAt w N start laterClose ∧
      RawLastWriterFrame w N (edge, settled)
        (laterOpen - returnTime) (laterClose - returnTime) ∧
      RawRepeatedWriterNovelAt w N (edge, settled)
        (laterClose - returnTime) := by
  obtain ⟨g, base, oldEntry, mouthState, q, u, settled, edge,
      repeatTime, caller, hbefore, hcaller, hcallerSimple,
      hgrooved, hcallerLe, hedge, hrepeatAt, hopen,
      hrepeatClose, hreturnClose, hcontact, hreturn,
      hpointwise, hcover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  let returnTime := repeatTime + caller.length + 1
  have habsoluteReturn :
      stepN w returnTime start = some (edge, settled) := by
    dsimp [returnTime]
    rw [show repeatTime + caller.length + 1 =
        repeatTime + (caller.length + 1) by omega,
      stepN_add, hrepeatAt]
    exact hreturn
  have hreturnLe : returnTime ≤ z₀ := by
    simpa [returnTime, Nat.add_assoc] using hreturnClose
  rcases hserial with hs | hs | hs | hs
  · refine ⟨edge, settled, returnTime, a₁, z₁,
      habsoluteReturn, hreturnLe, hs, F₁.outer.order,
      F₁.outer, H₁, ?_, ?_⟩
    · exact F₁.outer.rebase (by omega) habsoluteReturn
    · exact H₁.rebase_after_frame F₁.outer (by omega) habsoluteReturn
  · refine ⟨edge, settled, returnTime, a₂, z₂,
      habsoluteReturn, hreturnLe, hs, F₂.outer.order,
      F₂.outer, H₂, ?_, ?_⟩
    · exact F₂.outer.rebase (by omega) habsoluteReturn
    · exact H₂.rebase_after_frame F₂.outer (by omega) habsoluteReturn
  · refine ⟨edge, settled, returnTime, a₃, z₃,
      habsoluteReturn, hreturnLe, hs, F₃.outer.order,
      F₃.outer, H₃, ?_, ?_⟩
    · exact F₃.outer.rebase (by omega) habsoluteReturn
    · exact H₃.rebase_after_frame F₃.outer (by omega) habsoluteReturn
  · refine ⟨edge, settled, returnTime, a₄, z₄,
      habsoluteReturn, hreturnLe, hs, F₄.outer.order,
      F₄.outer, H₄, ?_, ?_⟩
    · exact F₄.outer.rebase (by omega) habsoluteReturn
    · exact H₄.rebase_after_frame F₄.outer (by omega) habsoluteReturn

/-- Encountering an external self-link is an exact identity reflection.
After the preceding passage exits through the self-linked port, the next
step traverses that passage backwards and leaves over the preceding entry's
external edge, without changing the returned tongue state. -/
theorem self_link_exit_bounces
    {w : Wiring} {before after : Nat × Tongues}
    (hstep : step w before = some after)
    (hself : w.link (exitPort before) = some (exitPort before)) :
    step w after =
      (w.link before.1).map (fun q => (q, after.2)) := by
  have hparts := step_some_parts hstep
  have hentry : after.1 = exitPort before := by
    rw [hself] at hparts
    exact Option.some.inj hparts.1.symm
  have hback := (step_grooves hstep).1
  unfold step
  rw [hentry, hback]

/-- A self-linked branch, with its stem connected to `outside`, is a
two-step identity reflector whenever that branch is selected. This is the
local lobe/reflector theorem needed for the self-link branch of `StateLaw`;
it is not an irreflexivity assumption. -/
theorem self_linked_branch_is_identity_reflector
    {w : Wiring} {branch outside : Nat}
    (hbranch : branch % 3 ≠ 0)
    (hself : w.link branch = some branch)
    (hmouth : w.link (3 * (branch / 3)) = some outside) :
    IsReflector w (3 * (branch / 3)) outside 2
      (fun state => state (branch / 3) = bval branch)
      (fun state => state) := by
  intro state hselected
  have hpin : pin state branch = state :=
    pin_of_agrees hselected
  have hgroove :
      arrive state branch = (3 * (branch / 3), state) := by
    simp [arrive, hbranch, hpin]
  obtain ⟨hstep, _⟩ :=
    self_edge_groove_isReflector w hself hmouth state hgroove
  exact ⟨hstep, hselected⟩

/-- A fixed canonical echo jump used by a certified concrete run is exactly
an external self-link in the underlying raw wiring. This is the missing
non-irreflexive branch of the physical triple obstruction. -/
theorem certified_fixed_bar_has_self_link
    {w : Wiring} (run : CertifiedConcreteEchoRun w) {q : Nat}
    (hfixed :
      (canonicalEchoMachine w).bar (encodedEntries run.entry q) =
        encodedEntries run.entry q) :
    ∃ p, w.link p = some p := by
  let p := run.toConcreteAscentTrace.entry q
  have hencoded : encodeSlot (wireBar w p) = encodeSlot p := by
    simpa [p, encodedEntries, canonicalEchoMachine,
      encodedMachine, encodedBar_encodeSlot] using hfixed
  have hwire : wireBar w p = p := encodeSlot_injective hencoded
  have hslot := run.toConcreteAscentTrace.freeSlot q
  have hlink : w.link p = some (wireBar w p) := by
    simpa [p] using hslot.2.2.1
  rw [hwire] at hlink
  exact ⟨p, hlink⟩

/-- The raw third branch carried by a canonical fixed jump: a realised
self-linked branch whose selected local passage is a two-step identity
reflector. -/
def HasSelfLinkIdentityReflector (w : Wiring) : Prop :=
  ∃ branch outside,
    w.link branch = some branch ∧
    IsReflector w (3 * (branch / 3)) outside 2
      (fun state => state (branch / 3) = bval branch)
      (fun state => state)

private theorem descentEntry_stem_link_exists
    {w : Wiring} {p : Nat} (hp : IsDescentEntry w p) :
    ∃ outside, w.link (3 * (p / 3)) = some outside := by
  obtain ⟨state, tail, landing, finish, descent⟩ := hp
  cases descent with
  | last _ hlink _ => exact ⟨_, hlink⟩
  | cons _ hlink _ _ => exact ⟨_, hlink⟩

/-- Strengthening of `certified_fixed_bar_has_self_link`: the self-link
alternative already carries its exact raw identity-reflector semantics. -/
theorem certified_fixed_bar_has_identity_reflector
    {w : Wiring} (run : CertifiedConcreteEchoRun w) {q : Nat}
    (hfixed :
      (canonicalEchoMachine w).bar (encodedEntries run.entry q) =
        encodedEntries run.entry q) :
    HasSelfLinkIdentityReflector w := by
  let branch := run.toConcreteAscentTrace.entry q
  have hencoded : encodeSlot (wireBar w branch) = encodeSlot branch := by
    simpa [branch, encodedEntries, canonicalEchoMachine,
      encodedMachine, encodedBar_encodeSlot] using hfixed
  have hwire : wireBar w branch = branch :=
    encodeSlot_injective hencoded
  have hslot := run.toConcreteAscentTrace.freeSlot q
  have hlink : w.link branch = some (wireBar w branch) := by
    simpa [branch] using hslot.2.2.1
  rw [hwire] at hlink
  have hentry : IsDescentEntry w branch := by
    simpa [branch] using hslot.1
  have hbranch : branch % 3 ≠ 0 := by
    simpa [branch] using hslot.2.1
  obtain ⟨outside, hmouth⟩ :=
    descentEntry_stem_link_exists hentry
  exact ⟨branch, outside, hlink,
    self_linked_branch_is_identity_reflector
      hbranch hlink hmouth⟩

/-- Three closing frames whose openings and closings have the same order:
`a₀ < a₁ < a₂ < z₀ < z₁ < z₂`. -/
def EndpointABCABC
    (a₀ z₀ a₁ z₁ a₂ z₂ : Nat) : Prop :=
  a₀ < a₁ ∧ a₁ < a₂ ∧ a₂ < z₀ ∧ z₀ < z₁ ∧ z₁ < z₂

/-- Three strictly nested closing frames:
`a₂ < a₁ < a₀ < z₀ < z₁ < z₂`. -/
def EndpointStrictNest
    (a₀ z₀ a₁ z₁ a₂ z₂ : Nat) : Prop :=
  a₂ < a₁ ∧ a₁ < a₀ ∧ a₀ < z₀ ∧ z₀ < z₁ ∧ z₁ < z₂

def EndpointTripleOutcome
    (a₀ z₀ a₁ z₁ a₂ z₂ : Nat) : Prop :=
  EndpointABCABC a₀ z₀ a₁ z₁ a₂ z₂ ∨
  EndpointStrictNest a₀ z₀ a₁ z₁ a₂ z₂

/-- One of the ten chronological triples selected from five frames is an
`ABCABC` interlacement or a strict nest. -/
def FiveFrameABCABC
    (a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat) : Prop :=
  EndpointABCABC a₀ z₀ a₁ z₁ a₂ z₂ ∨
  EndpointABCABC a₀ z₀ a₁ z₁ a₃ z₃ ∨
  EndpointABCABC a₀ z₀ a₁ z₁ a₄ z₄ ∨
  EndpointABCABC a₀ z₀ a₂ z₂ a₃ z₃ ∨
  EndpointABCABC a₀ z₀ a₂ z₂ a₄ z₄ ∨
  EndpointABCABC a₀ z₀ a₃ z₃ a₄ z₄ ∨
  EndpointABCABC a₁ z₁ a₂ z₂ a₃ z₃ ∨
  EndpointABCABC a₁ z₁ a₂ z₂ a₄ z₄ ∨
  EndpointABCABC a₁ z₁ a₃ z₃ a₄ z₄ ∨
  EndpointABCABC a₂ z₂ a₃ z₃ a₄ z₄

def FiveFrameStrictNest
    (a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat) : Prop :=
  EndpointStrictNest a₀ z₀ a₁ z₁ a₂ z₂ ∨
  EndpointStrictNest a₀ z₀ a₁ z₁ a₃ z₃ ∨
  EndpointStrictNest a₀ z₀ a₁ z₁ a₄ z₄ ∨
  EndpointStrictNest a₀ z₀ a₂ z₂ a₃ z₃ ∨
  EndpointStrictNest a₀ z₀ a₂ z₂ a₄ z₄ ∨
  EndpointStrictNest a₀ z₀ a₃ z₃ a₄ z₄ ∨
  EndpointStrictNest a₁ z₁ a₂ z₂ a₃ z₃ ∨
  EndpointStrictNest a₁ z₁ a₂ z₂ a₄ z₄ ∨
  EndpointStrictNest a₁ z₁ a₃ z₃ a₄ z₄ ∨
  EndpointStrictNest a₂ z₂ a₃ z₃ a₄ z₄

def FiveFrameTripleOutcome
    (a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat) : Prop :=
  FiveFrameABCABC a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ ∨
  FiveFrameStrictNest a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄

private theorem fiveOutcome012
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inl habc)
  · exact Or.inr (Or.inl hnest)

private theorem fiveOutcome013
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₀ z₀ a₁ z₁ a₃ z₃) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inr (Or.inl habc))
  · exact Or.inr (Or.inr (Or.inl hnest))

private theorem fiveOutcome123
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₁ z₁ a₂ z₂ a₃ z₃) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl habc)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl hnest)))))))

private theorem fiveOutcome134
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₁ z₁ a₃ z₃ a₄ z₄) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl habc)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl hnest)))))))))

private theorem fiveOutcome234
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (h : EndpointTripleOutcome a₂ z₂ a₃ z₃ a₄ z₄) :
    FiveFrameTripleOutcome a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases h with habc | hnest
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr habc)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr hnest)))))))))

/-- The order-theoretic core: five distinct openings before the first of
five ordered closings contain an increasing or decreasing triple. This is
the five-term Erdős-Szekeres argument discharged in Presburger arithmetic,
not an enumeration of switch systems. -/
theorem five_distinct_common_openings_have_triple
    {a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ : Nat}
    (hz01 : z₀ < z₁) (hz12 : z₁ < z₂)
    (hz23 : z₂ < z₃) (hz34 : z₃ < z₄)
    (ha0 : a₀ < z₀)
    (hcommon : a₁ < z₀ ∧ a₂ < z₀ ∧ a₃ < z₀ ∧ a₄ < z₀)
    (hn01 : a₀ ≠ a₁) (hn02 : a₀ ≠ a₂)
    (hn03 : a₀ ≠ a₃) (hn04 : a₀ ≠ a₄)
    (hn12 : a₁ ≠ a₂) (hn13 : a₁ ≠ a₃)
    (hn14 : a₁ ≠ a₄) (hn23 : a₂ ≠ a₃)
    (hn24 : a₂ ≠ a₄) (hn34 : a₃ ≠ a₄) :
    FiveFrameTripleOutcome
      a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  by_cases h01 : a₀ < a₁
  · by_cases h12 : a₁ < a₂
    · apply fiveOutcome012
      left
      unfold EndpointABCABC
      omega
    · by_cases h23 : a₂ < a₃
      · by_cases h34 : a₃ < a₄
        · apply fiveOutcome234
          left
          unfold EndpointABCABC
          omega
        · by_cases h13 : a₁ < a₃
          · apply fiveOutcome013
            left
            unfold EndpointABCABC
            omega
          · apply fiveOutcome134
            right
            unfold EndpointStrictNest
            omega
      · apply fiveOutcome123
        right
        unfold EndpointStrictNest
        omega
  · by_cases h12 : a₁ < a₂
    · by_cases h23 : a₂ < a₃
      · apply fiveOutcome123
        left
        unfold EndpointABCABC
        omega
      · by_cases h34 : a₃ < a₄
        · by_cases h31 : a₃ < a₁
          · apply fiveOutcome013
            right
            unfold EndpointStrictNest
            omega
          · apply fiveOutcome134
            left
            unfold EndpointABCABC
            omega
        · apply fiveOutcome234
          right
          unfold EndpointStrictNest
          omega
    · apply fiveOutcome012
      right
      unfold EndpointStrictNest
      omega

/-- Five common-overlap raw last-writer frames therefore contain the exact
triple endpoint pattern needed by the curve-shrink/`ABCABC` obstruction. -/
theorem five_common_raw_closing_frames_have_triple
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {a₀ q₀ z₀ a₁ q₁ z₁ a₂ q₂ z₂ a₃ q₃ z₃ a₄ q₄ z₄ : Nat}
    (hz01 : z₀ < z₁) (hz12 : z₁ < z₂)
    (hz23 : z₂ < z₃) (hz34 : z₃ < z₄)
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hcommon : a₁ < z₀ ∧ a₂ < z₀ ∧ a₃ < z₀ ∧ a₄ < z₀) :
    FiveFrameTripleOutcome
      a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  have hz02 : z₀ < z₂ := Nat.lt_trans hz01 hz12
  have hz03 : z₀ < z₃ := Nat.lt_trans hz02 hz23
  have hz04 : z₀ < z₄ := Nat.lt_trans hz03 hz34
  have hz13 : z₁ < z₃ := Nat.lt_trans hz12 hz23
  have hz14 : z₁ < z₄ := Nat.lt_trans hz13 hz34
  have hz24 : z₂ < z₄ := Nat.lt_trans hz23 hz34
  exact five_distinct_common_openings_have_triple
    hz01 hz12 hz23 hz34 F₀.outer.order hcommon
    (rawLastWriterFrame_open_ne_of_close_lt hz01 F₀.outer F₁.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz02 F₀.outer F₂.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz03 F₀.outer F₃.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz04 F₀.outer F₄.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz12 F₁.outer F₂.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz13 F₁.outer F₃.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz14 F₁.outer F₄.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz23 F₂.outer F₃.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz24 F₂.outer F₄.outer)
    (rawLastWriterFrame_open_ne_of_close_lt hz34 F₃.outer F₄.outer)

/-- Once strict three-frame nesting has been excluded, five common-overlap
frames force an actual `ABCABC` endpoint interlacement. -/
theorem five_common_raw_closing_frames_abcabc_of_no_nest
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {a₀ q₀ z₀ a₁ q₁ z₁ a₂ q₂ z₂ a₃ q₃ z₃ a₄ q₄ z₄ : Nat}
    (hz01 : z₀ < z₁) (hz12 : z₁ < z₂)
    (hz23 : z₂ < z₃) (hz34 : z₃ < z₄)
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hcommon : a₁ < z₀ ∧ a₂ < z₀ ∧ a₃ < z₀ ∧ a₄ < z₀)
    (hnoNest : ¬ FiveFrameStrictNest
      a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄) :
    FiveFrameABCABC a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄ := by
  rcases five_common_raw_closing_frames_have_triple
      hz01 hz12 hz23 hz34 F₀ F₁ F₂ F₃ F₄ hcommon with
    habc | hnest
  · exact habc
  · exact (hnoNest hnest).elim

/-- Exact conditional non-coexistence statement. The only hypotheses still
needed from the two geometric programmes are exclusion of the grouped
`ABCABC` and strict-nest endpoint patterns; no counting assumption remains
inside this theorem. -/
theorem five_common_raw_closing_frames_impossible
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {a₀ q₀ z₀ a₁ q₁ z₁ a₂ q₂ z₂ a₃ q₃ z₃ a₄ q₄ z₄ : Nat}
    (hz01 : z₀ < z₁) (hz12 : z₁ < z₂)
    (hz23 : z₂ < z₃) (hz34 : z₃ < z₄)
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hcommon : a₁ < z₀ ∧ a₂ < z₀ ∧ a₃ < z₀ ∧ a₄ < z₀)
    (hnoABCABC : ¬ FiveFrameABCABC
      a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄)
    (hnoNest : ¬ FiveFrameStrictNest
      a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄) :
    False := by
  exact hnoABCABC
    (five_common_raw_closing_frames_abcabc_of_no_nest
      hz01 hz12 hz23 hz34 F₀ F₁ F₂ F₃ F₄ hcommon hnoNest)

/-- **Five-frame raw obstruction.** Five chronologically closing repeated
novelties either split serially at the first close, or reduce to one exact
`ABCABC`/strict-nest triple. Every returned frame retains its proved
fresh-or-interlacing parity witness. -/
theorem five_repeated_novelties_serial_or_triple
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (hz01 : z₀ < z₁) (hz12 : z₁ < z₂)
    (hz23 : z₂ < z₃) (hz34 : z₃ < z₄)
    (h₀ : RawRepeatedWriterNovelAt w N start z₀)
    (h₁ : RawRepeatedWriterNovelAt w N start z₁)
    (h₂ : RawRepeatedWriterNovelAt w N start z₂)
    (h₃ : RawRepeatedWriterNovelAt w N start z₃)
    (h₄ : RawRepeatedWriterNovelAt w N start z₄) :
    ∃ a₀ q₀ a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄,
      RawNovelClosingFrame w N start a₀ q₀ z₀ ∧
      RawNovelClosingFrame w N start a₁ q₁ z₁ ∧
      RawNovelClosingFrame w N start a₂ q₂ z₂ ∧
      RawNovelClosingFrame w N start a₃ q₃ z₃ ∧
      RawNovelClosingFrame w N start a₄ q₄ z₄ ∧
      (FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄ ∨
       FiveFrameTripleOutcome
         a₀ z₀ a₁ z₁ a₂ z₂ a₃ z₃ a₄ z₄) := by
  obtain ⟨a₀, q₀, F₀⟩ := h₀.novelClosingFrame hN
  obtain ⟨a₁, q₁, F₁⟩ := h₁.novelClosingFrame hN
  obtain ⟨a₂, q₂, F₂⟩ := h₂.novelClosingFrame hN
  obtain ⟨a₃, q₃, F₃⟩ := h₃.novelClosingFrame hN
  obtain ⟨a₄, q₄, F₄⟩ := h₄.novelClosingFrame hN
  refine ⟨a₀, q₀, a₁, q₁, a₂, q₂, a₃, q₃, a₄, q₄,
    F₀, F₁, F₂, F₃, F₄, ?_⟩
  by_cases hcommon : a₁ < z₀ ∧ a₂ < z₀ ∧ a₃ < z₀ ∧ a₄ < z₀
  · exact Or.inr (five_common_raw_closing_frames_have_triple
      hz01 hz12 hz23 hz34 F₀ F₁ F₂ F₃ F₄ hcommon)
  · left
    unfold FiveFrameSerialBreak
    omega

end GeneralN

namespace Echo

/-- Physical triple-interlacement obstruction without silently assuming
external irreflexivity. The abstract fixed-jump alternative is transported
back to its exact raw meaning: a self-linked external port. -/
theorem physical_cyclic_minimal_stable_blocker_lobe_replay_or_identity_reflector
    {w : GeneralN.Wiring}
    (run : GeneralN.CertifiedConcreteEchoRun w)
    {K p t₀ u₀ t₁ u₁ b j : Nat}
    (hper : RestorationPeriodicTail
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p t₀ u₀ t₁ u₁)
    (hKb : K ≤ b)
    (ht1b : t₁ < b)
    (hbu0 : b < u₀)
    (hstable : StableBlockerUntil
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister b j) :
    (∃ k, ExactLobeWrite
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister k) ∨
    EarlierCompleteStateReplay
      (GeneralN.canonicalEchoMachine w)
      (GeneralN.encodedEntries run.entry)
      run.initialRegister K p ∨
    GeneralN.HasSelfLinkIdentityReflector w := by
  have hout := cyclic_minimal_stable_blocker_obstruction
    (GeneralN.canonicalEchoMachine w)
    (GeneralN.encodedEntries run.entry)
    run.initialRegister
    (GeneralN.certifiedConcreteEcho_isRun run)
    run.initialWellFormed
    hper hmin hKb ht1b hbu0 hstable
  rcases hout with hlobe | hreplay | hfixed
  · exact Or.inl hlobe
  · exact Or.inr (Or.inl hreplay)
  · obtain ⟨q, hq⟩ := hfixed
    exact Or.inr (Or.inr
      (GeneralN.certified_fixed_bar_has_identity_reflector run hq))

end Echo
