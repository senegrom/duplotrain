import RunwayHistoricalThree
import SharpStateLawAssembly
import FiveFrameObstruction

/-!
# Closing the sharp certificate from a raw five-frame tail

This file isolates the exact global-history extraction still needed by the
sharp state law.  The local runway/candy analysis is already complete:
`runway_or_candy_absolute_three_novelty` says that, once the construction
lead is historical, the entire changed-forward tail has at most three fresh
tongue vectors.

The remaining raw obstruction is therefore very concrete.  Five ordered
repeated-writer novelties provide five fixed-stem open rerouting frames.  If
the physical global construction turns those frames into a changed-forward
tail before the second novelty, the last four post-vectors are all globally
novel, pairwise distinct, and yet must lie in a list of length at most three.
That is impossible.

The theorem `knownEdgeFourRepeatedWriterNovelty_of_fiveFrameRunwayExtraction`
below performs all finite-prefix extraction, time shifting, novelty, and
counting.  Its sole hypothesis is the remaining geometric statement
`KnownEdgeFiveFrameRunwayExtraction`, stated over the explicit raw frames.
There is no residual list-counting assumption in that hypothesis.
-/

namespace GeneralN

/-- The vectors occurring strictly before `bound` in the original raw run. -/
def rawPrefixHistory (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (bound : Nat) : List (List Bool) :=
  (List.range bound).map (restrictedTonguesAt w N start)

/-- A globally novel post-vector is absent from every shorter prefix history. -/
theorem RawNovelAt.not_mem_rawPrefixHistory
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {k bound : Nat}
    (h : RawNovelAt w N start k) (hbound : bound ≤ k + 1) :
    restrictedTonguesAt w N start (k + 1) ∉
      rawPrefixHistory w N start bound := by
  intro hmem
  apply h
  obtain ⟨j, hj, hjv⟩ := List.mem_map.mp hmem
  apply List.mem_map.mpr
  refine ⟨j, List.mem_range.mpr ?_, hjv⟩
  have hjlt : j < bound := List.mem_range.mp hj
  omega

/-- A raw trajectory shifted to a reached configuration has exactly the same
restricted tongue vectors. -/
theorem restrictedTonguesAt_add_of_reach
    {w : Wiring} {N shift d : Nat}
    {start middle finish : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hfinish : stepN w d middle = some finish) :
    restrictedTonguesAt w N start (shift + d) =
      restrictedTonguesAt w N middle d := by
  simp [restrictedTonguesAt, tonguesAt, stepN_add, hreach, hfinish]

/-- A successful absolute suffix of a reached raw configuration is a
successful local suffix.  This tiny transport fact lets the global-history
argument use the local changed-forward novelty theorem without assuming an
all-time liveness oracle. -/
theorem stepN_suffix_some_of_reach
    {w : Wiring} {shift d : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hglobal : (stepN w (shift + d) start).isSome) :
    ∃ finish, stepN w d middle = some finish := by
  rw [stepN_add, hreach] at hglobal
  simpa using (Option.isSome_iff_exists.mp hglobal)

/-- Transport one live post-time from an ambient raw run to a reached local
run. -/
theorem restrictedTonguesAt_sub_of_reach
    {w : Wiring} {N shift t : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hshift : shift ≤ t)
    (hlive : (stepN w t start).isSome) :
    restrictedTonguesAt w N start t =
      restrictedTonguesAt w N middle (t - shift) := by
  have ht : t = shift + (t - shift) := by omega
  have hglobal' :
      (stepN w (shift + (t - shift)) start).isSome := by
    rw [← ht]
    exact hlive
  obtain ⟨finish, hfinish⟩ := stepN_suffix_some_of_reach
    hreach hglobal'
  have htransport := restrictedTonguesAt_add_of_reach
    (N := N) hreach hfinish
  rw [← ht] at htransport
  exact htransport

/-- Raw writer names are invariant under shifting to a reached local run. -/
theorem rawWriterAt_add_of_reach
    {w : Wiring} {shift d : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : (stepN w d middle).isSome) :
    rawWriterAt w start (shift + d) =
      rawWriterAt w middle d := by
  obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hlive
  simp [rawWriterAt, rawEntryAt, stepN_add, hreach, hfinish]

/-- A productive event in an ambient run remains productive after shifting
to a previously reached configuration. -/
theorem rawProductiveAt_sub_of_reach
    {w : Wiring} {N shift d : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hprod : RawProductiveAt w N start (shift + d)) :
    RawProductiveAt w N middle d := by
  have hpostGlobal :
      (stepN w (shift + (d + 1)) start).isSome := by
    simpa [Nat.add_assoc] using hprod.1
  obtain ⟨post, hpost⟩ := stepN_suffix_some_of_reach
    hreach hpostGlobal
  obtain ⟨pre, hpre⟩ := stepN_prefix_some
    (d := d) (K := d + 1) (by omega) hpost
  refine ⟨by simp [hpost], ?_⟩
  intro heq
  apply hprod.2
  have hpostVector := restrictedTonguesAt_add_of_reach
    (N := N) hreach hpost
  have hpreVector := restrictedTonguesAt_add_of_reach
    (N := N) hreach hpre
  calc
    restrictedTonguesAt w N start (shift + d + 1) =
        restrictedTonguesAt w N middle (d + 1) := by
          simpa [Nat.add_assoc] using hpostVector
    _ = restrictedTonguesAt w N middle d := heq
    _ = restrictedTonguesAt w N start (shift + d) :=
      hpreVector.symm

/-- The raw writer at any time inside a physical trace is the switch label
of one of that trace's recorded passages. -/
theorem PhysicalTrace.rawWriterAt_mem_passageSwitches
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    ∀ {k : Nat}, k < passages.length →
      rawWriterAt w start k ∈ passages.map passageSwitch := by
  intro k hk
  induction htrace generalizing k with
  | nil => simp at hk
  | @cons p x q u v passages finish harrive hlink tail ih =>
      cases k with
      | zero =>
          simp [rawWriterAt, rawEntryAt, stepN, passageSwitch]
      | succ k =>
          have hkTail : k < passages.length := by
            simp only [List.length_cons] at hk
            omega
          have hstep : step w (p, u) = some (q, v) := by
            simp [step, harrive, hlink]
          have hreach : stepN w 1 (p, u) = some (q, v) := by
            simpa [stepN] using hstep
          obtain ⟨cfg, hcfg⟩ := stepN_prefix_some
            (d := k) (K := passages.length)
            (Nat.le_of_lt hkTail) tail.sound
          have hcfgSome : (stepN w k (q, v)).isSome := by
            rw [hcfg]
            simp
          have hwriter := rawWriterAt_add_of_reach
            hreach hcfgSome
          have hmem := ih hkTail
          apply List.mem_cons_of_mem
          rw [← hwriter] at hmem
          simpa [Nat.one_add] using hmem

/-- At a time inside a physical trace, the raw writer is exactly the switch
recorded at the same position of the passage list.  Unlike mere membership,
this time-indexed form lets switch simplicity rule out every earlier writer. -/
theorem PhysicalTrace.rawWriterAt_eq_passageSwitch_getElem
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    ∀ {k : Nat} (hk : k < passages.length),
      rawWriterAt w start k = passageSwitch passages[k] := by
  intro k hk
  induction htrace generalizing k with
  | nil => simp at hk
  | @cons p x q u v passages finish harrive hlink tail ih =>
      cases k with
      | zero =>
          simp [rawWriterAt, rawEntryAt, stepN, passageSwitch]
      | succ k =>
          have hkTail : k < passages.length := by
            simp only [List.length_cons] at hk
            omega
          have hstep : step w (p, u) = some (q, v) := by
            simp [step, harrive, hlink]
          have hreach : stepN w 1 (p, u) = some (q, v) := by
            simpa [stepN] using hstep
          obtain ⟨cfg, hcfg⟩ := stepN_prefix_some
            (d := k) (K := passages.length)
            (Nat.le_of_lt hkTail) tail.sound
          have hcfgSome : (stepN w k (q, v)).isSome := by
            rw [hcfg]
            simp
          have hwriter := rawWriterAt_add_of_reach hreach hcfgSome
          have htail := ih hkTail
          simpa [Nat.one_add] using hwriter.trans htail

/-- Every productive event inside a switch-simple physical construction is
globally the first productive event of its writer.  This is the raw-history
extraction missing from the older five-frame formulation: passage simplicity
controls the complete absolute run prefix, not merely a local certificate. -/
theorem PhysicalTrace.rawProductiveAt_first_of_switchSimple
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    ∀ {k : Nat}, k < passages.length →
      RawProductiveAt w N start k →
      RawFirstWriterAt w N start k := by
  intro k hk hprod
  refine ⟨hprod, ?_⟩
  intro j hj hprodj hwriter
  have hjBound : j < passages.length := Nat.lt_trans hj hk
  have hwriterJ := htrace.rawWriterAt_eq_passageSwitch_getElem hjBound
  have hwriterK := htrace.rawWriterAt_eq_passageSwitch_getElem hk
  have hpair := List.pairwise_iff_getElem.mp hsimple
  have hne := hpair j k (by simpa using hjBound) (by simpa using hk) hj
  apply hne
  simpa [hwriterJ, hwriterK] using hwriter

/-- A switch-simple physical construction prefix contains no repeated-writer
novelty event.  This is the event-level form of the global history
extraction, and follows from the time-indexed passage theorem above. -/
theorem PhysicalTrace.rawRepeatedWriterNovelTimes_eq_nil_of_switchSimple
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    rawRepeatedWriterNovelTimes w N start passages.length = [] := by
  classical
  cases htimes : rawRepeatedWriterNovelTimes w N start passages.length with
  | nil => rfl
  | cons k rest =>
      exfalso
      have hkMem :
          k ∈ rawRepeatedWriterNovelTimes w N start passages.length := by
        rw [htimes]
        exact List.mem_cons_self
      have hkData := mem_rawRepeatedWriterNovelTimes_iff.mp hkMem
      have hkFirst := htrace.rawProductiveAt_first_of_switchSimple
        hsimple hkData.1 hkData.2.1
      exact hkData.2.2.1 hkFirst

/-- Every state of a switch-simple physical construction prefix belongs to
the canonical initial-plus-first-writer history.  This is an unconditional
global raw-history extraction, including the endpoint of the trace. -/
theorem PhysicalTrace.restrictedTonguesAt_mem_rawFirstWriterHistory
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    ∀ k, k ≤ passages.length →
      restrictedTonguesAt w N start k ∈
        rawFirstWriterHistory w N start passages.length := by
  classical
  intro k hk
  have hcover := restrictedTonguesAt_mem_finite_writer_cover
    w N start passages.length k hk
  have hempty :=
    htrace.rawRepeatedWriterNovelTimes_eq_nil_of_switchSimple
      (N := N) hsimple
  unfold rawRepeatedWriterFresh at hcover
  rw [hempty] at hcover
  simpa using hcover

/-- The canonical first-writer history is monotone in its raw horizon. -/
theorem rawFirstWriterHistory_mono
    {w : Wiring} {N K L : Nat} {start : Nat × Tongues}
    (hKL : K ≤ L) :
    ∀ {v : List Bool},
      v ∈ rawFirstWriterHistory w N start K →
      v ∈ rawFirstWriterHistory w N start L := by
  classical
  intro v hv
  unfold rawFirstWriterHistory at hv ⊢
  rcases List.mem_cons.mp hv with hv | hv
  · exact List.mem_cons.mpr (Or.inl hv)
  · apply List.mem_cons.mpr
    apply Or.inr
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    apply List.mem_map.mpr
    refine ⟨k, ?_, rfl⟩
    have hkData := mem_rawFirstWriterTimes_iff.mp hk
    exact mem_rawFirstWriterTimes_iff.mpr
      ⟨Nat.lt_of_lt_of_le hkData.1 hKL, hkData.2⟩

/-- Horizon-independent form of the switch-simple construction-history
extraction.  A later ambient horizon retains every construction vector. -/
theorem PhysicalTrace.restrictedTonguesAt_mem_rawFirstWriterHistory_of_le
    {w : Wiring} {N K : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (horizon : passages.length ≤ K) :
    ∀ k, k ≤ passages.length →
      restrictedTonguesAt w N start k ∈
        rawFirstWriterHistory w N start K := by
  intro k hk
  exact rawFirstWriterHistory_mono horizon
    (htrace.restrictedTonguesAt_mem_rawFirstWriterHistory hsimple k hk)

/-- The full simple exploration used to manufacture any reflector is already
present in the ambient raw first-writer history.  This is the promised
construction-state extraction from the actual first-revisit control flow,
not a cardinality surrogate. -/
theorem ManufacturedReflector.exploration_mem_rawFirstWriterHistory
    {w : Wiring} {N K g e : Nat}
    (A : ManufacturedReflector w g e)
    (horizon : A.exploration.length ≤ K) :
    ∀ k, k ≤ A.exploration.length →
      restrictedTonguesAt w N (g, A.baseState) k ∈
        rawFirstWriterHistory w N (g, A.baseState) K := by
  exact A.exploration_trace
    |>.restrictedTonguesAt_mem_rawFirstWriterHistory_of_le
      A.exploration_simple horizon

/-- The complete out-and-back journey which manufactures a reflector uses
only the raw first-writer construction history plus its single activated
contact vector.  This replaces the old ad-hoc `N+2` construction list by the
canonical `N+1` raw history and one explicit exceptional state. -/
theorem ManufacturedReflector.manufacturing_journey_mem_rawHistory_one_extra
    {w : Wiring} {N K g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    (horizon : A.exploration.length ≤ K) :
    ∀ j, j ≤ A.exploration.length + A.runway.length + 1 →
      restrictedTonguesAt w N (g, A.baseState) j ∈
        rawFirstWriterHistory w N (g, A.baseState) K ++
          [VectorCount.restrict N A.activatedState] := by
  intro j hj
  have hm := A.manufacturing_journey_mem_sharpHistory
    (N := N) hpaths hj
  unfold ManufacturedReflector.sharpConstructionHistory at hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨k, hk, hvector⟩ := List.mem_map.mp hm
    have hkBound : k ≤ A.exploration.length := by
      have hkRange := List.mem_range.mp hk
      omega
    apply List.mem_append_left
    rw [← hvector]
    exact A.exploration_mem_rawFirstWriterHistory
      horizon k hkBound
  · exact List.mem_append_right _ hm

/-- In the complete first-reflector manufacturing journey, at most one raw
repeated-writer novelty occurs.  All simple-exploration states are charged to
first writers; the forced return has only the single activated vector.  This
is the exact pre-tail `≤ 1` fact needed by the sharp global count. -/
theorem ManufacturedReflector.manufacturing_repeatedWriterNovelty_le_one
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState) :
    (rawRepeatedWriterNovelTimes w N (g, A.baseState)
      (A.exploration.length + A.runway.length + 1)).length ≤ 1 := by
  let J := A.exploration.length + A.runway.length + 1
  let start : Nat × Tongues := (g, A.baseState)
  let history := rawFirstWriterHistory w N start J
  let postTimes := rawRepeatedWriterPostTimes w N start J
  have hexplorationLe : A.exploration.length ≤ J := by
    dsimp [J]
    omega
  have hcover : NoveltyCoverOn w N start postTimes history 1 := by
    refine ⟨[VectorCount.restrict N A.activatedState], by simp, ?_⟩
    intro t ht
    have htBound : t ≤ J := by
      dsimp [postTimes] at ht
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
      have hkData := mem_rawRepeatedWriterNovelTimes_iff.mp hk
      omega
    have hm := A.manufacturing_journey_mem_rawHistory_one_extra
      (N := N) (K := J) hpaths hexplorationLe t (by
        simpa [J] using htBound)
    simpa [start, history] using hm
  have hnew : ∀ t ∈ postTimes,
      restrictedTonguesAt w N start t ∉ history := by
    simpa [postTimes, history, start] using
      repeatedWriterPostTimes_avoid_firstHistory
        (w := w) (N := N) hN start J
  have hnd :
      (postTimes.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [postTimes]
    rw [map_repeatedWriterPostTimes_eq_fresh]
    exact rawRepeatedWriterFresh_nodup w N start J
  have hcount := noveltyCoverOn_fresh_distinct_count
    hcover hnew hnd
  simpa [postTimes, rawRepeatedWriterPostTimes, start, J] using hcount

/-! ## First-revisit extraction from an arbitrary finite physical prefix -/

/-- A nonsimple finite physical trace already contains the complete activated
first-revisit normal form; the `N+1` liveness wrapper used elsewhere is not
needed once the concrete trace is available.  This is the control-flow
bridge used by raw repeated-writer frame spans. -/
theorem PhysicalTrace.first_revisit_activated_outcome
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage} {entryEdge : Nat}
    (htrace : PhysicalTrace w start passages finish)
    (hnonsimple : ¬ SwitchSimple passages)
    (hentry : w.link entryEdge = some start.1) :
    ∃ atRepeat visited,
      stepN w visited start = some atRepeat ∧
      (SettlesOnSimpleCycle w atRepeat ∨
        ∃ (A : ManufacturedReflector w start.1 entryEdge)
            (state : Tongues) (backSteps : Nat),
          PathGrooves A.toSupported.paths state ∧
          A.baseState = start.2 ∧
          state = A.activatedState ∧
          stepN w backSteps atRepeat = some (entryEdge, state) ∧
          (∀ j, j ∉ A.exploration.map passageSwitch →
            state j = start.2 j)) := by
  obtain ⟨before, repeated, after, hsplit, hsimple, hrepeatMem⟩ :=
    first_revisit_split hnonsimple
  rw [hsplit] at htrace
  obtain ⟨atRepeat, hbeforeTrace, hafterTrace⟩ :=
    htrace.split_append
  obtain ⟨old, hold, hsameSwitch⟩ := List.mem_map.mp hrepeatMem
  obtain ⟨runway, path, hbeforeSplit⟩ := List.append_of_mem hold
  rw [hbeforeSplit] at hbeforeTrace
  obtain ⟨atOld, hrunway, hexcursion⟩ :=
    hbeforeTrace.split_append
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  have hatOldPort : atOld.1 = p := hexcursion.head_arrive.1
  rcases atOld with ⟨oldPort, u₀⟩
  simp only at hatOldPort
  subst oldPort
  have hatRepeatPort : atRepeat.1 = q := hafterTrace.head_arrive.1
  rcases atRepeat with ⟨repeatPort, u⟩
  simp only at hatRepeatPort
  subst repeatPort
  obtain ⟨v, hrepeat⟩ := hafterTrace.head_arrive.2
  have hsimpleBefore : SwitchSimple (runway ++ (p, x) :: path) := by
    simpa [hbeforeSplit] using hsimple
  have hswitch : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  have hout := first_revisit_cycle_or_activated_manufactured_reflector w
    hrunway hexcursion hsimpleBefore hswitch hrepeat hentry
  refine ⟨(q, u), before.length, ?_, ?_⟩
  · simpa [hbeforeSplit] using hbeforeTrace.sound
  · rcases hout with hcycle | hreflector
    · exact Or.inl hcycle
    · obtain ⟨A, state, hpaths, hbase, hactivated,
          hback, hpreserves⟩ := hreflector
      exact Or.inr ⟨A, state, runway.length + 1,
        hpaths, hbase, hactivated, hback, hpreserves⟩

/-- Every configuration actually reached from a known-edge start again has
a concrete incoming physical edge.  At time zero it is the supplied edge;
after a positive number of steps it is the preceding configuration's exit. -/
theorem exists_entryEdge_of_reach
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

/-- The serial branch of five raw repeated novelties now yields an actual
first-revisit control-flow outcome at the first frame: either a reached
simple cycle or a fully activated manufactured reflector with its concrete
incoming edge.  No runway-tail choice is assumed. -/
theorem five_serial_novelties_first_activated_outcome
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
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
    ∃ (before close : Nat × Tongues) (edge : Nat)
        (atRepeat : Nat × Tongues) (visited : Nat),
      stepN w a₀ start = some before ∧
      stepN w z₀ start = some close ∧
      w.link edge = some before.1 ∧
      stepN w visited before = some atRepeat ∧
      (SettlesOnSimpleCycle w atRepeat ∨
        ∃ (A : ManufacturedReflector w before.1 edge)
            (state : Tongues) (backSteps : Nat),
          PathGrooves A.toSupported.paths state ∧
          A.baseState = before.2 ∧
          state = A.activatedState ∧
          stepN w backSteps atRepeat = some (edge, state) ∧
          (∀ j, j ∉ A.exploration.map passageSwitch →
            state j = before.2 j)) := by
  obtain ⟨before, close, passages, runway, repeated, suffix,
      hbefore, hclose, _hlength, htrace, hsplit, hsimple,
      hrepeat⟩ :=
    five_serial_novelties_force_first_repeated_switch
      hN H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  have hnonsimple : ¬ SwitchSimple passages := by
    intro hallSimple
    unfold SwitchSimple at hallSimple
    rw [hsplit] at hallSimple
    simp only [List.map_append, List.map_cons] at hallSimple
    have hparts := List.nodup_append.mp hallSimple
    have hdisjoint := hparts.2.2 (passageSwitch repeated)
      hrepeat (passageSwitch repeated) (by simp)
    exact hdisjoint rfl
  obtain ⟨edge, hedge⟩ := exists_entryEdge_of_reach hentry hbefore
  obtain ⟨atRepeat, visited, hvisited, houtcome⟩ :=
    htrace.first_revisit_activated_outcome hnonsimple hedge
  exact ⟨before, close, edge, atRepeat, visited,
    hbefore, hclose, hedge, hvisited, houtcome⟩

/-- A later globally novel post-vector differs from every earlier vector. -/
theorem RawNovelAt.post_ne_earlier
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {k earlier : Nat}
    (h : RawNovelAt w N start k) (hearlier : earlier < k + 1) :
    restrictedTonguesAt w N start (k + 1) ≠
      restrictedTonguesAt w N start earlier := by
  intro heq
  apply h
  apply List.mem_map.mpr
  exact ⟨earlier, List.mem_range.mpr hearlier, heq.symm⟩

/-- Four chronologically ordered novel events have four pairwise-distinct
post-vectors. -/
theorem four_raw_novel_post_vectors_nodup
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z₁ z₂ z₃ z₄ : Nat}
    (h₁₂ : z₁ < z₂) (h₂₃ : z₂ < z₃) (h₃₄ : z₃ < z₄)
    (H₁ : RawNovelAt w N start z₁)
    (H₂ : RawNovelAt w N start z₂)
    (H₃ : RawNovelAt w N start z₃)
    (H₄ : RawNovelAt w N start z₄) :
    [restrictedTonguesAt w N start (z₁ + 1),
     restrictedTonguesAt w N start (z₂ + 1),
     restrictedTonguesAt w N start (z₃ + 1),
     restrictedTonguesAt w N start (z₄ + 1)].Nodup := by
  have h₁₃ : z₁ < z₃ := Nat.lt_trans h₁₂ h₂₃
  have h₁₄ : z₁ < z₄ := Nat.lt_trans h₁₃ h₃₄
  have h₂₄ : z₂ < z₄ := Nat.lt_trans h₂₃ h₃₄
  have hne₁₂ : restrictedTonguesAt w N start (z₁ + 1) ≠
      restrictedTonguesAt w N start (z₂ + 1) :=
    (H₂.post_ne_earlier (by omega)).symm
  have hne₁₃ : restrictedTonguesAt w N start (z₁ + 1) ≠
      restrictedTonguesAt w N start (z₃ + 1) :=
    (H₃.post_ne_earlier (by omega)).symm
  have hne₁₄ : restrictedTonguesAt w N start (z₁ + 1) ≠
      restrictedTonguesAt w N start (z₄ + 1) :=
    (H₄.post_ne_earlier (by omega)).symm
  have hne₂₃ : restrictedTonguesAt w N start (z₂ + 1) ≠
      restrictedTonguesAt w N start (z₃ + 1) :=
    (H₃.post_ne_earlier (by omega)).symm
  have hne₂₄ : restrictedTonguesAt w N start (z₂ + 1) ≠
      restrictedTonguesAt w N start (z₄ + 1) :=
    (H₄.post_ne_earlier (by omega)).symm
  have hne₃₄ : restrictedTonguesAt w N start (z₃ + 1) ≠
      restrictedTonguesAt w N start (z₄ + 1) :=
    (H₄.post_ne_earlier (by omega)).symm
  simp [List.nodup_cons, hne₁₂, hne₁₃, hne₁₄,
    hne₂₃, hne₂₄, hne₃₄]

/-! ## Direct global-control-flow bridge

The five-frame extraction below is useful geometric normal form, but the
sharp count does not actually require every five-frame family to manufacture
one particular tail.  It is enough that the global first-revisit/repair
control flow reaches a changed-forward tail after at most one repeated-writer
novelty, with its construction lead already represented by the canonical
first-writer history.  The next theorem proves that exact implication.
-/

/-- **Compiled early-tail closure.**

Fix an arbitrary finite raw horizon.  Suppose the actual global repair run
reaches a changed-forward manufactured tail at absolute time `shift`.

* at most one repeated-writer novelty post-time lies before `shift`; and
* every state of the manufactured construction lead is already in
  `rawFirstWriterHistory`.

Then the whole horizon contains at most four repeated-writer novelties.  The
single pre-tail event plus the historical-entry runway theorem's three fresh
tail vectors give the exact constant four.  This theorem performs the full
absolute/local time transport and uses the raw novelty facts to count the
original event list; its hypotheses are only the remaining global
first-revisit/control-flow extraction. -/
theorem rawRepeatedWriterNovelTimes_le_four_of_early_changedForward
    {w : Wiring} {N K g e shift : Nat}
    {start : Nat × Tongues}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hmerge : A.ChangedForwardMerge (.flip R))
    (hreach : stepN w shift start =
      some (g, (ManufacturedReflector.flip R).activatedState))
    (hbefore :
      ((rawRepeatedWriterPostTimes w N start K).filter
        (fun t => decide (t < shift))).length ≤ 1)
    (hleadHistorical : ∀ j, j ≤ A.toSupported.travel →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈
          rawFirstWriterHistory w N start K) :
    (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 := by
  let postTimes := rawRepeatedWriterPostTimes w N start K
  let history := rawFirstWriterHistory w N start K
  let before := postTimes.filter (fun t => decide (t < shift))
  let localTimes := postTimes.map (fun t => t - shift)
  obtain ⟨tailFresh, htailLength, htailMem⟩ :=
    hmerge.runway_or_candy_absolute_three_novelty
      N history (by simpa [history] using hleadHistorical) localTimes
  let fresh :=
    before.map (restrictedTonguesAt w N start) ++ tailFresh
  have hfreshLength : fresh.length ≤ 4 := by
    have hbefore' : before.length ≤ 1 := by
      simpa [before, postTimes] using hbefore
    dsimp [fresh]
    simp only [List.length_append, List.length_map]
    omega
  have hcover : NoveltyCoverOn w N start postTimes history 4 := by
    refine ⟨fresh, hfreshLength, ?_⟩
    intro t ht
    by_cases htshift : t < shift
    · apply List.mem_append_right history
      apply List.mem_append_left tailFresh
      apply List.mem_map.mpr
      exact ⟨t, List.mem_filter.mpr
        ⟨ht, decide_eq_true htshift⟩, rfl⟩
    · have hshiftLe : shift ≤ t := by omega
      let d := t - shift
      have hd : d ∈ localTimes := by
        apply List.mem_map.mpr
        exact ⟨t, ht, rfl⟩
      have htLive : (stepN w t start).isSome := by
        dsimp [postTimes] at ht
        obtain ⟨k, hk, hkt⟩ := List.mem_map.mp ht
        subst t
        exact (mem_rawRepeatedWriterNovelTimes_iff.mp hk).2.1.1
      have hvector := restrictedTonguesAt_sub_of_reach
        (N := N) hreach hshiftLe htLive
      have hm := htailMem d hd
      dsimp [d] at hm
      rw [← hvector] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left fresh hm
      · apply List.mem_append_right history
        exact List.mem_append_right
          (before.map (restrictedTonguesAt w N start)) hm
  have hnew : ∀ t ∈ postTimes,
      restrictedTonguesAt w N start t ∉ history := by
    simpa [postTimes, history] using
      repeatedWriterPostTimes_avoid_firstHistory
        (w := w) (N := N) hN start K
  have hnd :
      (postTimes.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [postTimes]
    rw [map_repeatedWriterPostTimes_eq_fresh]
    exact rawRepeatedWriterFresh_nodup w N start K
  have hcount := noveltyCoverOn_fresh_distinct_count
    hcover hnew hnd
  simpa [postTimes, rawRepeatedWriterPostTimes] using hcount

/-- **One-extra-state early-tail closure.**

The actual first-revisit construction naturally has one repeated contact
state in addition to `rawFirstWriterHistory`.  Requiring the entire repair
lead to lie in the smaller history is therefore stronger than the sharp
count needs.  It is enough to supply one extra vector which covers both the
pre-tail raw events and the manufactured lead.  The changed-forward theorem
then contributes only three further vectors, so the repeated-writer novelty
budget is still exactly four.

This is the direct interface for the global first-revisit/repair extraction:
it asks for pointwise history coverage, not a five-frame normal form. -/
theorem rawRepeatedWriterNovelTimes_le_four_of_early_changedForward_one_extra
    {w : Wiring} {N K g e shift : Nat}
    {start : Nat × Tongues}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hmerge : A.ChangedForwardMerge (.flip R))
    (hreach : stepN w shift start =
      some (g, (ManufacturedReflector.flip R).activatedState))
    (extra : List (List Bool))
    (hextra : extra.length ≤ 1)
    (hbeforeCovered : ∀ t,
      t ∈ rawRepeatedWriterPostTimes w N start K → t < shift →
      restrictedTonguesAt w N start t ∈
        rawFirstWriterHistory w N start K ++ extra)
    (hleadCovered : ∀ j, j ≤ A.toSupported.travel →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈
          rawFirstWriterHistory w N start K ++ extra) :
    (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 := by
  let postTimes := rawRepeatedWriterPostTimes w N start K
  let history := rawFirstWriterHistory w N start K
  let extendedHistory := history ++ extra
  let localTimes := postTimes.map (fun t => t - shift)
  obtain ⟨tailFresh, htailLength, htailMem⟩ :=
    hmerge.runway_or_candy_absolute_three_novelty
      N extendedHistory (by
        simpa [extendedHistory, history] using hleadCovered) localTimes
  let fresh := extra ++ tailFresh
  have hfreshLength : fresh.length ≤ 4 := by
    dsimp [fresh]
    simp only [List.length_append]
    omega
  have hcover : NoveltyCoverOn w N start postTimes history 4 := by
    refine ⟨fresh, hfreshLength, ?_⟩
    intro t ht
    by_cases htshift : t < shift
    · have hm := hbeforeCovered t (by simpa [postTimes] using ht) htshift
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left fresh hm
      · exact List.mem_append_right history
          (List.mem_append_left tailFresh hm)
    · have hshiftLe : shift ≤ t := by omega
      let d := t - shift
      have hd : d ∈ localTimes := by
        apply List.mem_map.mpr
        exact ⟨t, ht, rfl⟩
      have htLive : (stepN w t start).isSome := by
        dsimp [postTimes] at ht
        obtain ⟨k, hk, hkt⟩ := List.mem_map.mp ht
        subst t
        exact (mem_rawRepeatedWriterNovelTimes_iff.mp hk).2.1.1
      have hvector := restrictedTonguesAt_sub_of_reach
        (N := N) hreach hshiftLe htLive
      have hm := htailMem d hd
      dsimp [d] at hm
      rw [← hvector] at hm
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left fresh hm
        · exact List.mem_append_right history
            (List.mem_append_left tailFresh hm)
      · exact List.mem_append_right history
          (List.mem_append_right extra hm)
  have hnew : ∀ t ∈ postTimes,
      restrictedTonguesAt w N start t ∉ history := by
    simpa [postTimes, history] using
      repeatedWriterPostTimes_avoid_firstHistory
        (w := w) (N := N) hN start K
  have hnd :
      (postTimes.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [postTimes]
    rw [map_repeatedWriterPostTimes_eq_fresh]
    exact rawRepeatedWriterFresh_nodup w N start K
  have hcount := noveltyCoverOn_fresh_distinct_count
    hcover hnew hnd
  simpa [postTimes, rawRepeatedWriterPostTimes] using hcount

/-! ## Exact direct-control-flow residual

The global theorem need not force one tail from every arbitrary five-frame
selection.  It suffices to follow the actual first-revisit/repair run and
return either the desired bound immediately or the one-extra changed-forward
certificate consumed above. -/

/-- Concrete witness returned by the non-small branch of the direct global
control-flow dichotomy.  Every field is pointwise raw-run data; there is no
cardinality conclusion or hidden frame-extraction premise in the structure. -/
structure EarlyChangedForwardHistoryCertificate
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) where
  g : Nat
  e : Nat
  A : ManufacturedReflector w g e
  R : ManufacturedFlipReflector w e g
  shift : Nat
  merge : A.ChangedForwardMerge (.flip R)
  reached : stepN w shift start =
    some (g, (ManufacturedReflector.flip R).activatedState)
  extra : List (List Bool)
  extra_length : extra.length ≤ 1
  before_covered : ∀ t,
    t ∈ rawRepeatedWriterPostTimes w N start K → t < shift →
    restrictedTonguesAt w N start t ∈
      rawFirstWriterHistory w N start K ++ extra
  lead_covered : ∀ j, j ≤ A.toSupported.travel →
    restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).activatedState) j ∈
        rawFirstWriterHistory w N start K ++ extra

/-- A direct early-tail certificate gives the sharp four-event bound. -/
theorem EarlyChangedForwardHistoryCertificate.repeatedWriterNovelty_le_four
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (C : EarlyChangedForwardHistoryCertificate w N start K) :
    (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 := by
  exact rawRepeatedWriterNovelTimes_le_four_of_early_changedForward_one_extra
    hN C.merge C.reached C.extra C.extra_length
      C.before_covered C.lead_covered

/-- **Exact weaker exhaustive dichotomy for the open global control flow.**

For the actual known-edge raw run and horizon, either the sharp event bound
already holds, or first-revisit/repair exposes one concrete early
changed-forward history certificate.  This is strictly weaker than
`KnownEdgeFiveFrameRunwayExtraction`: it does not select five events, impose
a common geometric normal form, or demand that every frame family produce a
tail. -/
def KnownEdgeEarlyChangedForwardDichotomy : Prop :=
  ∀ (w : Wiring) (N e : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues) (K : Nat),
      w.link e = some start.1 →
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 ∨
        Nonempty (EarlyChangedForwardHistoryCertificate w N start K)

/-- Closing the direct exhaustive dichotomy closes the public known-edge
four-repeated-writer theorem, with no five-frame extraction. -/
theorem knownEdgeFourRepeatedWriterNovelty_of_earlyChangedForwardDichotomy
    (hcontrol : KnownEdgeEarlyChangedForwardDichotomy) :
    KnownEdgeFourRepeatedWriterNovelty := by
  intro w N e hN start K hentry
  rcases hcontrol w N e hN start K hentry with hsmall | hcertificate
  · exact hsmall
  · obtain ⟨C⟩ := hcertificate
    exact C.repeatedWriterNovelty_le_four hN

/-- Consequently, the direct first-revisit/repair dichotomy suffices for the
raw-track state law. -/
theorem stateLaw_of_earlyChangedForwardDichotomy
    (hcontrol : KnownEdgeEarlyChangedForwardDichotomy) : StateLaw :=
  stateLaw_of_knownEdgeFourRepeatedWriterNovelty
    (knownEdgeFourRepeatedWriterNovelty_of_earlyChangedForwardDichotomy
      hcontrol)

/-! ## The changed-forward theorem needs only its actual short lead -/

/-- A changed-forward merge exposes a concrete pre-splice `leadSteps`, no
longer than the old reflector's macro travel.  Historical coverage is needed
only through that actual lead, not through every nominal step of
`A.toSupported.travel`.  Once this shorter prefix is historical, the entire
future has the same absolute three-vector novelty cover. -/
theorem ManufacturedReflector.ChangedForwardMerge.exists_short_lead_three_novelty
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R)) :
    ∃ leadSteps, leadSteps ≤ A.toSupported.travel ∧
      ∀ (N : Nat) (history : List (List Bool)),
        (∀ j, j ≤ leadSteps →
          restrictedTonguesAt w N
            (g, (ManufacturedReflector.flip R).activatedState) j ∈
              history) →
        ∀ times : List Nat,
          NoveltyCoverOn w N
            (g, (ManufacturedReflector.flip R).activatedState)
            times history 3 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      approach, candy, state, leadSteps, _tailSteps, horiented,
      hrouteSplit, hOldTail, hApproach, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach,
      _hcomplete, hleadLen, _htailLen, happroachLe⟩ :=
    hmerge.spliced_lobe_reflector
  have hleadLe : leadSteps ≤ A.toSupported.travel := by
    rw [hleadLen]
    exact happroachLe
  refine ⟨leadSteps, hleadLe, ?_⟩
  intro N history hleadHistorical times
  have hentryHistorical : VectorCount.restrict N
      (flipAt state (mouth / 3)) ∈ history := by
    have hvector : restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState)
        leadSteps =
        VectorCount.restrict N (flipAt state (mouth / 3)) := by
      simp [restrictedTonguesAt, tonguesAt, hreach]
    rw [← hvector]
    exact hleadHistorical leadSteps (Nat.le_refl _)
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨C, _hCAction, hEntryOldNe, hCpaths,
        hNewAvoidsCRaw, _htravel⟩ :=
      R.suffix_after_runway_passage_with_travel state hRpaths
        hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove : arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch state entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe : mouth / 3 ≠ C.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsC : (LocalAction.flip (mouth / 3)).Avoids
        C.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsCRaw
    by_cases hcontact : ∃ passage ∈ candy,
        passageSwitch passage = C.actionSwitch
    · apply manufactured_flip_arbitrary_lobe_absolute_three_novelty
        C state hCpaths hNewAvoidsC hentryBranch hentrySwitch
        hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
        hmouthLink hcontact hreach times history hentryHistorical
      intro j _hj hjLead
      exact hleadHistorical j (Nat.le_of_lt hjLead)
    · have hCandyForeignOld : ∀ passage ∈ candy,
          passageSwitch passage ≠ C.actionSwitch := by
        intro passage hp hEq
        exact hcontact ⟨passage, hp, hEq⟩
      apply manufactured_suffix_explicit_lobe_absolute_three_novelty
        C state hCpaths hNewAvoidsC hActionsNe hentryBranch
        hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hCandyForeignOld hLobe hmouthLink hreach
        times history hentryHistorical
      intro j _hj hjLead
      exact hleadHistorical j (Nat.le_of_lt hjLead)
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        horiented hrunway hentryBranch
    have hentryGrooved : arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved hApproach hApproachGrooved
      hApproachForeign hcrossed hmouthLink harms hreach
      N history hentryHistorical times (by
        intro j _hj hjLead
        exact hleadHistorical j (Nat.le_of_lt hjLead))
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩

/-- Reusable package for the actual short lead selected by a changed-forward
merge. -/
structure ChangedForwardShortLead
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (R : ManufacturedFlipReflector w e g) where
  leadSteps : Nat
  lead_le : leadSteps ≤ A.toSupported.travel
  three_novelty : ∀ (N : Nat) (history : List (List Bool)),
    (∀ j, j ≤ leadSteps →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈ history) →
    ∀ times : List Nat,
      NoveltyCoverOn w N
        (g, (ManufacturedReflector.flip R).activatedState)
        times history 3

/-- Every changed-forward merge has a short-lead package. -/
theorem ManufacturedReflector.ChangedForwardMerge.has_shortLead
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hmerge : A.ChangedForwardMerge (.flip R)) :
    Nonempty (ChangedForwardShortLead A R) := by
  obtain ⟨leadSteps, hlead, hthree⟩ :=
    hmerge.exists_short_lead_three_novelty
  exact ⟨{
    leadSteps := leadSteps
    lead_le := hlead
    three_novelty := hthree
  }⟩

/-- Generic absolute counting step: one exceptional pre-tail vector followed
by a reached local three-vector novelty cover gives at most four raw repeated
novelties. -/
theorem rawRepeatedWriterNovelTimes_le_four_of_reached_three_cover
    {w : Wiring} {N K g shift : Nat}
    {start : Nat × Tongues} {localState : Tongues}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (hreach : stepN w shift start = some (g, localState))
    (extra : List (List Bool))
    (hextra : extra.length ≤ 1)
    (hbeforeCovered : ∀ t,
      t ∈ rawRepeatedWriterPostTimes w N start K → t < shift →
      restrictedTonguesAt w N start t ∈
        rawFirstWriterHistory w N start K ++ extra)
    (htail : NoveltyCoverOn w N (g, localState)
      ((rawRepeatedWriterPostTimes w N start K).map
        (fun t => t - shift))
      (rawFirstWriterHistory w N start K ++ extra) 3) :
    (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 := by
  let postTimes := rawRepeatedWriterPostTimes w N start K
  let history := rawFirstWriterHistory w N start K
  obtain ⟨tailFresh, htailLength, htailMem⟩ := htail
  let fresh := extra ++ tailFresh
  have hfreshLength : fresh.length ≤ 4 := by
    dsimp [fresh]
    simp only [List.length_append]
    omega
  have hcover : NoveltyCoverOn w N start postTimes history 4 := by
    refine ⟨fresh, hfreshLength, ?_⟩
    intro t ht
    by_cases htshift : t < shift
    · have hm := hbeforeCovered t (by simpa [postTimes] using ht) htshift
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left fresh hm
      · exact List.mem_append_right history
          (List.mem_append_left tailFresh hm)
    · have hshiftLe : shift ≤ t := by omega
      let d := t - shift
      have hd : d ∈ (rawRepeatedWriterPostTimes w N start K).map
          (fun s => s - shift) := by
        apply List.mem_map.mpr
        exact ⟨t, by simpa [postTimes] using ht, rfl⟩
      have htLive : (stepN w t start).isSome := by
        dsimp [postTimes] at ht
        obtain ⟨k, hk, hkt⟩ := List.mem_map.mp ht
        subst t
        exact (mem_rawRepeatedWriterNovelTimes_iff.mp hk).2.1.1
      have hvector := restrictedTonguesAt_sub_of_reach
        (N := N) hreach hshiftLe htLive
      have hm := htailMem d hd
      dsimp [d] at hm
      rw [← hvector] at hm
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left fresh hm
        · exact List.mem_append_right history
            (List.mem_append_left tailFresh hm)
      · exact List.mem_append_right history
          (List.mem_append_right extra hm)
  have hnew : ∀ t ∈ postTimes,
      restrictedTonguesAt w N start t ∉ history := by
    simpa [postTimes, history] using
      repeatedWriterPostTimes_avoid_firstHistory
        (w := w) (N := N) hN start K
  have hnd :
      (postTimes.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [postTimes]
    rw [map_repeatedWriterPostTimes_eq_fresh]
    exact rawRepeatedWriterFresh_nodup w N start K
  have hcount := noveltyCoverOn_fresh_distinct_count
    hcover hnew hnd
  simpa [postTimes, rawRepeatedWriterPostTimes] using hcount

/-- **Shortest current direct-control-flow bridge.**  The global extraction
need cover only the merge's actual short lead by the canonical history plus
one exceptional vector.  No nominal `A.travel` coverage is required. -/
theorem rawRepeatedWriterNovelTimes_le_four_of_short_changedForward
    {w : Wiring} {N K g e shift : Nat}
    {start : Nat × Tongues}
    {A : ManufacturedReflector w g e}
    {R : ManufacturedFlipReflector w e g}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (_hmerge : A.ChangedForwardMerge (.flip R))
    (hreach : stepN w shift start =
      some (g, (ManufacturedReflector.flip R).activatedState))
    (S : ChangedForwardShortLead A R)
    (extra : List (List Bool))
    (hextra : extra.length ≤ 1)
    (hbeforeCovered : ∀ t,
      t ∈ rawRepeatedWriterPostTimes w N start K → t < shift →
      restrictedTonguesAt w N start t ∈
        rawFirstWriterHistory w N start K ++ extra)
    (hleadCovered : ∀ j, j ≤ S.leadSteps →
      restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).activatedState) j ∈
          rawFirstWriterHistory w N start K ++ extra) :
    (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 := by
  apply rawRepeatedWriterNovelTimes_le_four_of_reached_three_cover
    hN hreach extra hextra hbeforeCovered
  exact S.three_novelty N
    (rawFirstWriterHistory w N start K ++ extra)
    hleadCovered
    ((rawRepeatedWriterPostTimes w N start K).map
      (fun t => t - shift))

/-- Strongest direct certificate currently required from global control
flow.  Compared with `EarlyChangedForwardHistoryCertificate`, its history
obligation stops at the physically extracted short lead. -/
structure ShortEarlyChangedForwardHistoryCertificate
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) where
  g : Nat
  e : Nat
  A : ManufacturedReflector w g e
  R : ManufacturedFlipReflector w e g
  shift : Nat
  merge : A.ChangedForwardMerge (.flip R)
  reached : stepN w shift start =
    some (g, (ManufacturedReflector.flip R).activatedState)
  shortLead : ChangedForwardShortLead A R
  extra : List (List Bool)
  extra_length : extra.length ≤ 1
  before_covered : ∀ t,
    t ∈ rawRepeatedWriterPostTimes w N start K → t < shift →
    restrictedTonguesAt w N start t ∈
      rawFirstWriterHistory w N start K ++ extra
  lead_covered : ∀ j, j ≤ shortLead.leadSteps →
    restrictedTonguesAt w N
      (g, (ManufacturedReflector.flip R).activatedState) j ∈
        rawFirstWriterHistory w N start K ++ extra

/-- The short direct certificate proves the four-event bound. -/
theorem ShortEarlyChangedForwardHistoryCertificate.repeatedWriterNovelty_le_four
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (C : ShortEarlyChangedForwardHistoryCertificate w N start K) :
    (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 := by
  exact rawRepeatedWriterNovelTimes_le_four_of_short_changedForward
    hN C.merge C.reached C.shortLead C.extra C.extra_length
      C.before_covered C.lead_covered

/-- Weakest current exhaustive raw-run residual: already small, or one short
changed-forward history certificate. -/
def KnownEdgeShortEarlyChangedForwardDichotomy : Prop :=
  ∀ (w : Wiring) (N e : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues) (K : Nat),
      w.link e = some start.1 →
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 4 ∨
        Nonempty
          (ShortEarlyChangedForwardHistoryCertificate w N start K)

/-- The short exhaustive control-flow dichotomy closes the public known-edge
four-event theorem. -/
theorem knownEdgeFourRepeatedWriterNovelty_of_shortEarlyDichotomy
    (hcontrol : KnownEdgeShortEarlyChangedForwardDichotomy) :
    KnownEdgeFourRepeatedWriterNovelty := by
  intro w N e hN start K hentry
  rcases hcontrol w N e hN start K hentry with hsmall | hcertificate
  · exact hsmall
  · obtain ⟨C⟩ := hcertificate
    exact C.repeatedWriterNovelty_le_four hN

/-- And therefore the same short exhaustive dichotomy closes `StateLaw`. -/
theorem stateLaw_of_shortEarlyChangedForwardDichotomy
    (hcontrol : KnownEdgeShortEarlyChangedForwardDichotomy) : StateLaw :=
  stateLaw_of_knownEdgeFourRepeatedWriterNovelty
    (knownEdgeFourRepeatedWriterNovelty_of_shortEarlyDichotomy hcontrol)

/-- The complete fixed-track content extracted from one raw repeated-writer
novelty.  Both the parity rerouter and the closing writer leave by immutable
stem links. -/
structure RawFixedStemOpenFrame
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (right : Nat) where
  left : Nat
  reroute : Nat
  outer : RawLastWriterFrame w N start left right
  reroute_productive : RawProductiveAt w N start reroute
  different_writer :
    rawWriterAt w start reroute ≠ rawWriterAt w start right
  no_same_rerouter_before : ∀ j, left < j → j < reroute →
    RawProductiveAt w N start j →
    rawWriterAt w start j ≠ rawWriterAt w start reroute
  shape : RawOpenReroutingShape w N start left reroute right
  reroute_stem_successor : ∃ next,
    stepN w (reroute + 1) start = some next ∧
    w.link (3 * rawWriterAt w start reroute) = some next.1
  close_stem_successor : ∃ next,
    stepN w (right + 1) start = some next ∧
    w.link (3 * rawWriterAt w start right) = some next.1

/-- Raw repeated-writer decomposition, repackaged without losing any of its
fixed-stem routing facts. -/
theorem RawRepeatedWriterNovelAt.fixedStemOpenFrame
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right) :
    Nonempty (RawFixedStemOpenFrame w N start right) := by
  obtain ⟨left, reroute, outer, hprod, hdiff, hfirst, hshape,
      hreroute, hclose⟩ := h.open_frame_with_fixed_stem_successors hN
  exact ⟨{
    left := left
    reroute := reroute
    outer := outer
    reroute_productive := hprod
    different_writer := hdiff
    no_same_rerouter_before := hfirst
    shape := hshape
    reroute_stem_successor := hreroute
    close_stem_successor := hclose
  }⟩

/-- Five chronological raw novelties together with all five proved fixed-stem
open frames.  This is the global object consumed by the remaining physical
history extraction. -/
structure FiveFixedStemNovelFrames
    (w : Wiring) (N : Nat) (start : Nat × Tongues) where
  z₀ : Nat
  z₁ : Nat
  z₂ : Nat
  z₃ : Nat
  z₄ : Nat
  order₀₁ : z₀ < z₁
  order₁₂ : z₁ < z₂
  order₂₃ : z₂ < z₃
  order₃₄ : z₃ < z₄
  event₀ : RawRepeatedWriterNovelAt w N start z₀
  event₁ : RawRepeatedWriterNovelAt w N start z₁
  event₂ : RawRepeatedWriterNovelAt w N start z₂
  event₃ : RawRepeatedWriterNovelAt w N start z₃
  event₄ : RawRepeatedWriterNovelAt w N start z₄
  frame₀ : RawFixedStemOpenFrame w N start z₀
  frame₁ : RawFixedStemOpenFrame w N start z₁
  frame₂ : RawFixedStemOpenFrame w N start z₂
  frame₃ : RawFixedStemOpenFrame w N start z₃
  frame₄ : RawFixedStemOpenFrame w N start z₄

/-- The exact manufactured-tail witness needed to rule out four novelties
after the first one.  The complete construction lead ends no later than the
second closing frame, so every lead vector is in that event's strict prefix
history. -/
structure RunwayTailBeforeSecond
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (second : Nat) where
  g : Nat
  e : Nat
  A : ManufacturedReflector w g e
  R : ManufacturedFlipReflector w e g
  shift : Nat
  merge : A.ChangedForwardMerge (.flip R)
  reached : stepN w shift start =
    some (g, (ManufacturedReflector.flip R).activatedState)
  live : ∀ d, ∃ finish,
    stepN w d (g, (ManufacturedReflector.flip R).activatedState) =
      some finish
  lead_before_second : shift + A.toSupported.travel ≤ second

/-- **Exact remaining global geometry statement.**

Starting beyond a known physical edge, any five explicit fixed-stem novelty
frames force the changed-forward manufactured tail before the second frame
closes.  Unlike `KnownEdgeFourRepeatedWriterNovelty`, this proposition has no
list length or state-count conclusion: it asks only for the concrete physical
object which the global repair construction must extract from the raw frames.
-/
def KnownEdgeFiveFrameRunwayExtraction : Prop :=
  ∀ (w : Wiring) (N e : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues),
      w.link e = some start.1 →
      ∀ F : FiveFixedStemNovelFrames w N start,
        Nonempty (RunwayTailBeforeSecond w N start F.z₁)

/-! ## Reduction of the global extraction to two physical cases -/

/-- The five raw closing frames returned by the Erdős--Szekeres reduction,
without yet choosing its serial or triple branch. -/
structure FiveRawClosingFrames
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (z₀ z₁ z₂ z₃ z₄ : Nat) where
  a₀ : Nat
  q₀ : Nat
  a₁ : Nat
  q₁ : Nat
  a₂ : Nat
  q₂ : Nat
  a₃ : Nat
  q₃ : Nat
  a₄ : Nat
  q₄ : Nat
  frame₀ : RawNovelClosingFrame w N start a₀ q₀ z₀
  frame₁ : RawNovelClosingFrame w N start a₁ q₁ z₁
  frame₂ : RawNovelClosingFrame w N start a₂ q₂ z₂
  frame₃ : RawNovelClosingFrame w N start a₃ q₃ z₃
  frame₄ : RawNovelClosingFrame w N start a₄ q₄ z₄

/-- The later construction starts only after the first frame has closed. -/
structure FiveFrameSerialCase
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (z₀ z₁ z₂ z₃ z₄ : Nat) where
  frames : FiveRawClosingFrames w N start z₀ z₁ z₂ z₃ z₄
  serial : FiveFrameSerialBreak z₀
    frames.a₁ frames.a₂ frames.a₃ frames.a₄

/-- The five common-overlap openings contain an exact `ABCABC` or strict
three-frame nest. -/
structure FiveFrameTripleCase
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (z₀ z₁ z₂ z₃ z₄ : Nat) where
  frames : FiveRawClosingFrames w N start z₀ z₁ z₂ z₃ z₄
  triple : FiveFrameTripleOutcome
    frames.a₀ z₀ frames.a₁ z₁ frames.a₂ z₂
    frames.a₃ z₃ frames.a₄ z₄

/-- The conflict-resolved raw/curve obstruction reduces every ordered five
novelties to the serial case or the triple-interlacement case. -/
theorem FiveFixedStemNovelFrames.serial_or_triple
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (F : FiveFixedStemNovelFrames w N start) :
    Nonempty (FiveFrameSerialCase w N start
      F.z₀ F.z₁ F.z₂ F.z₃ F.z₄) ∨
    Nonempty (FiveFrameTripleCase w N start
      F.z₀ F.z₁ F.z₂ F.z₃ F.z₄) := by
  obtain ⟨a₀, q₀, a₁, q₁, a₂, q₂, a₃, q₃, a₄, q₄,
      G₀, G₁, G₂, G₃, G₄, hout⟩ :=
    five_repeated_novelties_serial_or_triple hN
      F.order₀₁ F.order₁₂ F.order₂₃ F.order₃₄
      F.event₀ F.event₁ F.event₂ F.event₃ F.event₄
  let G : FiveRawClosingFrames w N start
      F.z₀ F.z₁ F.z₂ F.z₃ F.z₄ := {
    a₀ := a₀
    q₀ := q₀
    a₁ := a₁
    q₁ := q₁
    a₂ := a₂
    q₂ := q₂
    a₃ := a₃
    q₃ := q₃
    a₄ := a₄
    q₄ := q₄
    frame₀ := G₀
    frame₁ := G₁
    frame₂ := G₂
    frame₃ := G₃
    frame₄ := G₄
  }
  rcases hout with hserial | htriple
  · exact Or.inl ⟨G, hserial⟩
  · exact Or.inr ⟨G, htriple⟩

/-- Exact serial residual: a serially separated five-frame configuration
must expose the manufactured changed-forward tail before the second close. -/
def KnownEdgeSerialFrameRunwayExtraction : Prop :=
  ∀ (w : Wiring) (N e : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues),
      w.link e = some start.1 →
      ∀ F : FiveFixedStemNovelFrames w N start,
        FiveFrameSerialCase w N start
          F.z₀ F.z₁ F.z₂ F.z₃ F.z₄ →
        Nonempty (RunwayTailBeforeSecond w N start F.z₁)

/-- Exact common-overlap residual: the physical curve/interlacement theorem
must rule out the `ABCABC`/strict-nest case.  This has no counting conclusion
and no manufactured-certificate choice. -/
def KnownEdgeTripleFrameObstruction : Prop :=
  ∀ (w : Wiring) (N e : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (start : Nat × Tongues),
      w.link e = some start.1 →
      ∀ F : FiveFixedStemNovelFrames w N start,
        FiveFrameTripleCase w N start
          F.z₀ F.z₁ F.z₂ F.z₃ F.z₄ → False

/-- The serial-tail theorem and the triple obstruction together discharge
the single five-frame extraction law. -/
theorem fiveFrameRunwayExtraction_of_serial_and_triple
    (hserial : KnownEdgeSerialFrameRunwayExtraction)
    (htriple : KnownEdgeTripleFrameObstruction) :
    KnownEdgeFiveFrameRunwayExtraction := by
  intro w N e hN start hentry F
  rcases F.serial_or_triple hN with hcase | hcase
  · obtain ⟨S⟩ := hcase
    exact hserial w N e hN start hentry F S
  · obtain ⟨T⟩ := hcase
    exact (htriple w N e hN start hentry F T).elim

/-- Once the physical tail has been extracted, the four later globally novel
post-vectors contradict the runway theorem's absolute three-vector cover. -/
theorem no_five_fixed_stem_novelties_of_runway_tail
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (F : FiveFixedStemNovelFrames w N start)
    (T : RunwayTailBeforeSecond w N start F.z₁) : False := by
  let localStart : Nat × Tongues :=
    (T.g, (ManufacturedReflector.flip T.R).activatedState)
  let history := rawPrefixHistory w N start (F.z₁ + 1)
  let localTimes :=
    [F.z₁ + 1 - T.shift,
     F.z₂ + 1 - T.shift,
     F.z₃ + 1 - T.shift,
     F.z₄ + 1 - T.shift]
  have hleadHistorical : ∀ j, j ≤ T.A.toSupported.travel →
      restrictedTonguesAt w N localStart j ∈ history := by
    intro j hj
    have htime : T.shift + j < F.z₁ + 1 := by
      have hlead := T.lead_before_second
      omega
    obtain ⟨finish, hfinish⟩ := T.live j
    have hshift := restrictedTonguesAt_add_of_reach
      (N := N) (d := j) T.reached hfinish
    dsimp [localStart]
    rw [← hshift]
    unfold history rawPrefixHistory
    apply List.mem_map.mpr
    exact ⟨T.shift + j, List.mem_range.mpr htime, rfl⟩
  have hcover : NoveltyCoverOn w N localStart localTimes history 3 :=
    T.merge.runway_or_candy_absolute_three_novelty
      N history hleadHistorical localTimes
  have hshiftLe : T.shift ≤ F.z₁ := by
    have hlead := T.lead_before_second
    omega
  have hz₁₂ : F.z₁ < F.z₂ := F.order₁₂
  have hz₂₃ : F.z₂ < F.z₃ := F.order₂₃
  have hz₃₄ : F.z₃ < F.z₄ := F.order₃₄
  have hv₁ : restrictedTonguesAt w N localStart
      (F.z₁ + 1 - T.shift) =
      restrictedTonguesAt w N start (F.z₁ + 1) := by
    obtain ⟨finish, hfinish⟩ := T.live (F.z₁ + 1 - T.shift)
    have h := restrictedTonguesAt_add_of_reach
      (N := N) (d := F.z₁ + 1 - T.shift) T.reached hfinish
    rw [← h]
    congr 1
    omega
  have hv₂ : restrictedTonguesAt w N localStart
      (F.z₂ + 1 - T.shift) =
      restrictedTonguesAt w N start (F.z₂ + 1) := by
    obtain ⟨finish, hfinish⟩ := T.live (F.z₂ + 1 - T.shift)
    have h := restrictedTonguesAt_add_of_reach
      (N := N) (d := F.z₂ + 1 - T.shift) T.reached hfinish
    rw [← h]
    congr 1
    omega
  have hv₃ : restrictedTonguesAt w N localStart
      (F.z₃ + 1 - T.shift) =
      restrictedTonguesAt w N start (F.z₃ + 1) := by
    obtain ⟨finish, hfinish⟩ := T.live (F.z₃ + 1 - T.shift)
    have h := restrictedTonguesAt_add_of_reach
      (N := N) (d := F.z₃ + 1 - T.shift) T.reached hfinish
    rw [← h]
    congr 1
    omega
  have hv₄ : restrictedTonguesAt w N localStart
      (F.z₄ + 1 - T.shift) =
      restrictedTonguesAt w N start (F.z₄ + 1) := by
    obtain ⟨finish, hfinish⟩ := T.live (F.z₄ + 1 - T.shift)
    have h := restrictedTonguesAt_add_of_reach
      (N := N) (d := F.z₄ + 1 - T.shift) T.reached hfinish
    rw [← h]
    congr 1
    omega
  have hnot₁ : restrictedTonguesAt w N localStart
      (F.z₁ + 1 - T.shift) ∉ history := by
    rw [hv₁]
    exact F.event₁.2.2.not_mem_rawPrefixHistory (Nat.le_refl _)
  have hnot₂ : restrictedTonguesAt w N localStart
      (F.z₂ + 1 - T.shift) ∉ history := by
    rw [hv₂]
    exact F.event₂.2.2.not_mem_rawPrefixHistory (by omega)
  have hnot₃ : restrictedTonguesAt w N localStart
      (F.z₃ + 1 - T.shift) ∉ history := by
    rw [hv₃]
    exact F.event₃.2.2.not_mem_rawPrefixHistory (by omega)
  have hnot₄ : restrictedTonguesAt w N localStart
      (F.z₄ + 1 - T.shift) ∉ history := by
    rw [hv₄]
    exact F.event₄.2.2.not_mem_rawPrefixHistory (by omega)
  obtain ⟨fresh, hfreshLength, hmem⟩ := hcover
  have hfresh₁ : restrictedTonguesAt w N localStart
      (F.z₁ + 1 - T.shift) ∈ fresh := by
    have hm := hmem (F.z₁ + 1 - T.shift) (by simp [localTimes])
    rcases List.mem_append.mp hm with hm | hm
    · exact (hnot₁ hm).elim
    · exact hm
  have hfresh₂ : restrictedTonguesAt w N localStart
      (F.z₂ + 1 - T.shift) ∈ fresh := by
    have hm := hmem (F.z₂ + 1 - T.shift) (by simp [localTimes])
    rcases List.mem_append.mp hm with hm | hm
    · exact (hnot₂ hm).elim
    · exact hm
  have hfresh₃ : restrictedTonguesAt w N localStart
      (F.z₃ + 1 - T.shift) ∈ fresh := by
    have hm := hmem (F.z₃ + 1 - T.shift) (by simp [localTimes])
    rcases List.mem_append.mp hm with hm | hm
    · exact (hnot₃ hm).elim
    · exact hm
  have hfresh₄ : restrictedTonguesAt w N localStart
      (F.z₄ + 1 - T.shift) ∈ fresh := by
    have hm := hmem (F.z₄ + 1 - T.shift) (by simp [localTimes])
    rcases List.mem_append.mp hm with hm | hm
    · exact (hnot₄ hm).elim
    · exact hm
  have hfreshCover : NoveltyCoverOn w N localStart localTimes [] 3 := by
    refine ⟨fresh, hfreshLength, ?_⟩
    intro d hd
    simp only [List.nil_append]
    simp only [localTimes, List.mem_cons, List.not_mem_nil,
      or_false] at hd
    rcases hd with h | h | h | h
    · simpa [h] using hfresh₁
    · simpa [h] using hfresh₂
    · simpa [h] using hfresh₃
    · simpa [h] using hfresh₄
  have hglobalNodup := four_raw_novel_post_vectors_nodup
    F.order₁₂ F.order₂₃ F.order₃₄
    F.event₁.2.2 F.event₂.2.2 F.event₃.2.2 F.event₄.2.2
  have hlocalNodup :
      (localTimes.map (restrictedTonguesAt w N localStart)).Nodup := by
    simpa [localTimes, hv₁, hv₂, hv₃, hv₄] using hglobalNodup
  have hcount := noveltyCoverOn_distinct_count hfreshCover hlocalNodup
  simp [localTimes] at hcount

/-- The finite list of repeated-writer novelties is chronologically ordered,
because it is a filter of `List.range`. -/
theorem rawRepeatedWriterNovelTimes_pairwise_lt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawRepeatedWriterNovelTimes w N start K).Pairwise (· < ·) := by
  classical
  unfold rawRepeatedWriterNovelTimes
  exact List.pairwise_lt_range.filter _

/-- **Global closure bridge.**  The exact five-frame manufactured-tail
extraction implies the raw known-edge four-event theorem.  This proof selects
the first five events from an arbitrary finite prefix, attaches all five raw
fixed-stem decompositions, invokes the physical extraction once, and closes
with the absolute three-vector runway theorem above. -/
theorem knownEdgeFourRepeatedWriterNovelty_of_fiveFrameRunwayExtraction
    (hextract : KnownEdgeFiveFrameRunwayExtraction) :
    KnownEdgeFourRepeatedWriterNovelty := by
  classical
  intro w N e hN start K hentry
  let events := rawRepeatedWriterNovelTimes w N start K
  by_cases hsmall : events.length ≤ 4
  · simpa [events] using hsmall
  · exfalso
    have hfive : 5 ≤ events.length := by omega
    let z₀ := events[0]'(by omega)
    let z₁ := events[1]'(by omega)
    let z₂ := events[2]'(by omega)
    let z₃ := events[3]'(by omega)
    let z₄ := events[4]'(by omega)
    have hsorted : events.Pairwise (· < ·) := by
      simpa [events] using rawRepeatedWriterNovelTimes_pairwise_lt
        w N start K
    have hget := List.pairwise_iff_getElem.mp hsorted
    have hz₀₁ : z₀ < z₁ := hget 0 1 (by omega) (by omega) (by omega)
    have hz₁₂ : z₁ < z₂ := hget 1 2 (by omega) (by omega) (by omega)
    have hz₂₃ : z₂ < z₃ := hget 2 3 (by omega) (by omega) (by omega)
    have hz₃₄ : z₃ < z₄ := hget 3 4 (by omega) (by omega) (by omega)
    have hmem₀ : z₀ ∈ rawRepeatedWriterNovelTimes w N start K := by
      simpa [events, z₀] using List.getElem_mem events (n := 0) (by omega)
    have hmem₁ : z₁ ∈ rawRepeatedWriterNovelTimes w N start K := by
      simpa [events, z₁] using List.getElem_mem events (n := 1) (by omega)
    have hmem₂ : z₂ ∈ rawRepeatedWriterNovelTimes w N start K := by
      simpa [events, z₂] using List.getElem_mem events (n := 2) (by omega)
    have hmem₃ : z₃ ∈ rawRepeatedWriterNovelTimes w N start K := by
      simpa [events, z₃] using List.getElem_mem events (n := 3) (by omega)
    have hmem₄ : z₄ ∈ rawRepeatedWriterNovelTimes w N start K := by
      simpa [events, z₄] using List.getElem_mem events (n := 4) (by omega)
    have H₀ : RawRepeatedWriterNovelAt w N start z₀ :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hmem₀).2
    have H₁ : RawRepeatedWriterNovelAt w N start z₁ :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hmem₁).2
    have H₂ : RawRepeatedWriterNovelAt w N start z₂ :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hmem₂).2
    have H₃ : RawRepeatedWriterNovelAt w N start z₃ :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hmem₃).2
    have H₄ : RawRepeatedWriterNovelAt w N start z₄ :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hmem₄).2
    obtain ⟨frame₀⟩ := H₀.fixedStemOpenFrame hN
    obtain ⟨frame₁⟩ := H₁.fixedStemOpenFrame hN
    obtain ⟨frame₂⟩ := H₂.fixedStemOpenFrame hN
    obtain ⟨frame₃⟩ := H₃.fixedStemOpenFrame hN
    obtain ⟨frame₄⟩ := H₄.fixedStemOpenFrame hN
    let F : FiveFixedStemNovelFrames w N start := {
      z₀ := z₀
      z₁ := z₁
      z₂ := z₂
      z₃ := z₃
      z₄ := z₄
      order₀₁ := hz₀₁
      order₁₂ := hz₁₂
      order₂₃ := hz₂₃
      order₃₄ := hz₃₄
      event₀ := H₀
      event₁ := H₁
      event₂ := H₂
      event₃ := H₃
      event₄ := H₄
      frame₀ := frame₀
      frame₁ := frame₁
      frame₂ := frame₂
      frame₃ := frame₃
      frame₄ := frame₄
    }
    obtain ⟨tail⟩ := hextract w N e hN start hentry F
    exact no_five_fixed_stem_novelties_of_runway_tail F tail

/-- Consequently, the explicit five-frame runway extraction closes the
public raw-track `StateLaw`. -/
theorem stateLaw_of_fiveFrameRunwayExtraction
    (hextract : KnownEdgeFiveFrameRunwayExtraction) : StateLaw :=
  stateLaw_of_knownEdgeFourRepeatedWriterNovelty
    (knownEdgeFourRepeatedWriterNovelty_of_fiveFrameRunwayExtraction
      hextract)

end GeneralN
