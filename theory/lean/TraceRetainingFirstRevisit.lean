import TripleSelfLinkSimpleCycleClosure

/-!
# Generic trace-retaining first revisit

`SettlesOnSimpleCycle` remembers only two period endpoint equations.  Sharp
novelty accounting needs the physical stable lap, because switch simplicity
is what proves that every intermediate tongue vector is unchanged.  The
self-link analysis already established the local trace-valued fork.  This
file packages the same decomposition for an arbitrary nonsimple physical
trace with a known incoming edge.
-/

namespace GeneralN

/-- Trace-retaining form of `PhysicalTrace.first_revisit_activated_outcome`.
The cycle branch keeps both the transient lap and the stable switch-simple
lap; the reflector branch keeps the actual manufactured reflector and its
completed return to the incoming edge. -/
theorem PhysicalTrace.first_revisit_trace_or_activated_reflector
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hnonsimple : ¬ SwitchSimple passages)
    {entryEdge : Nat}
    (hentry : w.link entryEdge = some start.1) :
    ∃ atRepeat visited,
      stepN w visited start = some atRepeat ∧
      ((∃ cycle settled,
          cycle ≠ [] ∧
          PhysicalTrace w atRepeat cycle (atRepeat.1, settled) ∧
          PhysicalTrace w (atRepeat.1, settled) cycle
            (atRepeat.1, settled) ∧
          SwitchSimple cycle) ∨
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
  have hout := first_revisit_cycle_traces_or_activated_reflector w
    hrunway hexcursion hsimpleBefore hswitch hrepeat hentry
  refine ⟨(q, u), before.length, ?_, ?_⟩
  · simpa [hbeforeSplit] using hbeforeTrace.sound
  · rcases hout with hcycle | hreflector
    · exact Or.inl hcycle
    · obtain ⟨A, state, hA, hbase, hstate, hback,
          hpreserves⟩ := hreflector
      exact Or.inr ⟨A, state, runway.length + 1,
        hA, by simpa using hbase, hstate, hback,
        by simpa using hpreserves⟩

end GeneralN
