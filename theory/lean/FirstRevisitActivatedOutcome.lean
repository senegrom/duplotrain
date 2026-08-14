import RunwayHistoricalThree
import SharpStateLawAssembly

/-!
# The activated first-revisit outcome, standalone

The first-probe normal form and the post-vector freshness fact the
self-link tail analysis consumes, extracted so it does not depend on the
five-frame certificate programme.
-/

namespace GeneralN

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

end GeneralN
