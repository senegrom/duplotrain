import TripleSelfLinkSimpleCycleClosure

/-!
# Sharp tongue count for the first simple-cycle outcome

The old `2*N+1` count charged an entire transient cycle lap by position.  In
the actual first-revisit construction the same-exit cycle is much sharper:
either it is stable immediately, or its very first passage installs the
settled tongue vector and every remaining passage is already grooved at that
vector.  Hence the cycle tail has only the repeat vector and the settled
vector.  A switch-simple prefix of length at most `N` therefore gives at most
`N+2` vectors total.
-/

namespace GeneralN

/-- A prefix of length at most `N` followed by one settled vector has at
most `N+2` distinct vectors, including the initial and boundary samples. -/
theorem prefix_then_settled_distinct_le
    {w : Wiring} {N L : Nat} {start atRepeat : Nat × Tongues} {settled : Tongues}
    (hreach : stepN w L start = some atRepeat) (hL : L ≤ N)
    (htail : ∀ d, 0 < d → ∃ port, stepN w d atRepeat = some (port, settled))
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 2 := by
  let history := (List.range (L + 1)).map (restrictedTonguesAt w N start) ++
    [VectorCount.restrict N settled]
  have hcover : ∀ k ∈ times, restrictedTonguesAt w N start k ∈ history := by
    intro k _
    by_cases hk : k ≤ L
    · exact List.mem_append_left _ (List.mem_map.mpr
        ⟨k, List.mem_range.mpr (by omega), rfl⟩)
    · obtain ⟨port, hr⟩ := htail (k - L) (by omega)
      have heq : k = L + (k - L) := by omega
      have hglobal : stepN w k start = some (port, settled) := by
        rw [heq, stepN_add, hreach]
        exact hr
      apply List.mem_append_right
      simp [restrictedTonguesAt, tonguesAt, hglobal]
  have hc := nodup_subset_length_nat hnd (by
    intro vector hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
    exact hcover k hk)
  simp only [history, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil] at hc
  omega

/-- First activation with the sharp `N+2` simple-cycle count. -/
theorem first_activated_count_outcome_sharp
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    (∀ times : List Nat,
      (times.map (restrictedTonguesAt w N start)).Nodup →
      times.length ≤ N + 2) ∨
      ∃ (A : ManufacturedReflector w start.1 e)
          (state : Tongues),
        PathGrooves A.toSupported.paths state ∧
        A.baseState = start.2 ∧
        state = A.activatedState ∧
        stepN w (A.exploration.length + A.runway.length + 1) start =
          some (e, state) ∧
        (∀ j, j ∉ A.exploration.map passageSwitch →
          state j = start.2 j) := by
  obtain ⟨lead, q, u, hleadTrace, hleadSimple, hfork⟩ :=
    first_revisit_fork hN hlive hentry
  have hvisited : stepN w lead.length start = some (q, u) := hleadTrace.sound
  have hvisitedLe : lead.length ≤ N :=
    hleadTrace.simple_length_le hN hleadSimple
  rcases hfork with hcycle | hreflector
  · left
    obtain ⟨settled, hsettled⟩ := hcycle
    exact fun times hnd => prefix_then_settled_distinct_le
      hvisited hvisitedLe hsettled times hnd
  · right
    obtain ⟨A, state, hgrooves, hbase, hactivated, hpreserves⟩ := hreflector
    have hgroovesActivated :
        PathGrooves A.toSupported.paths A.activatedState := by
      rw [← hactivated]
      exact hgrooves
    have hreachBase := A.manufacturing_journey_reaches_activated hgroovesActivated
    refine ⟨A, state, hgrooves, hbase, hactivated, ?_, hpreserves⟩
    simpa [hbase, hactivated] using hreachBase

end GeneralN
