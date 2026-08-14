import FirstReflectorNovelty
import RepeatedNoveltyDecomposition

/-!
# Sharp state-law assembly

This file contains only the final novelty bookkeeping around the physical
track constructions.  It deliberately separates two questions:

* the arithmetic/trajectory assembly proved here; and
* the remaining semantic assertion that every raw global-repair trajectory
  admits the advertised five-vector novelty cover.

The budget is exact:

* at most `N+1` historical vectors (the initial vector and at most one vector
  charged to each switch);
* four vectors for a compatible manufactured-reflector orbit; and
* one further vector for the strict foreign candy splice.

Thus a certified trajectory has at most `N+6` distinct tongue vectors.  No
path length or period length occurs in the conclusion.
-/

namespace GeneralN


def ManufacturedReflector.sharpConstructionHistory
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : List (List Bool) :=
  ((List.range (A.exploration.length + 1)).map
      (restrictedTonguesAt w N (g, A.baseState))) ++
    [VectorCount.restrict N A.activatedState]

/-- The canonical first-construction history has size at most `N+2`. -/
theorem ManufacturedReflector.sharpConstructionHistory_length
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N) :
    (A.sharpConstructionHistory N).length ≤ N + 2 := by
  have hlength : A.exploration.length ≤ N :=
    A.exploration_trace.simple_length_le hN A.exploration_simple
  simp [ManufacturedReflector.sharpConstructionHistory]
  omega

/-- Every raw vector through the complete first manufacturing journey lies
in the canonical `N+2` history.  This is pointwise, including the contact and
every depth of the reverse runway. -/
theorem ManufacturedReflector.manufacturing_journey_mem_sharpHistory
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    {j : Nat}
    (hj : j ≤ A.exploration.length + A.runway.length + 1) :
    restrictedTonguesAt w N (g, A.baseState) j ∈
      A.sharpConstructionHistory N := by
  let prefixHistory :=
    (List.range (A.exploration.length + 1)).map
      (restrictedTonguesAt w N (g, A.baseState))
  by_cases hprefix : j ≤ A.exploration.length
  · apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨j, List.mem_range.mpr (by omega), rfl⟩
  · have hvectorAtRepeat :
        restrictedTonguesAt w N (g, A.baseState)
            A.exploration.length =
          VectorCount.restrict N A.preReturn.2 := by
      simp [restrictedTonguesAt, tonguesAt,
        A.exploration_trace.sound]
    have hpre : VectorCount.restrict N A.preReturn.2 ∈
        prefixHistory := by
      rw [← hvectorAtRepeat]
      apply List.mem_map.mpr
      exact ⟨A.exploration.length,
        List.mem_range.mpr (by omega), rfl⟩
    rcases completed_retrace_at_vector_mem_history_or_contact
        A.runway_trace (A.runway_grooved hpaths) A.entryEdge
        A.return_arrive_mouth A.exploration_trace.sound
        N prefixHistory hpre (by omega) hj with hhistory | hactivated
    · exact List.mem_append_left _ hhistory
    · apply List.mem_append_right prefixHistory
      exact List.mem_singleton.mpr hactivated
theorem RawRepeatedWriterNovelAt.open_frame_with_fixed_stem_successors
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {right : Nat}
    (h : RawRepeatedWriterNovelAt w N start right) :
    ∃ left reroute,
      RawLastWriterFrame w N start left right ∧
      RawProductiveAt w N start reroute ∧
      rawWriterAt w start reroute ≠ rawWriterAt w start right ∧
      (∀ j, left < j → j < reroute →
        RawProductiveAt w N start j →
        rawWriterAt w start j ≠ rawWriterAt w start reroute) ∧
      RawOpenReroutingShape w N start left reroute right ∧
      (∃ next,
        stepN w (reroute + 1) start = some next ∧
        w.link (3 * rawWriterAt w start reroute) = some next.1) ∧
      (∃ next,
        stepN w (right + 1) start = some next ∧
        w.link (3 * rawWriterAt w start right) = some next.1) := by
  obtain ⟨left, reroute, F, hprod, hdiff, hfirst, hshape⟩ :=
    h.open_rerouting_decomposition hN
  exact ⟨left, reroute, F, hprod, hdiff, hfirst, hshape,
    rawProductiveAt_fixed_stem_successor hN hprod,
    rawProductiveAt_fixed_stem_successor hN h.1⟩

end GeneralN
