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

end GeneralN
