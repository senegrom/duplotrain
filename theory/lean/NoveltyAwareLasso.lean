import FirstActivatedExact
import SharpStateLawAssembly

/-! Novelty-aware assembly of two construction journeys and a repair lasso. -/

namespace GeneralN

/-- The complete lasso window, represented as restricted tongue vectors. -/
def EventuallyPeriodicWithin.tongueHistory
    {w : Wiring} (_h : EventuallyPeriodicWithin w start cap)
    (N : Nat) : List (List Bool) :=
  (List.range cap).map (restrictedTonguesAt w N start)

/-- Every local time is represented in the bounded lasso tongue history. -/
theorem EventuallyPeriodicWithin.mem_tongueHistory
    {w : Wiring} {start : Nat × Tongues} {cap N k : Nat}
    (h : EventuallyPeriodicWithin w start cap) :
    restrictedTonguesAt w N start k ∈ h.tongueHistory N := by
  obtain ⟨r, hr, heq⟩ := h.reduce_time (k := k)
  unfold EventuallyPeriodicWithin.tongueHistory
  apply List.mem_map.mpr
  refine ⟨r, List.mem_range.mpr hr, ?_⟩
  simp [restrictedTonguesAt, tonguesAt, heq]

private theorem zero_novelty_cover_of_mem
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (times : List Nat) (history : List (List Bool))
    (hmem : ∀ k ∈ times,
      restrictedTonguesAt w N start k ∈ history) :
    NoveltyCoverOn w N start times history 0 := by
  refine ⟨[], by simp, ?_⟩
  intro k hk
  simpa using hmem k hk

end GeneralN
