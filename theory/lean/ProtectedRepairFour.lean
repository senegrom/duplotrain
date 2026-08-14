import ChangedFlipCountFour
import CompleteRepairFour

/-! Every protected repair uses at most four restricted tongue vectors. -/

namespace GeneralN

/-- **Uniform four-vector protected-repair bound.** -/
theorem manufactured_pair_protected_repair_distinct_le_four
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ 4 := by
  rcases manufactured_pair_protected_repair_constant_outcomes
      A B hA hB with hcount | hrest
  · have hc := hcount times hlive hnd
    omega
  · rcases hrest with hfacing | hrest
    · have hc := hfacing.distinct_le_three hA hB times hlive hnd
      omega
    · rcases hrest with hchanged | hcomplete
      · cases B with
        | stay R =>
            have hc := hchanged.stay_distinct_le_three
              hA hB times hlive hnd
            omega
        | flip R =>
            exact hchanged.flip_distinct_le_four hA hB times hnd
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        exact A.completed_protected_route_with_pair_distinct_le_four
          B hA hB hrepair hAfinal hBfinal times hlive hnd

end GeneralN
