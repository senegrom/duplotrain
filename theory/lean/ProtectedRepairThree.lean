import KnownEdgeFive
import ChangedFlipCountActual

/-!
# Protected repair costs `N+4` vectors

All branches except the changed-forward flip splice were already at most
`N+4`.  The actual-lead count closes that final branch at `N+4` as well.
-/

namespace GeneralN

/-- **Protected-repair count:** every branch exposes at most `N+4` distinct
restricted tongue vectors. -/
theorem manufactured_pair_protected_repair_distinct_le_n_add_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, B.activatedState))).Nodup) :
    times.length ≤ N + 4 := by
  rcases manufactured_pair_protected_repair_quantitative_outcomes_count
      hN A B hA hB with hcount | hrest
  · have hc := hcount times hnd
    omega
  · rcases hrest with hfacing | hrest
    · have hc := hfacing.distinct_le_succ_succ hN times hnd
      omega
    · rcases hrest with hchanged | hcomplete
      · cases B with
        | stay R =>
            have hc := hchanged.stay_distinct_le_n_succ_two hN times hnd
            omega
        | flip R =>
            have hc := hchanged.flip_distinct_le_n_add_four_actual
              hN times hnd
            omega
      · obtain ⟨finalState, hrepair, hAfinal, hBfinal⟩ := hcomplete
        have hc := A.completed_route_with_pair_support_distinct_le_n_succ_four
          hN B B.baseState B.activatedState finalState hA hrepair
          hAfinal hBfinal times hlive hnd
        omega

end GeneralN
