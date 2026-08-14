import BoundaryApproachWrittenElimination
import BoundaryAbsentPresentWriterElimination
import BoundaryOccurrenceDamageElimination

/-!
# Sharp `N+4` state law

This file eliminates the four residual constructors isolated by
`BoundaryResidualSharpening` and closes the remaining arbitrary-start unit.
The known-incoming-edge theorem was already `N+4`; the result below proves
that the time-zero vector of a productive first passage is always historical.
-/

namespace GeneralN

/-- Every constructor in the final productive-boundary residual is
physically impossible. -/
theorem BoundarySharpResidual.impossible
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {S : ProductiveBoundaryNAddFourSavingResidual w N}
    (D : BoundarySharpResidual S) : False := by
  cases D with
  | approachWritten D =>
      exact D.impossible hN
  | occurrenceCycleDamage O hstay C damage =>
      have hA : PathGrooves S.A.toSupported.paths
          S.A.activatedState := by
        rw [← S.activated]
        exact S.grooves
      obtain ⟨contact⟩ :=
        PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple
          S.A hA C.lead_trace C.lead_simple damage
      exact S.false_of_occurrence_changed_contact
        hN O hstay contact
  | occurrenceReflectorDamage O hstay P damage =>
      have hA : PathGrooves S.A.toSupported.paths
          S.A.activatedState := by
        rw [← S.activated]
        exact S.grooves
      have htrace : PhysicalTrace w
          (S.source.e, S.A.activatedState)
          P.reflector.exploration P.reflector.preReturn := by
        simpa [P.base] using P.reflector.exploration_trace
      obtain ⟨contact⟩ :=
        PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple
          S.A hA htrace P.reflector.exploration_simple damage
      exact S.false_of_occurrence_changed_contact
        hN O hstay contact
  | absentPresentWriter R kind absentA P supportGrooved present =>
      exact BoundarySharpResidual.absentPresentWriter_impossible
        R kind absentA P supportGrooved present

/-- The productive arbitrary-start boundary fits the exact `N+4` budget. -/
theorem productiveInitialBoundaryNAddFour
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    ProductiveInitialBoundaryNAddFour w N := by
  apply (productiveInitialBoundaryNAddFour_iff_no_sharp_residual hN).2
  intro S D
  exact D.impossible hN

/-- **Sharp state law.**  A single train on any finite `N`-switch lazy-point
layout visits at most `N+4` pairwise-distinct tongue vectors. -/
theorem state_law_N_add_four : StateLawNAddFour := by
  apply stateLawNAddFour_of_known_edge_and_productive_boundary
  · intro w N hN
    exact knownIncomingEdgeNAddFour hN
  · intro w N hN
    exact productiveInitialBoundaryNAddFour hN

/-- The historically stated target `StateLaw` (`StateLaw.lean`), which the
whole bound-tightening campaign aimed at, follows a fortiori. -/
theorem stateLaw : StateLaw := by
  intro w N hN c0 ks hlive hnd
  have hnd' : (ks.map (fun k => VectorCount.restrict N
      ((stepN w k c0).getD c0).2)).Nodup := hnd
  have hbound := state_law_N_add_four w N hN c0 ks hlive hnd'
  omega

end GeneralN
