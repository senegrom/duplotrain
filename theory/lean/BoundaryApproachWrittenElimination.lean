import BoundaryResidualSharpening

/-!
# Elimination of the approach-written productive-boundary residual

The shifted second run starts at the stem of the boundary switch.  Hence a
switch-simple strict approach cannot first-write that boundary switch: time
zero is a quiet facing traversal, while a later visit would repeat its switch.
If the old action is first-written instead, the forward tail has only one fresh
corner and the boundary coordinate remains reserved.  In either case the
changed-contact run has at most `N+3` selected vectors, contradicting boundary
saturation at `N+4`.
-/

namespace GeneralN

/-- The approach-written constructor in `BoundarySharpResidual` is empty. -/
theorem BoundaryApproachWrittenResidual.impossible
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {S : ProductiveBoundaryNAddFourSavingResidual w N}
    (D : BoundaryApproachWrittenResidual S) : False := by
  let C := D.contact
  have hA : PathGrooves
      (ManufacturedReflector.flip D.R).toSupported.paths
      (ManufacturedReflector.flip D.R).activatedState := by
    rw [← D.kind, ← S.activated]
    exact S.grooves
  have hAbase : (ManufacturedReflector.flip D.R).baseState =
      S.source.base := by
    simpa [D.kind] using S.reflector_base
  have hlive : forall k, k ∈ S.source.times ->
      (stepN w k
        (S.source.g,
          (ManufacturedReflector.flip D.R).baseState)).isSome := by
    intro k hk
    simpa [hAbase] using S.source.live k hk
  have hnd : (S.source.times.map
      (restrictedTonguesAt w N
        (S.source.g,
          (ManufacturedReflector.flip D.R).baseState))).Nodup := by
    have htail := (List.nodup_cons.mp S.source.distinct).2
    simpa [hAbase] using htail
  have hbound :=
    C.changed_all_run_distinct_le_N_add_three_of_stem_reserved
      hN hA S.source.switch_lt S.source.stem
      D.absentExploration S.source.times hlive hnd
  have hsaturated := S.source.saturated
  omega

end GeneralN
