import BoundaryCanonicalGeometry
import TrackThetaAllTime

/-!
# Elimination of the canonical productive-boundary saturation

At the canonical unchanged occurrence, the first manufactured flip
reflector has empty runway and equal source and target ports.  Consequently
the reflector is already a same-endpoint lobe: after its manufacturing
journey, every future tongue vector is one of its two action phases.

The reduced boundary history contains `original` and every vector of the
manufacturing journey.  It also contains the activated phase.  Adding the
single opposite phase therefore gives a global history of length at most
`N + 3`, contradicting an `N + 4` saturation which globally avoids
`original`.

This is a direct raw-physical contradiction for arbitrary `N`.  It uses no
finite-instance argument and no second-reflector hypothesis.
-/

namespace GeneralN

/-- Pairing a grooved flip reflector with itself at equal endpoints collapses
the general four-phase law to its two action phases. -/
private theorem ManufacturedFlipReflector.same_endpoint_two_phase
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e)
    (hge : g = e)
    (state : Tongues)
    (hpaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths state)
    (d : Nat) :
    exists port phase,
      stepN w d (g, state) = some (port, phase) /\
        (phase = state \/ phase = flipAt state R.actionSwitch) := by
  subst e
  obtain ⟨port, phase, hrun, hphase⟩ :=
    manufactured_flip_pair_all_time_four_phase
      R R state hpaths hpaths d
  refine ⟨port, phase, hrun, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hphase
  rcases hphase with hstate | hfirst | hsecond | hboth
  · exact Or.inl hstate
  · exact Or.inr hfirst
  · exact Or.inr hsecond
  · exact Or.inl (by simpa [flipAt_flipAt] using hboth)

/-- **The canonical unchanged saturation is impossible.**

Canonicality forces an empty runway and a self-linked source.  The complete
future after the first manufacture then has only the activated phase and its
action mate.  Both manufacturing phases, `original`, and that one mate fit in
a global history of size at most `N + 3`, contradicting saturation and global
avoidance of `original`. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_canonical_saturation
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (hAeq : S.A = ManufacturedReflector.flip R)
    (O : InitialEntryWriterOccurrence
      w S.source.g S.source.e S.source.k0
        (ManufacturedReflector.flip R))
    (hstay : O.next = O.middle)
    (hcanonical : O.before.length = R.runway.length) :
    False := by
  let A : ManufacturedReflector w S.source.g S.source.e :=
    ManufacturedReflector.flip R
  let firstTravel := A.exploration.length + A.runway.length + 1
  let opposite := VectorCount.restrict N
    (flipAt A.activatedState R.actionSwitch)
  let history :=
    O.reducedBoundaryHistory N S.source.original ++ [opposite]

  have hgeometry := S.canonical_source_self_link R O hcanonical
  have hge : S.source.g = S.source.e := hgeometry.1
  have hApathsS : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [← S.activated]
    exact S.grooves
  have hApaths : PathGrooves A.toSupported.paths A.activatedState := by
    simpa [A, hAeq] using hApathsS
  have hAbase : A.baseState = S.source.base := by
    simpa [A, hAeq] using S.reflector_base
  have hreach : stepN w firstTravel
      (S.source.g, S.source.base) =
        some (S.source.e, A.activatedState) := by
    simpa [firstTravel, A, hAeq, S.activated] using S.reached
  have hreachSelf : stepN w firstTravel
      (S.source.g, S.source.base) =
        some (S.source.g, A.activatedState) := by
    simpa [hge] using hreach

  have hlengthReduced :=
    O.reducedBoundaryHistory_length hN S.source.original
  have hlength : history.length <= N + 3 := by
    dsimp [history]
    simp only [List.length_append, List.length_singleton]
    omega
  have horiginal : VectorCount.restrict N S.source.original ∈ history := by
    apply List.mem_append_left
    exact List.mem_cons_self
  have hactivated : VectorCount.restrict N A.activatedState ∈
      O.reducedBoundaryHistory N S.source.original := by
    apply O.sharp_mem_reduced_of_stay S.source.original hstay
    unfold ManufacturedReflector.sharpConstructionHistory
    apply List.mem_append_right
    exact List.mem_cons_self

  have hglobal : forall d,
      (stepN w d (S.source.g, S.source.base)).isSome ->
      restrictedTonguesAt w N (S.source.g, S.source.base) d ∈
        history := by
    intro d _hdLive
    by_cases hprefix : d <= firstTravel
    · apply List.mem_append_left
      apply O.sharp_mem_reduced_of_stay S.source.original hstay
      have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hApaths (j := d)
          (by simpa [firstTravel] using hprefix)
      have hmR :
          restrictedTonguesAt w N (S.source.g, S.source.base) d ∈
            (ManufacturedReflector.flip R).sharpConstructionHistory N := by
        simpa only [A, hAbase] using hm
      exact hmR
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hpathsR : PathGrooves
          (ManufacturedReflector.flip R).toSupported.paths
            (ManufacturedReflector.flip R).activatedState := by
        simpa [A] using hApaths
      obtain ⟨port, phase, hrun, hphase⟩ :=
        R.same_endpoint_two_phase hge
          (ManufacturedReflector.flip R).activatedState hpathsR q
      have hrunGlobal :
          stepN w d (S.source.g, S.source.base) =
            some (port, phase) := by
        rw [hdEq, stepN_add, hreachSelf]
        simpa [A] using hrun
      have hvector :
          restrictedTonguesAt w N (S.source.g, S.source.base) d =
            VectorCount.restrict N phase := by
        simp [restrictedTonguesAt, tonguesAt, hrunGlobal]
      rw [hvector]
      rcases hphase with hphase | hphase
      · apply List.mem_append_left
        simpa [A, hphase] using hactivated
      · apply List.mem_append_right
        simp [opposite, A, hphase]

  exact S.source.false_of_global_history
    history (by omega) horiginal hglobal

end GeneralN
