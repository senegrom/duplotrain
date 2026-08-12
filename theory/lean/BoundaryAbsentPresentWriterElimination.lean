import BoundaryResidualSharpening

/-!
# Elimination of the absent-present-writer residual

A manufactured reflector's construction is switch-simple.  If that
construction starts at the stem of switch `k0`, then `k0` cannot be a
productive first writer: time zero is a quiet facing traversal, while a later
productive write would revisit the switch already used by the first passage.
This removes the absent-present-writer constructor from the productive-boundary
frontier.
-/

namespace GeneralN

/-- A switch-simple trace beginning at the stem of `k0` cannot productively
first-write `k0` during that trace. -/
theorem stem_switch_not_mem_firstWriterSwitches_of_simple_trace
    {w : Wiring} {N e k0 : Nat} {state : Tongues}
    {route : List Passage} {finish : Nat × Tongues}
    (hstem : e = 3 * k0)
    (htrace : PhysicalTrace w (e, state) route finish)
    (hsimple : SwitchSimple route) :
    Not (k0 ∈
      (rawFirstWriterTimes w N (e, state) route.length).map
        (rawWriterAt w (e, state))) := by
  intro hm
  obtain ⟨k, hk, hwriter⟩ := List.mem_map.mp hm
  have hkData := mem_rawFirstWriterTimes_iff.mp hk
  have hklt : k < route.length := hkData.1
  have hprod : RawProductiveAt w N (e, state) k := hkData.2.1
  by_cases hkzero : k = 0
  · subst k
    apply hprod.2
    rcases Option.isSome_iff_exists.mp hprod.1 with ⟨next, hnext⟩
    have hnextOne : stepN w 1 (e, state) = some next := by
      simpa using hnext
    have hemod : e % 3 = 0 := by omega
    have hediv : e / 3 = k0 := by omega
    have harrive : arrive state e =
        (selectedBranch state k0, state) := by
      simp [arrive, hemod, hediv, selectedBranch]
    have hnextState : next.2 = state := by
      simp only [stepN, step, harrive] at hnextOne
      cases hlink : w.link (selectedBranch state k0) with
      | none => simp [hlink] at hnextOne
      | some q =>
          simp [hlink] at hnextOne
          exact (Prod.mk.inj hnextOne.symm).2
    unfold restrictedTonguesAt tonguesAt
    rw [hnextOne]
    simp [hnextState, stepN]
  · have hkpos : 0 < k := by omega
    have hzeroInside : 0 < route.length := by omega
    have hzeroWriter :=
      htrace.rawWriterAt_eq_passageSwitch_getElem
        (k := 0) hzeroInside
    have hkWriter :=
      htrace.rawWriterAt_eq_passageSwitch_getElem
        (k := k) hklt
    have hpair := List.pairwise_iff_getElem.mp hsimple
    have hzeroMap : 0 < (route.map passageSwitch).length := by
      simpa using hzeroInside
    have hkMap : k < (route.map passageSwitch).length := by
      simpa using hklt
    have hne := hpair 0 k hzeroMap hkMap hkpos
    apply hne
    simp only [List.getElem_map]
    rw [← hzeroWriter, ← hkWriter]
    calc
      rawWriterAt w (e, state) 0 = e / 3 := by
        simp [rawWriterAt, rawEntryAt, stepN]
      _ = k0 := by omega
      _ = rawWriterAt w (e, state) k := hwriter.symm

/-- The construction of a manufactured reflector cannot productively
first-write its starting switch when the incoming port is that switch's
stem. -/
theorem ManufacturedReflector.stem_switch_not_mem_constructionFirstWriterSwitches
    {w : Wiring} {N g e k0 : Nat}
    (B : ManufacturedReflector w g e)
    (hstem : g = 3 * k0) :
    Not (k0 ∈ B.constructionFirstWriterSwitches N) := by
  exact stem_switch_not_mem_firstWriterSwitches_of_simple_trace
    hstem B.exploration_trace B.exploration_simple

/-- The absent-present-writer constructor in `BoundarySharpResidual` is
empty: the second construction starts at the boundary switch's stem. -/
theorem BoundarySharpResidual.absentPresentWriter_impossible
    {w : Wiring} {N : Nat}
    {S : ProductiveBoundaryNAddFourSavingResidual w N}
    (R : ManufacturedFlipReflector w S.source.g S.source.e)
    (_kind : S.A = ManufacturedReflector.flip R)
    (_absentA : Not (S.source.k0 ∈
      S.A.exploration.map passageSwitch))
    (P : PartialSecondReflectorCompletion S.A N)
    (_supportGrooved : PathGrooves S.A.toSupported.paths
      P.reflector.preReturn.2)
    (present : S.source.k0 ∈
      P.reflector.constructionFirstWriterSwitches N) : False := by
  exact (P.reflector.stem_switch_not_mem_constructionFirstWriterSwitches
    S.source.stem) present

end GeneralN
