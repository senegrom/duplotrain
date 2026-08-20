import BoundaryOccurrenceDamageElimination
import ProductiveBoundaryNAddFourComplete

/-!
# Eliminating the productive-boundary saving residual

The two support-damage outcomes of the productive boundary both expose the
same sharp changed contact of the first reflector: the damaged stable cycle
through its lead, the damaged opposite reflector through its exploration.
Under the *absent* boundary saving, starting at the boundary stem makes its
coordinate automatically reserved and closes every such contact at `N+3`.
Under the occurrence saving, the occurrence replacement closes the same
contact.  The provenance of the damage therefore need not survive as an
intermediate residual.
-/

namespace GeneralN


/-- Under the absent boundary saving, every sharp changed contact contradicts
saturation.  In the flip case the boundary stem makes its coordinate
automatically reserved from the strict approach. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_absent_changed_contact
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (habsentA : Not (S.source.k0 ∈
      S.A.exploration.map passageSwitch))
    (D : PartialSecondRunSharp.ChangedContact w S.A) : False := by
  have hApaths : PathGrooves S.A.toSupported.paths
      S.A.activatedState := S.grooves
  have hlive : forall k, k ∈ S.source.times ->
      (stepN w k (S.source.g, S.A.baseState)).isSome := by
    intro k hk
    simpa [S.reflector_base] using S.source.live k hk
  have hnd : (S.source.times.map
      (restrictedTonguesAt w N
        (S.source.g, S.A.baseState))).Nodup := by
    have htail := (List.nodup_cons.mp S.source.distinct).2
    simpa [S.reflector_base] using htail
  have hsaturated := S.source.saturated
  cases hkind : S.A with
  | stay R =>
      rw [hkind] at D hApaths hlive hnd
      have hbound :=
        D.stay_saving_all_run_distinct_le_N_add_three
          hN hApaths S.source.times hlive hnd
      exact absurd hbound (by omega)
  | flip R =>
      rw [hkind] at D hApaths hlive hnd habsentA
      have hbound :=
        D.changed_all_run_distinct_le_N_add_three_of_stem_reserved
          hN hApaths S.source.switch_lt S.source.stem
            habsentA S.source.times hlive hnd
      exact absurd hbound (by omega)

/-- Any switch-simple continuation that damages the first reflector's support
contradicts whichever boundary saving produced the saturated residual. -/
theorem ProductiveBoundaryNAddFourSavingResidual.false_of_broken_simple
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w
      (S.source.e, S.A.activatedState) passages finish)
    (hsimple : SwitchSimple passages)
    (hbroken : Not (PathGrooves S.A.toSupported.paths finish.2)) :
    False := by
  have hApaths : PathGrooves S.A.toSupported.paths
      S.A.activatedState := S.grooves
  obtain ⟨D⟩ :=
    PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple
      S.A hApaths htrace hsimple hbroken
  rcases S.saving with habsent | ⟨O, hstay⟩
  · exact S.false_of_absent_changed_contact hN habsent D
  · exact S.false_of_occurrence_changed_contact hN O hstay D

/-- **Final dead/cycle/reflector assembly.**  Every saturated productive
boundary saving residual is physically impossible. -/
theorem ProductiveBoundaryNAddFourSavingResidual.impossible
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) : False := by
  cases hprobe :
      stepN w (N + 1) (S.source.e, S.A.activatedState) with
  | none =>
      exact S.false_of_dead_second_probe hN hprobe
  | some finish =>
      have hback : w.link S.source.g = some S.source.e :=
        w.symm _ _ S.source.entry
      rcases first_activated_trace_outcome_sharp_partial
        hN hprobe hback with hcycle | hreflector
      case inl =>
        obtain ⟨C⟩ := hcycle
        by_cases hprotected :
            PathGrooves S.A.toSupported.paths C.atRepeat.2
        case pos =>
          exact S.false_of_preserved_second_cycle hN C hprotected
        case neg =>
          exact S.false_of_broken_simple
            hN C.lead_trace C.lead_simple hprotected
      case inr =>
        obtain ⟨B, _, hBpaths, hbase, rfl⟩ := hreflector
        by_cases hpre :
            PathGrooves S.A.toSupported.paths B.preReturn.2
        case neg =>
          exact S.false_of_broken_simple hN
            (by simpa [hbase] using B.exploration_trace)
            B.exploration_simple hpre
        case pos =>
          rcases S.saving with habsent | ⟨O, hstay⟩
          case inl =>
            exact S.false_of_absent_protected_pair_of_second_writer_absent
              hN habsent B hbase hBpaths hpre
                (stem_switch_not_mem_firstWriterSwitches_of_simple_trace
                  (N := N) S.source.stem B.exploration_trace
                    B.exploration_simple)
          case inr =>
            generalize hkind : S.A = A at O hstay hbase hpre
            cases A with
            | stay R =>
                exact S.false_of_first_stay_protected_pair
                  hN R hkind B hbase hBpaths hpre
            | flip R =>
                by_cases hcanonical :
                    O.before.length = R.runway.length
                · exact S.false_of_canonical_saturation
                    hN R hkind O hstay hcanonical
                · exact S.false_of_noncanonical_unchanged_protected_pair
                    hN R hkind O hstay hcanonical B
                      hbase hBpaths hpre

end GeneralN
