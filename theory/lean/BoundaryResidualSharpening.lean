import BoundaryOccurrenceDamageElimination
import KnownEdgeNAddFourComplete
import ProductiveBoundaryNAddFourComplete
import PartialSecondRunSharp

/-!
# Sharpening the productive-boundary residuals

The two support-damage residuals of the productive boundary both expose a sharp changed
contact of the first reflector: the damaged stable cycle through its
lead, the damaged opposite reflector through its exploration.  Under the
*absent* boundary saving the keystone dichotomy
(`BoundaryChangedContactSaving`) closes every such contact at `N+3` —
one inside saturation — unless the reflector is a flip whose strict
approach productively first-writes its action switch or the boundary
switch.  This file rewires the exact-residual reduction accordingly: the
two damage constructors survive only in that approach-written form or
under the occurrence saving.
-/


/-!
# Structural dichotomy for an unfinished second journey

This file separates the dynamic statement "the second probe does not
manufacture an opposite reflector" from the coefficient-one accounting
problem.  The dynamic conclusion is exact: the `N+1` probe either dies, or
reaches a stable switch-simple cycle.  The latter has one settled restricted
tongue vector at every absolute time after its transient lap.

The statements are over raw `Wiring`, `PhysicalTrace`, and `stepN`; there is
no finite-`N` evaluation and no hidden completion selector.
-/

namespace GeneralN

/-- The literal reflector payload returned by the second `N+1` probe. -/
structure PartialSecondReflectorCompletion
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : Type where
  reflector : ManufacturedReflector w e g
  base : reflector.baseState = A.activatedState

end GeneralN


/-!
# Coordinate charge in the canonical productive-boundary residual

This file isolates the remaining canonical branch.  At the unchanged
canonical occurrence, the initial boundary switch is the omitted action
switch of the first flip reflector.  Full coordinate charge therefore puts
that switch among the second reflector's productive first writers and the
present-writer boundary theorem closes the branch.

Saturation alone, however, leaves one exact arithmetic corner: if the action
is absent from the second first writers, the generic two-novelty protected
repair and the reserved-action charge bound meet at
`reusable + secondWriters + 1 = N`.  The final theorem records this tight
residual without claiming the unavailable full-charge equality.
-/

namespace GeneralN

end GeneralN


namespace GeneralN

/-- The refined damage residual: a flip first reflector whose changed
contact first-writes the omitted action switch or the boundary switch
during its strict approach. -/
structure BoundaryApproachWrittenResidual
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N) : Type where
  R : ManufacturedFlipReflector w S.source.g S.source.e
  kind : S.A = ManufacturedReflector.flip R
  absentExploration : Not (S.source.k0 ∈
    (ManufacturedReflector.flip R).exploration.map passageSwitch)
  contact : PartialSecondRunSharp.ChangedContact w
    (ManufacturedReflector.flip R)

/-- **The keystone applied to a saving residual.**  Under the absent
boundary saving, any sharp changed contact of the first reflector either
contradicts saturation or is the refined approach-written residual. -/
theorem ProductiveBoundaryNAddFourSavingResidual.changed_contact_approach_written_of_absent
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (habsentA : Not (S.source.k0 ∈
      S.A.exploration.map passageSwitch))
    (D : PartialSecondRunSharp.ChangedContact w S.A) :
    Nonempty (BoundaryApproachWrittenResidual S) := by
  have hApaths : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
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
      rcases D.flip_saving_le_N_add_three_or_approach_written
          hN hApaths S.source.switch_lt habsentA
            S.source.times hlive hnd with hbound | hwritten
      · exact absurd hbound (by omega)
      · exact ⟨{
          R := R
          kind := hkind
          absentExploration := habsentA
          contact := D
        }⟩

/-- A support-damaging stable second cycle under the absent saving is the
approach-written residual. -/
theorem ProductiveBoundaryNAddFourSavingResidual.cycle_damage_approach_written_of_absent
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (habsentA : Not (S.source.k0 ∈
      S.A.exploration.map passageSwitch))
    (C : PartialSecondCycleOutcome w
      (S.source.e, S.A.activatedState) N)
    (hdamage : Not
      (PathGrooves S.A.toSupported.paths C.atRepeat.2)) :
    Nonempty (BoundaryApproachWrittenResidual S) := by
  have hApaths : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
  obtain ⟨D⟩ := PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple S.A
    hApaths C.lead_trace C.lead_simple hdamage
  exact S.changed_contact_approach_written_of_absent
    hN habsentA D

/-- A support-damaging completed opposite reflector under the absent
saving is the approach-written residual. -/
theorem ProductiveBoundaryNAddFourSavingResidual.reflector_damage_approach_written_of_absent
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (habsentA : Not (S.source.k0 ∈
      S.A.exploration.map passageSwitch))
    (P : PartialSecondReflectorCompletion S.A N)
    (hdamage : Not (PathGrooves S.A.toSupported.paths
      P.reflector.preReturn.2)) :
    Nonempty (BoundaryApproachWrittenResidual S) := by
  have hApaths : PathGrooves S.A.toSupported.paths
      S.A.activatedState := by
    rw [<- S.activated]
    exact S.grooves
  have htrace : PhysicalTrace w
      (S.source.e, S.A.activatedState)
      P.reflector.exploration P.reflector.preReturn := by
    simpa [P.base] using P.reflector.exploration_trace
  obtain ⟨D⟩ := PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple S.A
    hApaths htrace P.reflector.exploration_simple hdamage
  exact S.changed_contact_approach_written_of_absent
    hN habsentA D

/-- The sharpened residual set.  Support damage survives only as an
approach-written flip contact or under the occurrence saving. -/
inductive BoundarySharpResidual
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N) : Type where
  | approachWritten
      (D : BoundaryApproachWrittenResidual S)
  | occurrenceCycleDamage
      (O : InitialEntryWriterOccurrence w
        S.source.g S.source.e S.source.k0 S.A)
      (hstay : O.next = O.middle)
      (C : PartialSecondCycleOutcome w
        (S.source.e, S.A.activatedState) N)
      (damage : Not
        (PathGrooves S.A.toSupported.paths C.atRepeat.2))
  | occurrenceReflectorDamage
      (O : InitialEntryWriterOccurrence w
        S.source.g S.source.e S.source.k0 S.A)
      (hstay : O.next = O.middle)
      (P : PartialSecondReflectorCompletion S.A N)
      (damage : Not (PathGrooves S.A.toSupported.paths
        P.reflector.preReturn.2))
  | absentPresentWriter
      (R : ManufacturedFlipReflector w S.source.g S.source.e)
      (kind : S.A = ManufacturedReflector.flip R)
      (absentA : Not (S.source.k0 ∈
        S.A.exploration.map passageSwitch))
      (P : PartialSecondReflectorCompletion S.A N)
      (supportGrooved : PathGrooves S.A.toSupported.paths
        P.reflector.preReturn.2)
      (present : S.source.k0 ∈
        P.reflector.constructionFirstWriterSwitches N)

/-- **Sharpened dead/cycle/reflector assembly.**  Every saving residual
reaches one of the four sharp constructors: the two absent-saving damage
branches collapse into the approach-written contact. -/
theorem ProductiveBoundaryNAddFourSavingResidual.reduces_to_sharp_residual
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    Nonempty (BoundarySharpResidual S) := by
  cases hprobe :
      stepN w (N + 1) (S.source.e, S.A.activatedState) with
  | none =>
      exact (S.false_of_dead_second_probe hN hprobe).elim
  | some finish =>
      have hback : w.link S.source.g = some S.source.e :=
        w.symm _ _ S.source.entry
      rcases first_activated_trace_outcome_sharp_partial
          hN hprobe hback with hcycle | hreflector
      case inl =>
        let C := Classical.choice hcycle
        by_cases hprotected :
            PathGrooves S.A.toSupported.paths C.atRepeat.2
        case pos =>
          exact (S.false_of_preserved_second_cycle
            hN C hprotected).elim
        case neg =>
          rcases S.saving with habsent | hoccurrence
          case inl =>
            obtain ⟨D⟩ := S.cycle_damage_approach_written_of_absent
              hN habsent.1 C hprotected
            exact ⟨BoundarySharpResidual.approachWritten D⟩
          case inr =>
            let O := Classical.choose hoccurrence
            have hOdata := Classical.choose_spec hoccurrence
            exact ⟨BoundarySharpResidual.occurrenceCycleDamage
              O hOdata.1 C hprotected⟩
      case inr =>
        let B := Exists.choose hreflector
        have hstateData := Exists.choose_spec hreflector
        let state := Exists.choose hstateData
        have hdata := Exists.choose_spec hstateData
        have hBpathsRaw :
            PathGrooves B.toSupported.paths state :=
          hdata.2.1
        have hbase : B.baseState = S.A.activatedState :=
          hdata.2.2.1
        have hactivated : state = B.activatedState :=
          hdata.2.2.2.1
        have hBpaths :
            PathGrooves B.toSupported.paths B.activatedState := by
          rw [<- hactivated]
          exact hBpathsRaw
        let P : PartialSecondReflectorCompletion S.A N := {
          reflector := B
          base := hbase
        }
        by_cases hpre :
            PathGrooves S.A.toSupported.paths B.preReturn.2
        case neg =>
          rcases S.saving with habsent | hoccurrence
          case inl =>
            obtain ⟨D⟩ := S.reflector_damage_approach_written_of_absent
              hN habsent.1 P (by simpa [P] using hpre)
            exact ⟨BoundarySharpResidual.approachWritten D⟩
          case inr =>
            let O := Classical.choose hoccurrence
            have hOdata := Classical.choose_spec hoccurrence
            exact ⟨BoundarySharpResidual.occurrenceReflectorDamage
              O hOdata.1 P (by simpa [P] using hpre)⟩
        case pos =>
          rcases S.saving with habsent | hoccurrence
          case inl =>
            by_cases hpresent : Membership.mem
                (B.constructionFirstWriterSwitches N) S.source.k0
            case pos =>
              cases hkind : S.A with
              | stay R =>
                  exact (S.false_of_first_stay_protected_pair
                    hN R hkind B
                      (by simpa [hkind] using hbase)
                      hBpaths (by simpa [hkind] using hpre)).elim
              | flip R =>
                  exact ⟨BoundarySharpResidual.absentPresentWriter
                    R hkind habsent.1 P (by simpa [P] using hpre)
                      (by simpa [P] using hpresent)⟩
            case neg =>
              exact (S.false_of_absent_protected_pair_of_second_writer_absent
                hN habsent.1 B hbase hBpaths hpre hpresent).elim
          case inr =>
            let O := Classical.choose hoccurrence
            have hOdata := Classical.choose_spec hoccurrence
            have hstay : O.next = O.middle := hOdata.1
            cases hkind : S.A with
            | stay R =>
                let Ostay : InitialEntryWriterOccurrence
                    w S.source.g S.source.e S.source.k0
                      (ManufacturedReflector.stay R) := {
                  before := O.before
                  after := O.after
                  p := O.p
                  x := O.x
                  nextPort := O.nextPort
                  middle := O.middle
                  next := O.next
                  split := by simpa [hkind] using O.split
                  switch_eq := O.switch_eq
                  before_trace := by
                    simpa [hkind] using O.before_trace
                  arrive_eq := O.arrive_eq
                  link_eq := O.link_eq
                  reach := by simpa [hkind] using O.reach
                  prefix_foreign := O.prefix_foreign
                  prefix_preserves := by
                    simpa [hkind] using O.prefix_preserves
                  state_case := O.state_case
                }
                have hstayStay : Ostay.next = Ostay.middle := by
                  exact hstay
                exact (S.false_of_unchanged_stay_protected_pair
                  hN R hkind Ostay hstayStay B
                    (by simpa [hkind] using hbase)
                    hBpaths (by simpa [hkind] using hpre)).elim
            | flip R =>
                let Oflip : InitialEntryWriterOccurrence
                    w S.source.g S.source.e S.source.k0
                      (ManufacturedReflector.flip R) := {
                  before := O.before
                  after := O.after
                  p := O.p
                  x := O.x
                  nextPort := O.nextPort
                  middle := O.middle
                  next := O.next
                  split := by simpa [hkind] using O.split
                  switch_eq := O.switch_eq
                  before_trace := by
                    simpa [hkind] using O.before_trace
                  arrive_eq := O.arrive_eq
                  link_eq := O.link_eq
                  reach := by simpa [hkind] using O.reach
                  prefix_foreign := O.prefix_foreign
                  prefix_preserves := by
                    simpa [hkind] using O.prefix_preserves
                  state_case := O.state_case
                }
                have hstayFlip : Oflip.next = Oflip.middle := by
                  exact hstay
                by_cases hcanonical :
                    Oflip.before.length = R.runway.length
                case pos =>
                  exact (S.false_of_canonical_saturation
                    hN R hkind Oflip hstayFlip hcanonical).elim
                case neg =>
                  exact (S.false_of_noncanonical_unchanged_protected_pair
                    hN R hkind Oflip hstayFlip hcanonical B
                      (by simpa [hkind] using hbase)
                      hBpaths (by simpa [hkind] using hpre)).elim

/-- **The sharpened equivalence.**  The productive boundary theorem — and
with it the exact `N+4` state law — is equivalent to eliminating the four
sharp residual constructors. -/
theorem productiveInitialBoundaryNAddFour_iff_no_sharp_residual
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    ProductiveInitialBoundaryNAddFour w N <->
      forall S : ProductiveBoundaryNAddFourSavingResidual w N,
        BoundarySharpResidual S -> False := by
  constructor
  case mp =>
    intro hboundary S _residual
    have hbound := hboundary S.source.entry S.source.stem
      S.source.switch_lt S.source.base_flip S.source.times
        S.source.live S.source.distinct
    have hsaturated := S.source.saturated
    omega
  case mpr =>
    intro hno
    unfold ProductiveInitialBoundaryNAddFour
    intro g e k0 original base hentry hstem hk0 hbase
      times hlive hnd
    rcases productive_initial_boundary_N_add_four_or_saving_saturation
        hN (knownIncomingEdgeNAddFour hN) hentry hstem hk0
          original base hbase times hlive hnd with hbound | hsaving
    case inl =>
      exact hbound
    case inr =>
      let S := Classical.choice hsaving
      exact (hno S
        (Classical.choice (S.reduces_to_sharp_residual hN))).elim

end GeneralN
