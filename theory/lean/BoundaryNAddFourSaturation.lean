import StateLawNAddFourTop
import ProductiveBoundarySupportContact
import ProtectedPairNAddFour
import BoundaryDoubleDuplicate

/-!
# Saturation at the productive `N+4` boundary

This file studies the exact gap between a known-incoming-edge `N+4` bound
and the productive arbitrary-start boundary.  It uses no finite-instance
argument.  If the extra pre-passage vector cannot be absorbed, then the
shifted known-edge run must use all `N+4` available vectors.  Saturation
therefore has two strong consequences:

* every live vector of the shifted run is already one of the selected
  vectors; and
* the original pre-flip vector never occurs anywhere on that run.

The first-activation geometry sharpens this further.  A productive first
revisit of the initially written switch closes a switch-simple transient
lap followed by a stable lap, hence has at most `N+1` vectors and cannot be
saturated.  Thus the only surviving first-journey configurations are a
literally absent initial coordinate or a facing occurrence which gives an
explicit pair of consecutive equal vectors.

The final theorem is a reduction, not a proof of
`ProductiveInitialBoundaryNAddFour`: its right-hand side is the strictly
smaller raw physical obstruction just described.
-/

namespace GeneralN

/-- A literal failure of boundary absorption after the known-edge run has
saturated its complete `N+4` allowance.  `covers_live` is the saturation
statement: there is no further live vector outside the selected family.
`avoids_original` records that the pre-flip vector is absent from the whole
shifted run, not merely from the selected times. -/
structure ProductiveBoundaryNAddFourSaturation
    (w : Wiring) (N : Nat) : Type where
  g : Nat
  e : Nat
  k0 : Nat
  original : Tongues
  base : Tongues
  entry : w.link e = some g
  stem : e = 3 * k0
  switch_lt : k0 < N
  base_flip : base = flipAt original k0
  times : List Nat
  live : forall k, k ∈ times ->
    (stepN w k (g, base)).isSome
  distinct : (VectorCount.restrict N original ::
    times.map (restrictedTonguesAt w N (g, base))).Nodup
  saturated : times.length = N + 4
  covers_live : forall d,
    (stepN w d (g, base)).isSome ->
    restrictedTonguesAt w N (g, base) d ∈
      times.map (restrictedTonguesAt w N (g, base))
  avoids_original : forall d,
    (stepN w d (g, base)).isSome ->
    restrictedTonguesAt w N (g, base) d ≠
      VectorCount.restrict N original

/-- The exact first-journey obstruction left by saturation.  The shifted
run has manufactured its first reflector.  At the initial switch `k0`,
either that coordinate is absent from the switch-simple exploration, or
its unique occurrence is facing: the tongue state is unchanged and the
two consecutive restricted vectors are literally equal. -/
structure ProductiveBoundaryNAddFourSavingResidual
    (w : Wiring) (N : Nat) : Type where
  source : ProductiveBoundaryNAddFourSaturation w N
  A : ManufacturedReflector w source.g source.e
  stateA : Tongues
  grooves : PathGrooves A.toSupported.paths stateA
  reflector_base : A.baseState = source.base
  activated : stateA = A.activatedState
  reached : stepN w
    (A.exploration.length + A.runway.length + 1)
    (source.g, source.base) = some (source.e, stateA)
  saving :
    ((¬ source.k0 ∈ A.exploration.map passageSwitch) ∧
      stateA source.k0 = source.base source.k0) ∨
      (Exists fun O : InitialEntryWriterOccurrence
          w source.g source.e source.k0 A =>
        O.next = O.middle ∧
          restrictedTonguesAt w N (source.g, A.baseState)
              O.before.length =
          restrictedTonguesAt w N (source.g, A.baseState)
              (O.before.length + 1))

/-- The first saving is not merely a cardinality statement.  In either
branch it gives a concrete `N+2` history which contains the arbitrary
pre-passage vector and covers the complete first manufacture. -/
theorem ProductiveBoundaryNAddFourSavingResidual.boundaryHistory
    {w : Wiring} {N : Nat}
    (R : ProductiveBoundaryNAddFourSavingResidual w N)
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N) :
    Nonempty (InitialBoundaryHistory w N
      R.source.g R.source.e R.A R.source.original) := by
  have hpaths :
      PathGrooves R.A.toSupported.paths R.A.activatedState := by
    rw [R.activated.symm]
    exact R.grooves
  rcases R.saving with habsent | hstay
  · exact boundary_history_of_entry_writer_absent
      R.A hN R.source.switch_lt habsent.1
        R.source.original hpaths
  · obtain ⟨O, hsame, _hduplicate⟩ := hstay
    exact boundary_history_of_entry_writer_stay
      R.A hN R.source.original hpaths O hsame

/-- A saturated family cannot fit into an `N+4` global history which also
contains the pre-passage vector.  The proof deliberately uses both global
saturation facts: `covers_live` puts every live shifted state into the
history, while `avoids_original` proves that the additional boundary vector
is genuinely new. -/
theorem ProductiveBoundaryNAddFourSaturation.false_of_global_history
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSaturation w N)
    (history : List (List Bool))
    (hlength : history.length <= N + 4)
    (horiginal : VectorCount.restrict N S.original ∈ history)
    (hglobal : forall d,
      (stepN w d (S.g, S.base)).isSome ->
      restrictedTonguesAt w N (S.g, S.base) d ∈ history) : False := by
  have htailNodup :
      (S.times.map
        (restrictedTonguesAt w N (S.g, S.base))).Nodup :=
    (List.nodup_cons.mp S.distinct).2
  have horiginalNotSelected :
      VectorCount.restrict N S.original ∉
        S.times.map
          (restrictedTonguesAt w N (S.g, S.base)) := by
    intro hmem
    obtain ⟨d, hd, heq⟩ := List.mem_map.mp hmem
    exact S.avoids_original d (S.live d hd) heq
  have haugmentedNodup :
      (VectorCount.restrict N S.original ::
        S.times.map
          (restrictedTonguesAt w N (S.g, S.base))).Nodup := by
    exact List.nodup_cons.mpr ⟨horiginalNotSelected, htailNodup⟩
  have hcover : NoveltyCoverOn w N (S.g, S.base) S.times history 0 := by
    refine ⟨[], by simp, ?_⟩
    intro d hd
    apply List.mem_append_left
    exact hglobal d (S.live d hd)
  have hcount := novelty_cover_count_with_historical_extra
    (VectorCount.restrict N S.original) hcover horiginal
      haugmentedNodup
  have hsaturated := S.saturated
  omega

/-- It is enough to cover the selected saturated family: `covers_live`
upgrades that finite inclusion to a cover of the complete shifted run. -/
theorem ProductiveBoundaryNAddFourSaturation.false_of_selected_history
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSaturation w N)
    (history : List (List Bool))
    (hlength : history.length <= N + 4)
    (horiginal : VectorCount.restrict N S.original ∈ history)
    (hselected : forall v,
      v ∈ S.times.map
        (restrictedTonguesAt w N (S.g, S.base)) -> v ∈ history) : False := by
  apply S.false_of_global_history history hlength horiginal
  intro d hd
  exact hselected _ (S.covers_live d hd)

private theorem saturation_nodup_of_map_nodup
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) :
    forall {xs : List alpha}, (xs.map f).Nodup -> xs.Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

private theorem saturation_live_distinct_le_of_stepN_none
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    {times : List Nat}
    (hnone : stepN w L start = none)
    (hlive : forall k, k ∈ times ->
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= L := by
  have htimesNodup : times.Nodup :=
    saturation_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  apply nodup_nat_lt_length htimesNodup
  intro k hk
  by_cases hlt : k < L
  · exact hlt
  · have hkEq : k = L + (k - L) := by omega
    have hnoneK : stepN w k start = none := by
      rw [hkEq, stepN_add, hnone]
      simp
    have hkLive := hlive k hk
    rw [hnoneK] at hkLive
    simp at hkLive

private theorem saturation_stable_simple_cycle_tail_distinct_le_one
    {w : Wiring} {N g : Nat} {settled : Tongues}
    {cycle : List Passage}
    (hnonempty : cycle ≠ [])
    (hstable : PhysicalTrace w (g, settled) cycle (g, settled))
    (hsimple : SwitchSimple cycle)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, settled))).Nodup) :
    times.length <= 1 := by
  have hcover : NoveltyCoverOn w N (g, settled) times
      [VectorCount.restrict N settled] 0 := by
    refine ⟨[], by simp, ?_⟩
    intro d _hd
    obtain ⟨port, hrun⟩ :=
      hstable.stable_simple_cycle_all_time hnonempty hsimple d
    simp [restrictedTonguesAt, tonguesAt, hrun]
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

/-- A switch-simple transient lap followed by its grooved stable replay has
at most `N+1` distinct vectors on the complete run. -/
private theorem saturation_early_cycle_distinct_le_N_add_one
    {w : Wiring} {N g : Nat} {base settled : Tongues}
    {cycle : List Passage}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hnonempty : cycle ≠ [])
    (htransient : PhysicalTrace w (g, base) cycle (g, settled))
    (hstable : PhysicalTrace w (g, settled) cycle (g, settled))
    (hsimple : SwitchSimple cycle)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, base)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, base))).Nodup) :
    times.length <= N + 1 := by
  let lead := cycle.length
  let history := (List.range (lead + 1)).map
    (restrictedTonguesAt w N (g, base))
  have hprefix : forall d, d <= lead ->
      restrictedTonguesAt w N (g, base) d ∈ history := by
    intro d hd
    dsimp [history]
    exact List.mem_map.mpr
      ⟨d, List.mem_range.mpr (by omega), rfl⟩
  have hboundary : VectorCount.restrict N settled ∈ history := by
    have hm := hprefix lead (Nat.le_refl _)
    have hvector : restrictedTonguesAt w N (g, base) lead =
        VectorCount.restrict N settled := by
      simp [restrictedTonguesAt, tonguesAt, lead, htransient.sound]
    rwa [hvector] at hm
  have htail : forall tailTimes : List Nat,
      (forall k, k ∈ tailTimes ->
        (stepN w k (g, settled)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N (g, settled))).Nodup ->
      tailTimes.length <= 1 := by
    intro tailTimes _htailLive htailNodup
    exact saturation_stable_simple_cycle_tail_distinct_le_one
      hnonempty hstable hsimple tailTimes htailNodup
  have hcount := boundary_history_then_direct_tail_distinct_le
    (show stepN w lead (g, base) = some (g, settled) by
      simpa [lead] using htransient.sound)
    history hprefix hboundary htail (by omega)
      times hlive hnd
  have hhistory : history.length = lead + 1 := by
    simp [history]
  have hlead : lead <= N := by
    dsimp [lead]
    exact htransient.simple_length_le hN hsimple
  omega

/-- Saturation lemma for the black-box known-edge theorem.  If the boundary
estimate fails, the tail has exactly `N+4` vectors.  Any additional live
vector would extend the selected list to `N+5`, so the selected vectors
cover the entire run.  The head of `distinct` then excludes the original
pre-flip vector globally. -/
theorem productive_boundary_N_add_four_or_saturation
    {w : Wiring} {N g e k0 : Nat}
    (hknown : KnownIncomingEdgeNAddFour w N)
    (hentry : w.link e = some g)
    (hstem : e = 3 * k0)
    (hk0 : k0 < N)
    (original base : Tongues)
    (hbase : base = flipAt original k0)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, base)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, base))).Nodup) :
    times.length + 1 <= N + 4 ∨
      Nonempty (ProductiveBoundaryNAddFourSaturation w N) := by
  have htailNodup :
      (times.map
        (restrictedTonguesAt w N (g, base))).Nodup :=
    (List.nodup_cons.mp hnd).2
  have htailBound := hknown hentry times hlive htailNodup
  by_cases hbound : times.length + 1 <= N + 4
  · exact Or.inl hbound
  · apply Or.inr
    have hsaturated : times.length = N + 4 := by omega
    have hcover : forall d,
        (stepN w d (g, base)).isSome ->
        restrictedTonguesAt w N (g, base) d ∈
          times.map (restrictedTonguesAt w N (g, base)) := by
      intro d hd
      by_cases hm : restrictedTonguesAt w N (g, base) d ∈
          times.map (restrictedTonguesAt w N (g, base))
      · exact hm
      · exfalso
        let augmented := d :: times
        have haugmentedLive : forall k, k ∈ augmented ->
            (stepN w k (g, base)).isSome := by
          intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact hd
          · exact hlive k hk
        have haugmentedNodup :
            (augmented.map
              (restrictedTonguesAt w N (g, base))).Nodup := by
          dsimp [augmented]
          rw [List.nodup_cons]
          exact ⟨hm, htailNodup⟩
        have htooMany :=
          hknown hentry augmented haugmentedLive haugmentedNodup
        have haugmentedLength :
            augmented.length = times.length + 1 := by
          simp [augmented]
        omega
    have havoid : forall d,
        (stepN w d (g, base)).isSome ->
        restrictedTonguesAt w N (g, base) d ≠
          VectorCount.restrict N original := by
      intro d hd heq
      have hm := hcover d hd
      have hhead := (List.nodup_cons.mp hnd).1
      apply hhead
      rw [← heq]
      exact hm
    exact ⟨{
      g := g
      e := e
      k0 := k0
      original := original
      base := base
      entry := hentry
      stem := hstem
      switch_lt := hk0
      base_flip := hbase
      times := times
      live := hlive
      distinct := hnd
      saturated := hsaturated
      covers_live := hcover
      avoids_original := havoid
    }⟩

/-- If the initially flipped coordinate has been restored at any live time
of a saturated counterexample, then some *other* counted coordinate must
still differ from the pre-passage state.  Otherwise the restricted vector
would be the globally forbidden original vector.  This is the pointwise
coordinate form of the saturation obstruction. -/
theorem ProductiveBoundaryNAddFourSaturation.restored_has_foreign_difference
    {w : Wiring} {N : Nat}
    (S : ProductiveBoundaryNAddFourSaturation w N)
    (d : Nat)
    (hlive : (stepN w d (S.g, S.base)).isSome)
    (hrestored :
      tonguesAt w (S.g, S.base) d S.k0 = S.original S.k0) :
    Exists fun C : Nat =>
      C < N ∧ C ≠ S.k0 ∧
        tonguesAt w (S.g, S.base) d C ≠ S.original C := by
  by_cases hexists : Exists fun C : Nat =>
      C < N ∧ C ≠ S.k0 ∧
        tonguesAt w (S.g, S.base) d C ≠ S.original C
  · exact hexists
  · exfalso
    apply S.avoids_original d hlive
    unfold restrictedTonguesAt
    unfold VectorCount.restrict
    apply List.map_congr_left
    intro C hCmem
    have hC : C < N := List.mem_range.mp hCmem
    by_cases hEq : C = S.k0
    · subst C
      exact hrestored
    · have hnot : ¬(
          C < N ∧ C ≠ S.k0 ∧
            tonguesAt w (S.g, S.base) d C ≠ S.original C) := by
        intro hdata
        exact hexists ⟨C, hdata⟩
      have hsame :
          ¬ tonguesAt w (S.g, S.base) d C ≠ S.original C := by
        intro hne
        exact hnot ⟨hC, hEq, hne⟩
      exact Classical.not_not.mp hsame

/-- **Exact independent saturation reduction.**

Assume the hypothetical known-incoming-edge `N+4` theorem.  For a productive
initial boundary, either the desired `N+4` estimate already holds, or the
shifted run is globally saturated and its first reflector has one of two
literal savings:

1. the initial coordinate is absent from the switch-simple exploration; or
2. its unique occurrence leaves the tongue state unchanged, producing two
   consecutive equal restricted vectors.

All other first-probe outcomes are eliminated here.  Death has at most
`N+1` live times, the first-cycle alternative has at most `N+2` vectors,
and a productive occurrence of `k0` is a transient/stable simple cycle with
at most `N+1` vectors.  The surviving right-hand side is therefore strictly
smaller than `ProductiveInitialBoundaryNAddFour`; it is not claimed to be
impossible in this file. -/
theorem productive_initial_boundary_N_add_four_or_saving_saturation
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hknown : KnownIncomingEdgeNAddFour w N)
    (hentry : w.link e = some g)
    (hstem : e = 3 * k0)
    (hk0 : k0 < N)
    (original base : Tongues)
    (hbase : base = flipAt original k0)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, base)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, base))).Nodup) :
    times.length + 1 <= N + 4 ∨
      Nonempty (ProductiveBoundaryNAddFourSavingResidual w N) := by
  rcases productive_boundary_N_add_four_or_saturation
      hknown hentry hstem hk0 original base hbase
        times hlive hnd with hbound | hsaturation
  · exact Or.inl hbound
  · apply Or.inr
    let S := Classical.choice hsaturation
    have htailNodup :
        (S.times.map
          (restrictedTonguesAt w N (S.g, S.base))).Nodup :=
      (List.nodup_cons.mp S.distinct).2
    cases hfirst : stepN w (N + 1) (S.g, S.base) with
    | none =>
        have hshort := saturation_live_distinct_le_of_stepN_none
          (N := N) hfirst S.live htailNodup
        have hsaturated := S.saturated
        omega
    | some finish =>
        rcases first_activated_count_outcome_sharp
            hN hfirst S.entry with hcycle | hreflector
        · have hshort := hcycle S.times htailNodup
          have hsaturated := S.saturated
          omega
        · let A := Exists.choose hreflector
          have hstateData := Exists.choose_spec hreflector
          let stateA := Exists.choose hstateData
          have hdata := Exists.choose_spec hstateData
          have hgrooves :
              PathGrooves A.toSupported.paths stateA := hdata.2.1
          have hreflectorBase : A.baseState = S.base := hdata.2.2.1
          have hactivated : stateA = A.activatedState :=
            hdata.2.2.2.1
          have hreached : stepN w
              (A.exploration.length + A.runway.length + 1)
              (S.g, S.base) = some (S.e, stateA) :=
            hdata.2.2.2.2.1
          have hpreserves : forall j,
              j ∉ A.exploration.map passageSwitch ->
              stateA j = S.base j :=
            hdata.2.2.2.2.2
          by_cases hmem : S.k0 ∈
              A.exploration.map passageSwitch
          · let O := Classical.choice
              (first_entry_writer_occurrence_dichotomy A hmem)
            rcases O.state_case with hstay | hflip
            · have hduplicate :=
                entry_writer_unchanged_gives_consecutive_duplicate
                  (N := N) A O hstay
              exact ⟨{
                source := S
                A := A
                stateA := stateA
                grooves := hgrooves
                reflector_base := hreflectorBase
                activated := hactivated
                reached := hreached
                saving := Or.inr ⟨O, hstay, hduplicate⟩
              }⟩
            · let cycle := O.before ++ [(O.p, O.x)]
              have hcycle :=
                productive_entry_writer_occurrence_is_simple_cycle
                  A S.stem O hflip
              have htransient : PhysicalTrace w (S.g, S.base)
                  cycle (S.g, O.next) := by
                have hraw := hcycle.2.1
                simpa [hreflectorBase] using hraw
              have hshort :=
                saturation_early_cycle_distinct_le_N_add_one
                  hN hcycle.1 htransient hcycle.2.2.1
                    hcycle.2.2.2 S.times S.live htailNodup
              have hsaturated := S.saturated
              omega
          · exact ⟨{
              source := S
              A := A
              stateA := stateA
              grooves := hgrooves
              reflector_base := hreflectorBase
              activated := hactivated
              reached := hreached
              saving := Or.inl ⟨hmem, hpreserves S.k0 hmem⟩
            }⟩

end GeneralN
