import StateLawNAddFourTop

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
literally absent initial coordinate or a facing occurrence, from which the
consecutive-vector equality can be derived when needed.

The final theorem is a reduction, not a proof of
`ProductiveInitialBoundaryNAddFour`: its right-hand side is the strictly
smaller raw physical obstruction just described.
-/

namespace GeneralN

/-- A literal failure of boundary absorption after the known-edge run has
saturated its complete `N+4` allowance.  `avoids_original` records that the
pre-flip vector is absent from the whole shifted run, not merely from the
selected times. -/
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
  avoids_original : forall d,
    (stepN w d (g, base)).isSome ->
    restrictedTonguesAt w N (g, base) d ≠
      VectorCount.restrict N original

/-- The exact first-journey obstruction left by saturation.  The shifted
run has manufactured its first reflector.  At the initial switch `k0`,
either that coordinate is absent from the switch-simple exploration, or
its unique occurrence leaves the state unchanged. -/
structure ProductiveBoundaryNAddFourSavingResidual
    (w : Wiring) (N : Nat) : Type where
  source : ProductiveBoundaryNAddFourSaturation w N
  A : ManufacturedReflector w source.g source.e
  grooves : PathGrooves A.toSupported.paths A.activatedState
  reflector_base : A.baseState = source.base
  saving :
    (¬ source.k0 ∈ A.exploration.map passageSwitch) ∨
      ∃ O : InitialEntryWriterOccurrence
          w source.g source.e source.k0 A, O.next = O.middle

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
  have hcount := noveltyCoverOn_distinct_count_with_extra
    hcover horiginal haugmentedNodup
  have hsaturated := S.saturated
  omega

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
      avoids_original := havoid
    }⟩

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
        have hshort := dead_horizon_live_distinct_le
          (N := N) hfirst S.times S.live htailNodup
        have hsaturated := S.saturated
        omega
    | some finish =>
        rcases first_activated_count_outcome_sharp
            hN hfirst S.entry with hcycle | hreflector
        · have hshort := hcycle S.times htailNodup
          have hsaturated := S.saturated
          omega
        · obtain ⟨A, _, hgrooves, hreflectorBase, rfl, _, _⟩ := hreflector
          by_cases hmem : S.k0 ∈
              A.exploration.map passageSwitch
          · let O := Classical.choice
              (first_entry_writer_occurrence_dichotomy A hmem)
            rcases O.state_case with hstay | hflip
            · exact ⟨{
                source := S
                A := A
                grooves := hgrooves
                reflector_base := hreflectorBase
                saving := Or.inr ⟨O, hstay⟩
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
              grooves := hgrooves
              reflector_base := hreflectorBase
              saving := Or.inl hmem
            }⟩

end GeneralN
