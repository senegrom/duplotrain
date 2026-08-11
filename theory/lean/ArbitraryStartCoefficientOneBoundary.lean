import StateLawCoefficientOneTop

/-!
# Arbitrary-start boundary absorption at coefficient one

This file is intentionally isolated from the known-edge proof.  It records
the exact first-step obligation needed to turn the closed known-edge `N + 6`
bound into the raw arbitrary-start theorem, without charging time zero as an
unstructured extra vector.
-/

namespace GeneralN

/-- The exact productive first-step obligation.  The hypotheses say that the
tail starts immediately after an actual trailing passage through switch `k0`:
the crossed exit is the stem `3*k0`, the resulting state is the one-bit flip
of the pre-passage state, and that switch is one of the `N` counted switches.

Unlike an unrestricted `cap + 1` lift, the conclusion counts the pre-passage
vector and all selected tail vectors together inside the same `N + 6` cap. -/
def ProductiveInitialBoundaryCap (w : Wiring) (N : Nat) : Prop :=
  forall {g e k0 : Nat} {original base : Tongues},
    w.link e = some g ->
    e = 3 * k0 ->
    k0 < N ->
    base = flipAt original k0 ->
    forall times : List Nat,
      (forall k, k ∈ times ->
        (stepN w k (g, base)).isSome) ->
      (VectorCount.restrict N original ::
        times.map (restrictedTonguesAt w N (g, base))).Nodup ->
      times.length + 1 <= N + 6

/-- A literal saturated counterexample to boundary absorption.  There are
`N+6` distinct states on the known-edge tail and the actual state immediately
before the productive trailing passage is a further distinct vector. -/
structure ProductiveInitialBoundarySaturation
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
  saturated : times.length = N + 6

/-- The residual after the first-history analysis has been performed.  In
particular, this is not merely the assertion that a productive first step
occurred: the first known-edge run has manufactured a reflector, and an
`InitialBoundaryHistory` of size at most `N+2` already contains both the
pre-step vector and every vector of that first journey. -/
structure ProductiveInitialBoundaryHistorySaturation
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
  A : ManufacturedReflector w g e
  stateA : Tongues
  grooves : PathGrooves A.toSupported.paths stateA
  reflector_base : A.baseState = base
  activated : stateA = A.activatedState
  reached : stepN w
    (A.exploration.length + A.runway.length + 1) (g, base) =
      some (e, stateA)
  boundary : InitialBoundaryHistory w N g e A original
  times : List Nat
  live : forall k, k ∈ times ->
    (stepN w k (g, base)).isSome
  distinct : (VectorCount.restrict N original ::
    times.map (restrictedTonguesAt w N (g, base))).Nodup
  saturated : times.length = N + 6

private theorem boundary_nodup_of_map_nodup
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

private theorem boundary_nodup_map_filter
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {f : Nat -> alpha} (p : Nat -> Bool) :
    forall {xs : List Nat},
      (xs.map f).Nodup -> ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true,
            List.map_cons, List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            apply hnd.1
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem boundary_nodup_filter_nat (p : Nat -> Bool) :
    forall {xs : List Nat}, xs.Nodup -> (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hm => hnd.1 (List.mem_filter.mp hm).1, ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem boundary_zero_positive_partition :
    forall xs : List Nat,
      (xs.filter (fun k => decide (k = 0))).length +
        (xs.filter (fun k => decide (0 < k))).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons k rest ih =>
      by_cases hk : k = 0
      · subst k
        simp
        omega
      · have hkPos : 0 < k := by omega
        simp [hk, hkPos]
        omega

private theorem boundary_zero_filter_length_le_one
    {xs : List Nat} (hnd : xs.Nodup) :
    (xs.filter (fun k => decide (k = 0))).length <= 1 := by
  have hfilterNodup :
      (xs.filter (fun k => decide (k = 0))).Nodup :=
    boundary_nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

private theorem boundary_nodup_map_eq_of_mem
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) {xs : List alpha}
    (hnd : (xs.map f).Nodup) {a b : alpha}
    (ha : a ∈ xs) (hb : b ∈ xs) (heq : f a = f b) : a = b := by
  induction xs generalizing a b with
  | nil => cases ha
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp ha with ha | ha
      · rcases List.mem_cons.mp hb with hb | hb
        · subst a
          subst b
          rfl
        · subst a
          exfalso
          apply hnd.1
          exact List.mem_map.mpr ⟨b, hb, heq.symm⟩
      · rcases List.mem_cons.mp hb with hb | hb
        · subst b
          exfalso
          apply hnd.1
          exact List.mem_map.mpr ⟨a, ha, heq⟩
        · exact ih hnd.2 ha hb heq

private theorem boundary_live_distinct_le_of_stepN_none
    {w : Wiring} {N L : Nat} {start : Nat × Tongues}
    {times : List Nat}
    (hnone : stepN w L start = none)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= L := by
  have htimesNodup : times.Nodup :=
    boundary_nodup_of_map_nodup
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

/-- The exceptional nonquiet return in the initial-boundary split is itself
a switch-simple transient lap followed by a grooved stable lap.  Its complete
known-edge run has at most `N+1` distinct vectors, so it cannot be an `N+6`
saturated tail. -/
private theorem boundary_early_cycle_distinct_le_N_add_one
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
    intro tailTimes _ htailNodup
    have hcover : NoveltyCoverOn w N (g, settled)
        tailTimes [VectorCount.restrict N settled] 0 := by
      refine ⟨[], by simp, ?_⟩
      intro d _
      obtain ⟨port, hrun⟩ :=
        hstable.stable_simple_cycle_all_time hnonempty hsimple d
      simp [restrictedTonguesAt, tonguesAt, hrun]
    have hcount := noveltyCoverOn_distinct_count hcover htailNodup
    simpa using hcount
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

/-- Every saturated productive boundary has already passed the complete
`InitialBoundaryHistory` split.  The alternative nonquiet return is excluded
by the preceding sharp early-cycle count.  Thus this theorem identifies the
precise remaining mathematical object rather than concealing it in a `+1`. -/
theorem saturated_productive_initial_has_boundary_history
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hentry : w.link e = some g)
    (he : e = 3 * k0)
    (hk0 : k0 < N)
    (original base : Tongues)
    (hbaseShift : base = flipAt original k0)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, base)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map (restrictedTonguesAt w N (g, base))).Nodup)
    (hsaturated : times.length = N + 6) :
    Nonempty (ProductiveInitialBoundaryHistorySaturation w N) := by
  have hlocalNodup :
      (times.map
        (restrictedTonguesAt w N (g, base))).Nodup :=
    (List.nodup_cons.mp hnd).2
  cases hfirst : stepN w (N + 1) (g, base) with
  | none =>
      have hc := boundary_live_distinct_le_of_stepN_none
        (N := N) hfirst hlive hlocalNodup
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycle | hreflector
      · have hc := hcycle times hlocalNodup
        omega
      · let A := Exists.choose hreflector
        have hreflectorState := Exists.choose_spec hreflector
        let stateA := Exists.choose hreflectorState
        have hdata := Exists.choose_spec hreflectorState
        have hgrooves :
            PathGrooves A.toSupported.paths stateA := hdata.2.1
        have hbase : A.baseState = base := hdata.2.2.1
        have hactivated : stateA = A.activatedState :=
          hdata.2.2.2.1
        have hreach : stepN w
            (A.exploration.length + A.runway.length + 1)
            (g, base) = some (e, stateA) := hdata.2.2.2.2.1
        have hgroovesActivated :
            PathGrooves A.toSupported.paths A.activatedState :=
          Eq.mp (congrArg
            (fun state => PathGrooves A.toSupported.paths state)
            hactivated) hgrooves
        have hbaseOriginal :
            A.baseState = flipAt original k0 :=
          hbase.trans hbaseShift
        rcases first_history_absorbed_or_productive_nonquiet_entry_return
            A hN hk0 original hbaseOriginal hgroovesActivated with
          hhistory | hreturn
        · let H := Classical.choice hhistory
          exact ⟨{
            g := g
            e := e
            k0 := k0
            original := original
            base := base
            entry := hentry
            stem := he
            switch_lt := hk0
            base_flip := hbaseShift
            A := A
            stateA := stateA
            grooves := hgrooves
            reflector_base := hbase
            activated := hactivated
            reached := hreach
            boundary := H
            times := times
            live := hlive
            distinct := hnd
            saturated := hsaturated
          }⟩
        · let O := Exists.choose hreturn
          have hO := Exists.choose_spec hreturn
          let cycle := O.before ++ [(O.p, O.x)]
          have hcycle :=
            productive_entry_writer_occurrence_is_simple_cycle
              A he O hO.1
          have hstartEq : (g, A.baseState) = (g, base) :=
            Prod.ext rfl hbase
          have htransient : PhysicalTrace w (g, base)
              cycle (g, O.next) := by
            exact Eq.mp (congrArg
              (fun c => PhysicalTrace w c cycle (g, O.next))
              hstartEq) hcycle.2.1
          have hc := boundary_early_cycle_distinct_le_N_add_one
            hN hcycle.1 htransient hcycle.2.2.1 hcycle.2.2.2
              times hlive hlocalNodup
          omega

/-- The productive boundary cap is equivalent to excluding the explicit
saturated first-history residual, once the closed known-edge `N+6` theorem is
available.  This direction is the useful one for the remaining proof: no
other arbitrary-start case remains. -/
theorem productiveInitialBoundaryCap_of_no_history_saturation
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hno : ProductiveInitialBoundaryHistorySaturation w N -> False) :
    ProductiveInitialBoundaryCap w N := by
  intro g e k0 original base hentry he hk0 hbase
    times hlive hnd
  have hlocalNodup := (List.nodup_cons.mp hnd).2
  have hknown := known_edge_all_run_distinct_le_N_add_six
    hN hentry times hlive hlocalNodup
  by_cases hbound : times.length + 1 <= N + 6
  · exact hbound
  · exfalso
    have hsaturated : times.length = N + 6 := by omega
    obtain ⟨S⟩ := saturated_productive_initial_has_boundary_history
      hN hentry he hk0 original base hbase
        times hlive hnd hsaturated
    exact hno S

/-- Exact arbitrary-start lift.  An ordinary `N+6` known-edge theorem is
enough for a quiet first passage.  A productive first passage is not charged
as an anonymous extra singleton: it is handed to the explicit physical
boundary obligation `ProductiveInitialBoundaryCap`. -/
theorem arbitrary_start_distinct_le_N_add_six_of_productive_boundary
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hproductive : ProductiveInitialBoundaryCap w N)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : forall k, k ∈ times -> (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= N + 6 := by
  rcases start with ⟨startPort, startState⟩
  have htimesNodup : times.Nodup :=
    boundary_nodup_of_map_nodup
      (restrictedTonguesAt w N (startPort, startState)) hnd
  cases hone : stepN w 1 (startPort, startState) with
  | none =>
      have hzero : forall k, k ∈ times -> k = 0 := by
        intro k hk
        by_cases hk0 : k = 0
        · exact hk0
        · have hkPos : 0 < k := by omega
          have hkEq : k = 1 + (k - 1) := by omega
          have hnone : stepN w k (startPort, startState) = none := by
            rw [hkEq, stepN_add, hone]
            simp
          have hkLive := hlive k hk
          simp [hnone] at hkLive
      have hlen : times.length <= 1 :=
        nodup_nat_lt_length htimesNodup (by
          intro k hk
          have hk0 := hzero k hk
          omega)
      omega
  | some middle =>
      have honeStep : stepN w 1 (startPort, startState) = some middle :=
        hone
      simp only [stepN, step] at hone
      let localStep := arrive startState startPort
      cases hlink : w.link localStep.1 with
      | none =>
          simp [localStep, hlink] at hone
      | some entry =>
          have hmiddle : middle = (entry, localStep.2) := by
            simpa [localStep, hlink] using hone.symm
          subst middle
          let positive := times.filter (fun k => decide (0 < k))
          let shifted := positive.map (fun k => k - 1)
          let zeroTimes := times.filter (fun k => decide (k = 0))
          have hshiftVector : shifted.map
                (restrictedTonguesAt w N (entry, localStep.2)) =
              positive.map
                (restrictedTonguesAt w N (startPort, startState)) := by
            dsimp [shifted]
            rw [List.map_map]
            apply List.map_congr_left
            intro k hk
            have hkPos : 0 < k :=
              of_decide_eq_true (List.mem_filter.mp hk).2
            have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
            have hkEq : k = 1 + (k - 1) := by omega
            have hkLive := hlive k hkTimes
            have hrun : stepN w k (startPort, startState) =
                stepN w (k - 1) (entry, localStep.2) := by
              rw [hkEq, stepN_add, honeStep]
              simp
            cases htail : stepN w (k - 1) (entry, localStep.2) with
            | none =>
                rw [hrun, htail] at hkLive
                simp at hkLive
            | some finish =>
                have hglobal : stepN w k (startPort, startState) =
                    some finish := by rw [hrun, htail]
                simp [Function.comp_apply, restrictedTonguesAt,
                  tonguesAt, hglobal, htail]
          have hpositiveNodup :
              (positive.map
                (restrictedTonguesAt w N
                  (startPort, startState))).Nodup := by
            dsimp [positive]
            exact boundary_nodup_map_filter _ hnd
          have hshiftedNodup :
              (shifted.map
                (restrictedTonguesAt w N
                  (entry, localStep.2))).Nodup := by
            rw [hshiftVector]
            exact hpositiveNodup
          have hshiftedLive : forall d, d ∈ shifted ->
              (stepN w d (entry, localStep.2)).isSome := by
            intro d hd
            obtain ⟨k, hk, hkd⟩ := List.mem_map.mp hd
            have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
            have hkPos : 0 < k :=
              of_decide_eq_true (List.mem_filter.mp hk).2
            have hkEq : k = 1 + (k - 1) := by omega
            have hkLive := hlive k hkTimes
            rw [hkEq, stepN_add, honeStep] at hkLive
            have hlocal :
                (stepN w (k - 1) (entry, localStep.2)).isSome := by
              simpa using hkLive
            simpa [hkd] using hlocal
          have hpositiveLength : positive.length = shifted.length := by
            simp [shifted]
          have hzeroBound : zeroTimes.length <= 1 := by
            dsimp [zeroTimes]
            exact boundary_zero_filter_length_le_one htimesNodup
          have hpartition : zeroTimes.length + positive.length =
              times.length := by
            simpa [zeroTimes, positive] using
              boundary_zero_positive_partition times
          by_cases hzero : 0 ∈ times
          · have hzeroMem : 0 ∈ zeroTimes := by
              dsimp [zeroTimes]
              exact List.mem_filter.mpr ⟨hzero, decide_eq_true rfl⟩
            have hzeroLengthNe : zeroTimes.length ≠ 0 := by
              intro hlen
              cases hz : zeroTimes with
              | nil => rw [hz] at hzeroMem; cases hzeroMem
              | cons z rest => simp [hz] at hlen
            have hzeroLength : zeroTimes.length = 1 := by omega
            have hzeroVector :
                restrictedTonguesAt w N (startPort, startState) 0 =
                  VectorCount.restrict N startState := by
              simp [restrictedTonguesAt, tonguesAt, stepN]
            have haugmentedNodup :
                (VectorCount.restrict N startState ::
                  shifted.map (restrictedTonguesAt w N
                    (entry, localStep.2))).Nodup := by
              rw [List.nodup_cons]
              constructor
              · intro hm
                rw [hshiftVector] at hm
                obtain ⟨k, hk, heq⟩ := List.mem_map.mp hm
                have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
                have heq' : restrictedTonguesAt w N
                    (startPort, startState) 0 =
                    restrictedTonguesAt w N
                      (startPort, startState) k :=
                  hzeroVector.trans heq.symm
                have htimeEq := boundary_nodup_map_eq_of_mem
                  (restrictedTonguesAt w N (startPort, startState))
                  hnd hzero hkTimes heq'
                have hkPos : 0 < k :=
                  of_decide_eq_true (List.mem_filter.mp hk).2
                omega
              · exact hshiftedNodup
            by_cases hsame : localStep.2 = startState
            · let augmented := 0 :: shifted
              have haugmentedLive : forall d, d ∈ augmented ->
                  (stepN w d (entry, localStep.2)).isSome := by
                intro d hd
                rcases List.mem_cons.mp hd with rfl | hd
                · simp [stepN]
                · exact hshiftedLive d hd
              have hlocalZero : restrictedTonguesAt w N
                    (entry, localStep.2) 0 =
                  VectorCount.restrict N startState := by
                simp [restrictedTonguesAt, tonguesAt, stepN, hsame]
              have haugmentedLocalNodup :
                  (augmented.map (restrictedTonguesAt w N
                    (entry, localStep.2))).Nodup := by
                dsimp [augmented]
                rw [hlocalZero]
                exact haugmentedNodup
              have hbound := known_edge_all_run_distinct_le_N_add_six hN hlink
                augmented haugmentedLive haugmentedLocalNodup
              have hlength : augmented.length = shifted.length + 1 := by
                simp [augmented]
              omega
            · let k0 := startPort / 3
              have harrive : arrive startState startPort =
                  (localStep.1, localStep.2) := by simp [localStep]
              have hchanged : localStep.2 k0 ≠ startState k0 := by
                intro heq
                apply hsame
                funext j
                by_cases hj : j = k0
                · subst j
                  exact heq
                · exact arrive_preserves_other harrive hj
              have htrailing := changed_arrival_is_trailing
                harrive hchanged
              have he : localStep.1 = 3 * k0 := htrailing.2.1
              have hk0 : k0 < N := by
                have hp := (hN localStep.1 entry hlink).1
                dsimp [k0] at he
                omega
              have hbaseShift : localStep.2 =
                  flipAt startState k0 :=
                changed_arrival_eq_flipAt harrive hchanged
              have hbound := hproductive hlink he hk0 hbaseShift
                shifted hshiftedLive haugmentedNodup
              omega
          · have hzeroLength : zeroTimes.length = 0 := by
              cases hz : zeroTimes with
              | nil => simp
              | cons z rest =>
                  have hzmem : z ∈ zeroTimes := by
                    rw [hz]
                    exact List.mem_cons_self
                  have hzdata := List.mem_filter.mp hzmem
                  have hz0 : z = 0 := of_decide_eq_true hzdata.2
                  subst z
                  exact (hzero hzdata.1).elim
            have hbound := known_edge_all_run_distinct_le_N_add_six hN hlink
              shifted hshiftedLive hshiftedNodup
            omega

/-- The exact raw `StateLaw` follows from the one explicit productive
boundary obligation.  There is no long-run, reachability, or fixed-`N`
hypothesis hidden in this wrapper. -/
theorem stateLaw_of_productive_initial_boundary
    (hboundary : forall (w : Wiring) (N : Nat),
      (forall p q, w.link p = some q ->
        p < 3 * N ∧ q < 3 * N) ->
      ProductiveInitialBoundaryCap w N) : StateLaw := by
  intro w N hN start times hlive hnd
  exact arbitrary_start_distinct_le_N_add_six_of_productive_boundary
    hN (hboundary w N hN) start times hlive hnd

/-- Final residual formulation in the language of the raw state law.  To
finish `StateLaw`, it is now enough to rule out the single explicit type
`ProductiveInitialBoundaryHistorySaturation`.  That type already includes the
actual productive first passage, an `N+6`-state known-edge tail, and the
`N+2` first-journey boundary history containing the pre-passage vector. -/
theorem stateLaw_of_no_productive_boundary_history_saturation
    (hno : forall (w : Wiring) (N : Nat),
      (forall p q, w.link p = some q ->
        p < 3 * N ∧ q < 3 * N) ->
      ProductiveInitialBoundaryHistorySaturation w N -> False) :
    StateLaw := by
  apply stateLaw_of_productive_initial_boundary
  intro w N hN
  exact productiveInitialBoundaryCap_of_no_history_saturation
    hN (hno w N hN)

end GeneralN
