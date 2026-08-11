import TrackCurveShrinkGlobal
import MellitDirectStateBound

/-!
# The all-empty-curves potential

For a fixed tongue vector, the external track matching together with the
selected stem--branch edge at every switch decomposes the finite track into
curves.  One curve contains the train; every other curve is empty.

The earlier Koizumi development tracked one chosen empty curve and proved
that repeated replacement by a strict subarc terminates.  That is not yet a
coefficient-one argument: naively restarting the same estimate on nested
curves can pay `N` repeatedly.

This file records *all* state-curves simultaneously.  Their switch carriers
form one partition of `0, ..., N-1`, and their unmatched endpoints form a
second partition into blocks of size at most two.  The total empty-curve mass
drops at a non-self pivot, because exactly one empty component is replaced by
a strict subarc.

It does **not** drop at a self-contact: that surgery may put a remnant of the
old train curve into the empty family.  The file proves this obstruction
formally.  Its unconditional raw measure is therefore the set of reachable
stems on the train curve.  Every non-self productive pivot strictly grows
that set, every self-contact can only shrink it, and a non-self-only epoch has
at most `N` productive pivots.  No conditional state-law theorem is exported.
-/

namespace GeneralN

/-! ## Finite state-curves and their two simultaneous partitions -/

/-- One component of the selected curve graph.

`switches` records the switches whose selected internal stem--branch edge is
in the component.  `endpoints` records the switches whose unmatched branch
is an endpoint of the component.  `root` is a concrete port used by the raw
representation predicate below. -/
structure OpenStateCurve where
  root : Nat
  switches : List Nat
  endpoints : List Nat

/-- Concatenate the switch carriers of a finite curve family. -/
def curveSwitchCarrier : List OpenStateCurve -> List Nat
  | [] => []
  | D :: rest => D.switches ++ curveSwitchCarrier rest

/-- Concatenate the unmatched-endpoint carriers of a finite curve family. -/
def curveEndpointCarrier : List OpenStateCurve -> List Nat
  | [] => []
  | D :: rest => D.endpoints ++ curveEndpointCarrier rest

/-- Total selected-edge mass of a finite curve family. -/
def curveSwitchMass : List OpenStateCurve -> Nat
  | [] => 0
  | D :: rest => D.switches.length + curveSwitchMass rest

@[simp] theorem curveSwitchCarrier_append
    (xs ys : List OpenStateCurve) :
    curveSwitchCarrier (xs ++ ys) =
      curveSwitchCarrier xs ++ curveSwitchCarrier ys := by
  induction xs with
  | nil => simp [curveSwitchCarrier]
  | cons D rest ih => simp [curveSwitchCarrier, ih, List.append_assoc]

@[simp] theorem curveEndpointCarrier_append
    (xs ys : List OpenStateCurve) :
    curveEndpointCarrier (xs ++ ys) =
      curveEndpointCarrier xs ++ curveEndpointCarrier ys := by
  induction xs with
  | nil => simp [curveEndpointCarrier]
  | cons D rest ih => simp [curveEndpointCarrier, ih, List.append_assoc]

@[simp] theorem curveSwitchMass_append
    (xs ys : List OpenStateCurve) :
    curveSwitchMass (xs ++ ys) =
      curveSwitchMass xs + curveSwitchMass ys := by
  induction xs with
  | nil => simp [curveSwitchMass]
  | cons D rest ih => simp [curveSwitchMass, ih, Nat.add_assoc]

theorem curveSwitchMass_eq_carrier_length
    (curves : List OpenStateCurve) :
    curveSwitchMass curves = (curveSwitchCarrier curves).length := by
  induction curves with
  | nil => rfl
  | cons D rest ih =>
      simp [curveSwitchMass, curveSwitchCarrier, ih]

/-- A complete selected-curve decomposition for `N` switches.

The train curve is distinguished.  Every selected internal edge belongs to
exactly one curve (`switches_*`), and every unmatched branch belongs to
exactly one curve (`endpoints_*`).  A component has at most two unmatched
endpoints, exactly as proved for the raw curve graph by
`finiteCurveEndpointWriters_length_le_two`.

The completeness fields are useful for checking that this is a genuine
partition rather than merely a disjoint collection. -/
structure OpenCurvePartition (N : Nat) where
  train : OpenStateCurve
  empty : List OpenStateCurve
  switches_nodup :
    (train.switches ++ curveSwitchCarrier empty).Nodup
  switches_inRange :
    forall C, C ∈ train.switches ++ curveSwitchCarrier empty -> C < N
  switches_complete :
    forall C, C < N -> C ∈ train.switches ++ curveSwitchCarrier empty
  endpoints_nodup :
    (train.endpoints ++ curveEndpointCarrier empty).Nodup
  endpoints_inRange :
    forall C, C ∈ train.endpoints ++ curveEndpointCarrier empty -> C < N
  endpoints_complete :
    forall C, C < N -> C ∈ train.endpoints ++ curveEndpointCarrier empty
  train_endpoints_le_two : train.endpoints.length <= 2
  empty_endpoints_le_two :
    forall D, D ∈ empty -> D.endpoints.length <= 2

/-- The one global reservoir: selected-edge mass on every curve not
containing the train. -/
def OpenCurvePartition.emptyPotential
    {N : Nat} (S : OpenCurvePartition N) : Nat :=
  curveSwitchMass S.empty

private theorem nodup_subset_length_emptyCurve
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall {xs ys : List alpha},
      xs.Nodup -> (forall x, x ∈ xs -> x ∈ ys) -> xs.length <= ys.length := by
  intro xs
  induction xs with
  | nil => intro ys _ _; exact Nat.zero_le _
  | cons x rest ih =>
      intro ys hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hrest : forall y, y ∈ rest -> y ∈ ys.erase x := by
        intro y hy
        have hy' : y ∈ ys := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hEq => hnd.1 (hEq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hy'
      have hle := ih hnd.2 hrest
      rw [List.length_erase_of_mem hx] at hle
      have hpositive : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-! ## An unconditional coefficient-one raw measure -/

/-- The represented switches whose stems lie on the selected curve rooted at
`root`.  Unlike `finiteCurvePorts`, this counts each switch at most once. -/
noncomputable def finiteCurveStems
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) : List Nat := by
  classical
  exact (List.range N).filter
    (fun C => decide (CurveReach w u root (3 * C)))

theorem mem_finiteCurveStems_iff
    {w : Wiring} {N : Nat} {u : Tongues} {root C : Nat} :
    C ∈ finiteCurveStems w N u root <->
      C < N ∧ CurveReach w u root (3 * C) := by
  classical
  simp [finiteCurveStems]

private theorem nodup_filter_emptyCurve (pred : Nat -> Bool) :
    forall {xs : List Nat}, xs.Nodup -> (xs.filter pred).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : pred x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hmem => hnd.1 ((List.mem_filter.mp hmem).1),
            ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

theorem finiteCurveStems_nodup
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) :
    (finiteCurveStems w N u root).Nodup := by
  classical
  unfold finiteCurveStems
  exact nodup_filter_emptyCurve _ List.nodup_range

theorem finiteCurveStems_length_le
    (w : Wiring) (N : Nat) (u : Tongues) (root : Nat) :
    (finiteCurveStems w N u root).length <= N := by
  classical
  unfold finiteCurveStems
  simpa using List.length_filter_le
    (fun C => decide (CurveReach w u root (3 * C))) (List.range N)

private theorem length_lt_of_strict_subset_emptyCurve
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {small big : List alpha}
    (hnd : small.Nodup)
    (hsub : forall x, x ∈ small -> x ∈ big)
    (fresh : alpha) (hfresh : fresh ∈ big) (hnot : fresh ∉ small) :
    small.length < big.length := by
  have hcons : (fresh :: small).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hnot, hnd⟩
  have hconsSub : forall x, x ∈ fresh :: small -> x ∈ big := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hfresh
    · exact hsub x hx
  have hle := nodup_subset_length_emptyCurve hcons hconsSub
  simp only [List.length_cons] at hle
  omega

/-- **Strict reachable-stem growth at a non-self productive pivot.**

The old train curve embeds in the new one and the pivot stem `C` is a new
member.  Counting stems rather than all three physical ports improves the
local capacity from `3*N` to `N`. -/
theorem nonself_endpoint_pivot_finiteCurveStems_growth
    {w : Wiring} {N C : Nat} {cur next : Nat × Tongues}
    (hC : C < N)
    (hstep : step w cur = some next)
    (hentry : cur.1 = unmatchedBranch cur.2 C)
    (hexit : exitPort cur = 3 * C)
    (hflip : next.2 = flipAt cur.2 C)
    (houtside : ¬ CurveReach w cur.2 cur.1 (3 * C)) :
    (finiteCurveStems w N cur.2 cur.1).length <
      (finiteCurveStems w N next.2 next.1).length := by
  have hgrowth := unmatched_pivot_strict_curve_growth cur.2 C (by
    simpa [hentry] using houtside)
  have hlink : w.link (3 * C) = some next.1 := by
    have hp := (step_some_parts hstep).1
    simpa [hexit] using hp
  have hrootStem : CurveReach w next.2 cur.1 (3 * C) := by
    simpa [hentry, hflip] using hgrowth.2.1
  have hrootNext : CurveReach w next.2 cur.1 next.1 :=
    CurveReach.step hrootStem (Or.inl hlink)
  have hnextRoot : CurveReach w next.2 next.1 cur.1 :=
    curveReach_symm hrootNext
  have hlift : forall D, CurveReach w cur.2 cur.1 (3 * D) ->
      CurveReach w next.2 next.1 (3 * D) := by
    intro D hD
    have hD' : CurveReach w next.2 cur.1 (3 * D) := by
      simpa [hentry, hflip] using hgrowth.1 (3 * D) (by
        simpa [hentry] using hD)
    exact curveReach_trans hnextRoot hD'
  have hsubset : forall D,
      D ∈ finiteCurveStems w N cur.2 cur.1 ->
      D ∈ finiteCurveStems w N next.2 next.1 := by
    intro D hD
    rw [mem_finiteCurveStems_iff] at hD ⊢
    exact ⟨hD.1, hlift D hD.2⟩
  have hCNew : C ∈ finiteCurveStems w N next.2 next.1 := by
    rw [mem_finiteCurveStems_iff]
    exact ⟨hC, curveReach_trans hnextRoot hrootStem⟩
  have hCOld : C ∉ finiteCurveStems w N cur.2 cur.1 := by
    intro hm
    exact houtside (mem_finiteCurveStems_iff.mp hm).2
  exact length_lt_of_strict_subset_emptyCurve
    (finiteCurveStems_nodup w N cur.2 cur.1)
    hsubset C hCNew hCOld

/-- At a self pivot the next reachable-stem carrier is contained in the
previous one. -/
theorem self_endpoint_pivot_finiteCurveStems_nonincrease
    {w : Wiring} {N C : Nat} {cur next : Nat × Tongues}
    (hstep : step w cur = some next)
    (hentry : cur.1 = unmatchedBranch cur.2 C)
    (hexit : exitPort cur = 3 * C)
    (hflip : next.2 = flipAt cur.2 C)
    (hself : CurveReach w cur.2 cur.1 (3 * C)) :
    (finiteCurveStems w N next.2 next.1).length <=
      (finiteCurveStems w N cur.2 cur.1).length := by
  have hlift := self_endpoint_pivot_curveReach_subset
    hstep hentry hexit hflip hself
  have hsubset : forall D,
      D ∈ finiteCurveStems w N next.2 next.1 ->
      D ∈ finiteCurveStems w N cur.2 cur.1 := by
    intro D hD
    rw [mem_finiteCurveStems_iff] at hD ⊢
    exact ⟨hD.1, hlift (3 * D) hD.2⟩
  exact nodup_subset_length_emptyCurve
    (finiteCurveStems_nodup w N next.2 next.1) hsubset

/-- Reachable-stem size at raw time `k`. -/
noncomputable def rawFiniteCurveStemSizeAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Nat :=
  let cur := (stepN w k start).getD start
  (finiteCurveStems w N cur.2 cur.1).length

theorem rawProductiveAt_nonself_stem_growth
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q -> p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hnonself : ¬ RawCurveSelfAt w start k) :
    rawFiniteCurveStemSizeAt w N start k <
      rawFiniteCurveStemSizeAt w N start (k + 1) := by
  obtain ⟨cur, next, C, hCwriter, hcur, hnext, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hC : C < N := by
    rw [hCwriter]
    exact rawProductiveAt_writer_lt hN hprod
  have hCcur : C = cur.1 / 3 := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hCwriter
  have houtside : ¬ CurveReach w cur.2 cur.1 (3 * C) := by
    unfold RawCurveSelfAt at hnonself
    simpa [hcur, hCcur] using hnonself
  have hgrowth := nonself_endpoint_pivot_finiteCurveStems_growth
    hC hstep hentry hexit hflip houtside
  simpa [rawFiniteCurveStemSizeAt, hcur, hnext] using hgrowth

theorem rawProductiveAt_self_stem_nonincrease
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q -> p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k)
    (hself : RawCurveSelfAt w start k) :
    rawFiniteCurveStemSizeAt w N start (k + 1) <=
      rawFiniteCurveStemSizeAt w N start k := by
  obtain ⟨cur, next, C, hCwriter, hcur, hnext, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hCcur : C = cur.1 / 3 := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hCwriter
  have hself' : CurveReach w cur.2 cur.1 (3 * C) := by
    unfold RawCurveSelfAt at hself
    simpa [hcur, hCcur] using hself
  have hle := self_endpoint_pivot_finiteCurveStems_nonincrease
    (N := N) hstep hentry hexit hflip hself'
  simpa [rawFiniteCurveStemSizeAt, hcur, hnext] using hle

/-- **Raw productive-step dichotomy.** Every productive lazy-point entry is
either a strict reachable-stem push at a non-self contact, or a self-contact
whose reachable-stem carrier does not grow.  This is unconditional and stated
directly over `Wiring`/`stepN`. -/
theorem rawProductiveAt_stem_growth_or_self_contact
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q -> p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hprod : RawProductiveAt w N start k) :
    (¬ RawCurveSelfAt w start k ∧
      rawFiniteCurveStemSizeAt w N start k <
        rawFiniteCurveStemSizeAt w N start (k + 1)) ∨
    (RawCurveSelfAt w start k ∧
      rawFiniteCurveStemSizeAt w N start (k + 1) <=
        rawFiniteCurveStemSizeAt w N start k) := by
  by_cases hself : RawCurveSelfAt w start k
  · exact Or.inr ⟨hself,
      rawProductiveAt_self_stem_nonincrease hN hprod hself⟩
  · exact Or.inl ⟨hself,
      rawProductiveAt_nonself_stem_growth hN hprod hself⟩

theorem rawNonproductiveAt_stem_size_eq
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q -> p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    (hlive : (stepN w (k + 1) start).isSome)
    (hnot : ¬ RawProductiveAt w N start k) :
    rawFiniteCurveStemSizeAt w N start (k + 1) =
      rawFiniteCurveStemSizeAt w N start k := by
  obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
    live_successor_configs hlive
  have hstate := rawNonproductiveAt_tongues_eq
    hN hcur hnext hstep hnot
  have hparts := step_some_parts hstep
  have hinternal : InternalCurveEdge cur.2 cur.1 (exitPort cur) := by
    unfold InternalCurveEdge
    apply Prod.ext
    · rfl
    · change arrivedTongues cur = cur.2
      rw [← hparts.2, hstate]
  have hcurNext : CurveReach w cur.2 cur.1 next.1 :=
    CurveReach.step
      (curveReach_edge (Or.inr hinternal))
      (Or.inl hparts.1)
  have hnextCur : CurveReach w cur.2 next.1 cur.1 :=
    curveReach_symm hcurNext
  have hforward : forall D,
      D ∈ finiteCurveStems w N cur.2 cur.1 ->
      D ∈ finiteCurveStems w N next.2 next.1 := by
    intro D hD
    rw [mem_finiteCurveStems_iff] at hD ⊢
    rw [hstate]
    exact ⟨hD.1, curveReach_trans hnextCur hD.2⟩
  have hbackward : forall D,
      D ∈ finiteCurveStems w N next.2 next.1 ->
      D ∈ finiteCurveStems w N cur.2 cur.1 := by
    intro D hD
    rw [mem_finiteCurveStems_iff] at hD ⊢
    rw [hstate] at hD
    exact ⟨hD.1, curveReach_trans hcurNext hD.2⟩
  have hleForward := nodup_subset_length_emptyCurve
    (finiteCurveStems_nodup w N cur.2 cur.1) hforward
  have hleBackward := nodup_subset_length_emptyCurve
    (finiteCurveStems_nodup w N next.2 next.1) hbackward
  unfold rawFiniteCurveStemSizeAt
  simp only [hcur, hnext, Option.getD_some]
  omega

private theorem ec_productiveTimes_length_succ_of_productive
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat)
    (hprod : RawProductiveAt w N start K) :
    (rawProductiveCurveTimes w N start (K + 1)).length =
      (rawProductiveCurveTimes w N start K).length + 1 := by
  classical
  simp [rawProductiveCurveTimes, List.range_succ, hprod]

private theorem ec_productiveTimes_length_succ_of_nonproductive
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat)
    (hnot : ¬ RawProductiveAt w N start K) :
    (rawProductiveCurveTimes w N start (K + 1)).length =
      (rawProductiveCurveTimes w N start K).length := by
  classical
  simp [rawProductiveCurveTimes, List.range_succ, hnot]

/-- **Unconditional coefficient-one epoch theorem.** In any live raw prefix
whose productive pivots are all non-self, there are at most `N` productive
pivots.  Nonproductive moves merely reroot the same selected curve. -/
theorem nonself_productive_times_le_N
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q -> p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : forall k, k <= K -> (stepN w k start).isSome)
    (hnonself : forall k, k < K -> RawProductiveAt w N start k ->
      ¬ RawCurveSelfAt w start k) :
    (rawProductiveCurveTimes w N start K).length <= N := by
  let sizeAt := rawFiniteCurveStemSizeAt w N start
  let countAt := fun k => (rawProductiveCurveTimes w N start k).length
  have hacc : forall j, j <= K ->
      sizeAt 0 + countAt j <= sizeAt j := by
    intro j hj
    induction j with
    | zero => simp [countAt, rawProductiveCurveTimes]
    | succ j ih =>
        have hjK : j < K := by omega
        have hprev := ih (by omega)
        by_cases hprod : RawProductiveAt w N start j
        · have hgrow : sizeAt j < sizeAt (j + 1) :=
            rawProductiveAt_nonself_stem_growth hN hprod
              (hnonself j hjK hprod)
          have hcount := ec_productiveTimes_length_succ_of_productive
            w N start j hprod
          change sizeAt 0 +
            (rawProductiveCurveTimes w N start j).length <= sizeAt j at hprev
          change sizeAt 0 +
            (rawProductiveCurveTimes w N start (j + 1)).length <= sizeAt (j + 1)
          rw [hcount]
          omega
        · have heq : sizeAt (j + 1) = sizeAt j :=
            rawNonproductiveAt_stem_size_eq hN
              (hlive (j + 1) (by omega)) hprod
          have hcount := ec_productiveTimes_length_succ_of_nonproductive
            w N start j hprod
          change sizeAt 0 +
            (rawProductiveCurveTimes w N start j).length <= sizeAt j at hprev
          change sizeAt 0 +
            (rawProductiveCurveTimes w N start (j + 1)).length <= sizeAt (j + 1)
          rw [hcount, heq]
          exact hprev
  have hfinal := hacc K (Nat.le_refl _)
  have hcap : sizeAt K <= N := by
    unfold sizeAt rawFiniteCurveStemSizeAt
    exact finiteCurveStems_length_le w N
      ((stepN w K start).getD start).2
      ((stepN w K start).getD start).1
  change sizeAt 0 +
    (rawProductiveCurveTimes w N start K).length <= sizeAt K at hfinal
  omega

/-- If a live prefix contains more than `N` productive entries, one of them
is necessarily a concrete raw self-contact. -/
theorem more_than_N_productive_forces_self_contact
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q -> p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : forall k, k <= K -> (stepN w k start).isSome)
    (hmore : N < (rawProductiveCurveTimes w N start K).length) :
    exists k, k < K ∧ RawProductiveAt w N start k ∧
      RawCurveSelfAt w start k := by
  apply Classical.byContradiction
  intro hnone
  have hnonself : forall k, k < K -> RawProductiveAt w N start k ->
      ¬ RawCurveSelfAt w start k := by
    intro k hk hprod hself
    exact hnone ⟨k, hk, hprod, hself⟩
  have hle := nonself_productive_times_le_N
    hN start K hlive hnonself
  omega

/-! ## First-contact single-truncation accounting -/

/-- The old support and the fresh second-journey prefix, stopped immediately
before their first support contact.  First-contact minimality says their
writer union is duplicate-free. -/
structure FirstSupportContactWindow (N : Nat) : Type where
  oldSupport : List Nat
  freshPrefix : List Nat
  union_nodup : (oldSupport ++ freshPrefix).Nodup
  union_inRange : forall C, C ∈ oldSupport ++ freshPrefix -> C < N

/-- The old support and fresh prefix consume one common `N`-writer budget,
not two separately restarted budgets. -/
theorem FirstSupportContactWindow.union_length_le
    {N : Nat} (W : FirstSupportContactWindow N) :
    W.oldSupport.length + W.freshPrefix.length <= N := by
  have hle := nodup_nat_lt_length W.union_nodup W.union_inRange
  simpa only [List.length_append] using hle

/-- The canonical union-first-repeat prefix supplies exactly the disjoint
writer window needed by single-truncation accounting. -/
def UnionFirstRepeat.toFirstSupportContactWindow
    {N : Nat} {old fresh : List Passage}
    (R : UnionFirstRepeat old fresh)
    (hOld : forall passage, passage ∈ old -> passageSwitch passage < N)
    (hFresh : forall passage, passage ∈ R.before ->
      passageSwitch passage < N) :
    FirstSupportContactWindow N := {
  oldSupport := old.map passageSwitch
  freshPrefix := R.before.map passageSwitch
  union_nodup := by
    have hsimple := R.combinedSimple
    unfold SwitchSimple at hsimple
    simpa only [List.map_append] using hsimple
  union_inRange := by
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨passage, hp, rfl⟩ := List.mem_map.mp hC
      exact hOld passage hp
    · obtain ⟨passage, hp, rfl⟩ := List.mem_map.mp hC
      exact hFresh passage hp
}

/-- **Single-truncation coefficient-one count.**

Suppose the pre-contact vectors cost at most one initial vector plus the old
support and the fresh prefix, and the post-contact classification contributes
at most three genuinely fresh tail vectors (the tail base is historical).
Then the whole duplicate-free sample has at most `N+4` vectors. -/
theorem firstSupportContact_singleTruncation_le_n_add_four
    {N : Nat} {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (W : FirstSupportContactWindow N)
    (prefixVectors freshTail samples : List alpha)
    (hprefix : prefixVectors.length <=
      W.oldSupport.length + W.freshPrefix.length + 1)
    (htail : freshTail.length <= 3)
    (hnd : samples.Nodup)
    (hcover : forall x, x ∈ samples ->
      x ∈ prefixVectors ++ freshTail) :
    samples.length <= N + 4 := by
  have hsample := nodup_subset_length_emptyCurve hnd hcover
  have hunion := W.union_length_le
  simp only [List.length_append] at hsample
  omega

/-- The switch carrier of all empty curves is duplicate-free. -/
theorem OpenCurvePartition.empty_switches_nodup
    {N : Nat} (S : OpenCurvePartition N) :
    (curveSwitchCarrier S.empty).Nodup := by
  exact (List.nodup_append.mp S.switches_nodup).2.1

/-- Every switch charged by the empty potential is represented. -/
theorem OpenCurvePartition.empty_switches_inRange
    {N : Nat} (S : OpenCurvePartition N) :
    forall C, C ∈ curveSwitchCarrier S.empty -> C < N := by
  intro C hC
  exact S.switches_inRange C (List.mem_append_right _ hC)

/-- The complete switch partition has exactly `N` entries. -/
theorem OpenCurvePartition.total_switch_mass
    {N : Nat} (S : OpenCurvePartition N) :
    S.train.switches.length + S.emptyPotential = N := by
  let carrier := S.train.switches ++ curveSwitchCarrier S.empty
  have hupper : carrier.length <= N := by
    apply nodup_nat_lt_length S.switches_nodup
    exact S.switches_inRange
  have hsub : forall C, C ∈ List.range N -> C ∈ carrier := by
    intro C hC
    exact S.switches_complete C (List.mem_range.mp hC)
  have hlower : (List.range N).length <= carrier.length :=
    nodup_subset_length_emptyCurve List.nodup_range hsub
  have hmass := curveSwitchMass_eq_carrier_length S.empty
  unfold OpenCurvePartition.emptyPotential
  dsimp [carrier] at hupper hlower
  simp only [List.length_append, List.length_range] at hupper hlower
  rw [hmass]
  omega

/-- In particular, the all-empty-curves potential is bounded once, globally,
by the number of switches. -/
theorem OpenCurvePartition.emptyPotential_le
    {N : Nat} (S : OpenCurvePartition N) :
    S.emptyPotential <= N := by
  have htotal := S.total_switch_mass
  omega

/-! ## Exact one-curve surgery and global descent -/

/-- A strict subarc carries only switches from the old curve and is strictly
shorter.  Endpoint data may change during the surgery. -/
def StrictEmptySubarc (new old : OpenStateCurve) : Prop :=
  (forall C, C ∈ new.switches -> C ∈ old.switches) ∧
    new.switches.length < old.switches.length

/-- One unresolved state-changing entry changes exactly one empty curve into
a strict subarc.  Every other empty curve is literally preserved.  The train
curve is allowed to absorb the complementary carrier; completeness of the
two partitions prevents carrier loss or duplication. -/
structure EmptyCurveUpdate {N : Nat}
    (S T : OpenCurvePartition N) : Type where
  before : List OpenStateCurve
  oldCurve : OpenStateCurve
  newCurve : OpenStateCurve
  after : List OpenStateCurve
  source : S.empty = before ++ oldCurve :: after
  target : T.empty = before ++ newCurve :: after
  strict : StrictEmptySubarc newCurve oldCurve

/-- The global potential drops strictly at one exact empty-curve update. -/
theorem EmptyCurveUpdate.potential_lt
    {N : Nat} {S T : OpenCurvePartition N}
    (U : EmptyCurveUpdate S T) :
    T.emptyPotential < S.emptyPotential := by
  unfold OpenCurvePartition.emptyPotential
  rw [U.source, U.target]
  simp only [curveSwitchMass_append, curveSwitchMass]
  exact Nat.add_lt_add_left
    (Nat.add_lt_add_right U.strict.2 (curveSwitchMass U.after))
    (curveSwitchMass U.before)

/-- Because total switch mass is conserved, every empty-potential drop is
exactly paid for by growth of the marked train curve. -/
theorem EmptyCurveUpdate.train_mass_lt
    {N : Nat} {S T : OpenCurvePartition N}
    (U : EmptyCurveUpdate S T) :
    S.train.switches.length < T.train.switches.length := by
  have hS := S.total_switch_mass
  have hT := T.total_switch_mass
  have hdrop := U.potential_lt
  omega

/-- Empty switch carriers are monotone: an update may delete switches from
one empty curve but can never put a new support writer into the empty
reservoir. -/
theorem EmptyCurveUpdate.empty_carrier_subset
    {N : Nat} {S T : OpenCurvePartition N}
    (U : EmptyCurveUpdate S T) :
    forall C, C ∈ curveSwitchCarrier T.empty ->
      C ∈ curveSwitchCarrier S.empty := by
  intro C hC
  rw [U.target, curveSwitchCarrier_append] at hC
  rw [U.source, curveSwitchCarrier_append]
  simp only [curveSwitchCarrier] at hC ⊢
  rcases List.mem_append.mp hC with hbefore | hrest
  · exact List.mem_append_left _ hbefore
  · rcases List.mem_append.mp hrest with hnew | hafter
    · apply List.mem_append_right
      apply List.mem_append_left
      exact U.strict.1 C hnew
    · apply List.mem_append_right
      exact List.mem_append_right _ hafter

/-- A concrete support writer consumed by one global empty-curve update. -/
structure SupportWriterCharge
    {N : Nat} {S T : OpenCurvePartition N}
    (U : EmptyCurveUpdate S T) : Type where
  writer : Nat
  source_empty : writer ∈ curveSwitchCarrier S.empty
  target_train : writer ∈ T.train.switches
  target_empty_not : writer ∉ curveSwitchCarrier T.empty

/-- Every strict empty-curve update consumes at least one actual support
writer.  The writer was in the old empty reservoir and, by exact partition
conservation, is in the marked train curve afterwards. -/
theorem EmptyCurveUpdate.has_supportWriterCharge
    {N : Nat} {S T : OpenCurvePartition N}
    (U : EmptyCurveUpdate S T) :
    Nonempty (SupportWriterCharge U) := by
  have hndSource := S.empty_switches_nodup
  rw [U.source, curveSwitchCarrier_append] at hndSource
  simp only [curveSwitchCarrier] at hndSource
  have htailNodup := (List.nodup_append.mp hndSource).2.1
  have holdNodup := (List.nodup_append.mp htailNodup).1
  have hexists : exists C,
      C ∈ U.oldCurve.switches ∧ C ∉ U.newCurve.switches := by
    apply Classical.byContradiction
    intro hnone
    have hsubset : forall C, C ∈ U.oldCurve.switches ->
        C ∈ U.newCurve.switches := by
      intro C hC
      by_cases hnew : C ∈ U.newCurve.switches
      · exact hnew
      · exact (hnone ⟨C, hC, hnew⟩).elim
    have hle := nodup_subset_length_emptyCurve holdNodup hsubset
    have hlt := U.strict.2
    omega
  obtain ⟨C, hold, hnew⟩ := hexists
  have hbeforeNot : C ∉ curveSwitchCarrier U.before := by
    intro hbefore
    have hcross := (List.nodup_append.mp hndSource).2.2
      C hbefore C (List.mem_append_left _ hold)
    exact hcross rfl
  have hafterNot : C ∉ curveSwitchCarrier U.after := by
    intro hafter
    have hcross := (List.nodup_append.mp htailNodup).2.2
      C hold C hafter
    exact hcross rfl
  have hsource : C ∈ curveSwitchCarrier S.empty := by
    rw [U.source, curveSwitchCarrier_append]
    simp only [curveSwitchCarrier]
    exact List.mem_append_right _ (List.mem_append_left _ hold)
  have htargetNot : C ∉ curveSwitchCarrier T.empty := by
    rw [U.target, curveSwitchCarrier_append]
    simp only [curveSwitchCarrier]
    intro hmem
    rcases List.mem_append.mp hmem with hbefore | hrest
    · exact hbeforeNot hbefore
    · rcases List.mem_append.mp hrest with hnew' | hafter
      · exact hnew hnew'
      · exact hafterNot hafter
  have hC_lt : C < N := S.empty_switches_inRange C hsource
  have htotal := T.switches_complete C hC_lt
  have htrain : C ∈ T.train.switches := by
    rcases List.mem_append.mp htotal with htrain | hempty
    · exact htrain
    · exact (htargetNot hempty).elim
  exact ⟨{
    writer := C
    source_empty := hsource
    target_train := htrain
    target_empty_not := htargetNot
  }⟩

/-- A finite run of unresolved entries, all charged against the same global
family of empty curves. -/
structure EmptyCurvePotentialHistory (N events : Nat) : Type where
  state : Nat -> OpenCurvePartition N
  update : forall k, k < events ->
    EmptyCurveUpdate (state k) (state (k + 1))

/-- Empty support is globally antitone through an arbitrary suffix of the
history. -/
theorem EmptyCurvePotentialHistory.empty_carrier_subset_add
    {N events : Nat} (H : EmptyCurvePotentialHistory N events) :
    forall i d, i + d <= events ->
      forall C, C ∈ curveSwitchCarrier (H.state (i + d)).empty ->
        C ∈ curveSwitchCarrier (H.state i).empty := by
  intro i d hbound
  induction d with
  | zero =>
      intro C hC
      simpa using hC
  | succ d ih =>
      intro C hC
      have hstep := H.update (i + d) (by omega)
      have hCprev :
          C ∈ curveSwitchCarrier (H.state (i + d)).empty := by
        apply hstep.empty_carrier_subset C
        simpa [Nat.add_assoc] using hC
      exact ih (by omega) C hCprev

/-- A history equipped with one support-writer witness for every update. -/
structure ChargedEmptyCurvePotentialHistory (N events : Nat) : Type where
  history : EmptyCurvePotentialHistory N events
  charge : forall k, (hk : k < events) ->
    SupportWriterCharge (history.update k hk)

/-- Every abstract potential history has concrete support-writer charges. -/
theorem EmptyCurvePotentialHistory.exists_charged
    {N events : Nat} (H : EmptyCurvePotentialHistory N events) :
    Nonempty (ChargedEmptyCurvePotentialHistory N events) := by
  classical
  exact ⟨{
    history := H
    charge := fun k hk =>
      Classical.choice ((H.update k hk).has_supportWriterCharge)
  }⟩

/-- **Unique support-writer charge.** A writer charged at one update can
never be charged at a later update: it has left the globally antitone empty
reservoir. -/
theorem ChargedEmptyCurvePotentialHistory.charge_ne_of_lt
    {N events : Nat} (H : ChargedEmptyCurvePotentialHistory N events)
    {i j : Nat} (hij : i < j) (hj : j < events) :
    (H.charge i (Nat.lt_trans hij hj)).writer ≠
      (H.charge j hj).writer := by
  let wi := (H.charge i (Nat.lt_trans hij hj)).writer
  let wj := (H.charge j hj).writer
  intro heq
  change wi = wj at heq
  have hjmem : wj ∈
      curveSwitchCarrier (H.history.state j).empty :=
    (H.charge j hj).source_empty
  have hi1j : i + 1 <= j := by omega
  let d := j - (i + 1)
  have hsum : i + 1 + d = j := by
    dsimp [d]
    omega
  have hfuture := H.history.empty_carrier_subset_add
    (i + 1) d (by omega) wi
  have hjmem' : wi ∈
      curveSwitchCarrier (H.history.state (i + 1 + d)).empty := by
    rw [hsum, heq]
    exact hjmem
  have hiMem := hfuture hjmem'
  exact (H.charge i (Nat.lt_trans hij hj)).target_empty_not hiMem

/-- Telescoping invariant.  This is the key distinction from nested
single-curve recursion: there is one initial potential and no restarted
`N`-sized budget. -/
theorem EmptyCurvePotentialHistory.potential_add_le_initial
    {N events : Nat} (H : EmptyCurvePotentialHistory N events) :
    forall k, k <= events ->
      (H.state k).emptyPotential + k <=
        (H.state 0).emptyPotential := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < events := by omega
      have hprev := ih (by omega)
      have hdrop := (H.update k hklt).potential_lt
      omega

/-- Exact global charge: the number of unresolved updates is at most the
initial empty mass. -/
theorem EmptyCurvePotentialHistory.events_le_initial_potential
    {N events : Nat} (H : EmptyCurvePotentialHistory N events) :
    events <= (H.state 0).emptyPotential := by
  have h := H.potential_add_le_initial events (Nat.le_refl _)
  omega

/-- Coefficient-one corollary, uniform in `N`. -/
theorem EmptyCurvePotentialHistory.events_le_switches
    {N events : Nat} (H : EmptyCurvePotentialHistory N events) :
    events <= N := by
  exact Nat.le_trans H.events_le_initial_potential
    (H.state 0).emptyPotential_le

/-- There is no infinite sequence of exact all-empty-curve updates. -/
theorem no_infinite_emptyCurve_updates
    {N : Nat} (state : Nat -> OpenCurvePartition N)
    (hupdate : forall k, EmptyCurveUpdate (state k) (state (k + 1))) :
    False := by
  let events := (state 0).emptyPotential + 1
  let H : EmptyCurvePotentialHistory N events := {
    state := state
    update := fun k _ => hupdate k
  }
  have h := H.events_le_initial_potential
  change (state 0).emptyPotential + 1 <=
    (state 0).emptyPotential at h
  omega

/-! ## Exact representation by the raw selected curve graph -/

/-- A listed curve is exactly one connected component of the selected raw
curve graph, simultaneously on selected internal edges and unmatched
endpoints. -/
def RepresentsOpenStateCurve
    (w : Wiring) (N : Nat) (u : Tongues)
    (D : OpenStateCurve) : Prop :=
  (forall C, C ∈ D.switches <->
      C < N ∧ CurveReach w u D.root (3 * C)) ∧
  (forall C, C ∈ D.endpoints <->
      C < N ∧ CurveReach w u D.root (unmatchedBranch u C))

/-- The marked component really is the component containing the train, and
every listed empty component has its exact raw carrier. -/
def RepresentsOpenCurvePartition
    (w : Wiring) (N : Nat) (config : Nat × Tongues)
    (S : OpenCurvePartition N) : Prop :=
  S.train.root = config.1 ∧
  RepresentsOpenStateCurve w N config.2 S.train ∧
  (forall D, D ∈ S.empty ->
    RepresentsOpenStateCurve w N config.2 D)

/-- A represented train carrier has exactly the raw reachable-stem size. -/
theorem RepresentsOpenCurvePartition.train_switches_length_eq_stems
    {w : Wiring} {N : Nat} {config : Nat × Tongues}
    {S : OpenCurvePartition N}
    (R : RepresentsOpenCurvePartition w N config S) :
    S.train.switches.length =
      (finiteCurveStems w N config.2 config.1).length := by
  have htrainNodup := (List.nodup_append.mp S.switches_nodup).1
  have hforward : forall C, C ∈ S.train.switches ->
      C ∈ finiteCurveStems w N config.2 config.1 := by
    intro C hC
    have hrepr := (R.2.1.1 C).mp hC
    rw [mem_finiteCurveStems_iff]
    refine ⟨hrepr.1, ?_⟩
    rw [← R.1]
    exact hrepr.2
  have hbackward : forall C,
      C ∈ finiteCurveStems w N config.2 config.1 ->
      C ∈ S.train.switches := by
    intro C hC
    have hraw := mem_finiteCurveStems_iff.mp hC
    apply (R.2.1.1 C).mpr
    refine ⟨hraw.1, ?_⟩
    rw [R.1]
    exact hraw.2
  have hleForward := nodup_subset_length_emptyCurve
    htrainNodup hforward
  have hleBackward := nodup_subset_length_emptyCurve
    (finiteCurveStems_nodup w N config.2 config.1) hbackward
  omega

/-- **Formal obstruction to the unqualified global-potential bridge.**

A raw self-contact cannot be represented by `EmptyCurveUpdate`: the abstract
update forces strict train-carrier growth, whereas exact raw self surgery can
only shrink the reachable-stem carrier.  Thus only non-self pivots may be
charged to the all-empty-curves potential. -/
theorem rawSelfContact_emptyCurveUpdate_false
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q -> p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {k : Nat}
    {S T : OpenCurvePartition N}
    (hprod : RawProductiveAt w N start k)
    (hself : RawCurveSelfAt w start k)
    (Rbefore : RepresentsOpenCurvePartition w N
      ((stepN w k start).getD start) S)
    (Rafter : RepresentsOpenCurvePartition w N
      ((stepN w (k + 1) start).getD start) T)
    (U : EmptyCurveUpdate S T) : False := by
  have hgrow := U.train_mass_lt
  have hraw := rawProductiveAt_self_stem_nonincrease hN hprod hself
  have hbefore := Rbefore.train_switches_length_eq_stems
  have hafter := Rafter.train_switches_length_eq_stems
  unfold rawFiniteCurveStemSizeAt at hraw
  rw [← hbefore, ← hafter] at hraw
  omega

/-- One globally charged **non-self** raw interval.  Quiet motion may reroot
the marked component, but the next novel non-self productive entry transforms
exactly one empty component into a strict subarc. -/
structure RawEmptyCurveShrinkInterval
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (beginTime pivotTime endTime : Nat)
    (S T : OpenCurvePartition N) : Type where
  schedule : beginTime <= pivotTime ∧ endTime = pivotTime + 1
  quiet : forall t, beginTime <= t -> t < pivotTime ->
    ¬ RawProductiveAt w N start t
  productive : RawProductiveAt w N start pivotTime
  nonself : ¬ RawCurveSelfAt w start pivotTime
  begin_live : (stepN w beginTime start).isSome
  end_live : (stepN w endTime start).isSome
  represents_begin : RepresentsOpenCurvePartition w N
    ((stepN w beginTime start).getD start) S
  represents_end : RepresentsOpenCurvePartition w N
    ((stepN w endTime start).getD start) T
  shrink : EmptyCurveUpdate S T

/-!
## Remaining global step

The raw dichotomy and the `N`-bound close all non-self accounting.  What
remains is the stack/replay theorem for self contacts: a self pop must replay
a previous boundary vector or enter the self-only four-snapshot tail.  No
theorem in this module assumes that statement.
-/

end GeneralN
