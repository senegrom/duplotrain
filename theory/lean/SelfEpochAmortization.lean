import TrackCurveShrinkGlobal
import EndpointEpochExtraction
import SelfPivotStrictShrink
import NestedRestorationCharge
import NestedRestorationElimination

/-!
# Global amortization of train-curve growth and self epochs

This file records the unconditional part of the finite-curve amortization
argument directly over `Wiring` and `stepN`.

Every productive non-self pivot strictly enlarges the represented train
curve.  A productive self-pivot can only shrink it, while a nonproductive
step preserves its size.  Summing these one-step facts gives an exact global
potential inequality: the number of non-self productive pivots is bounded by
the final curve size plus the total amount ever discarded by self-pivots.
Since every represented curve has at most `3 * N` ports, this is

`non-self pivots <= 3 * N + total drop mass`.

The second result is the local dichotomy needed for a future global charge.
After any strict self-shrink, every finite live continuation is either a
self-only continuation (and hence exposes at most four tongue vectors), or
contains a later non-self pivot which strictly regrows the carrier.  The
strict shrink also supplies a concrete discarded port.

What is deliberately *not* asserted here is that the discarded ports chosen
at different shrink events are globally distinct.  The nested-restoration
library proves injectivity once the raw events have been compiled into one
strictly nested first-restoration family; constructing that family, or proving
that failure to construct it enters a permanent four-state tail, remains the
global bridge.
-/

namespace GeneralN

/-! ## Event lists and drop mass -/

/-- Productive non-self pivots in the half-open raw prefix `[0, K)`. -/
noncomputable def rawNonselfProductiveTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter (fun k => decide
    (RawProductiveAt w N start k ∧ ¬ RawCurveSelfAt w start k))

theorem mem_rawNonselfProductiveTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawNonselfProductiveTimes w N start K ↔
      k < K ∧ RawProductiveAt w N start k ∧
        ¬ RawCurveSelfAt w start k := by
  classical
  simp [rawNonselfProductiveTimes]

/-- Number of productive non-self pivots strictly before raw time `k`.  This
is the canonical epoch label for the state visible at time `k`. -/
noncomputable def rawNonselfRank
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Nat :=
  (rawNonselfProductiveTimes w N start k).length

/-- The amount by which the represented finite train curve drops at one raw
step.  It is zero on growth and quiet steps. -/
noncomputable def rawCurveDropAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Nat :=
  rawFiniteCurveSizeAt w N start k -
    rawFiniteCurveSizeAt w N start (k + 1)

/-- Total downward variation of the finite train-curve size on `[0, K)`. -/
noncomputable def rawCurveDropMass
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : Nat :=
  ((List.range K).map (rawCurveDropAt w N start)).sum

@[simp] theorem rawCurveDropMass_zero
    (w : Wiring) (N : Nat) (start : Nat × Tongues) :
    rawCurveDropMass w N start 0 = 0 := by
  simp [rawCurveDropMass]

theorem rawCurveDropMass_succ
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    rawCurveDropMass w N start (K + 1) =
      rawCurveDropMass w N start K + rawCurveDropAt w N start K := by
  simp [rawCurveDropMass, List.range_succ]

private theorem rawNonselfProductiveTimes_length_succ_of_mem
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat)
    (hprod : RawProductiveAt w N start K)
    (hnonself : ¬ RawCurveSelfAt w start K) :
    (rawNonselfProductiveTimes w N start (K + 1)).length =
      (rawNonselfProductiveTimes w N start K).length + 1 := by
  classical
  simp [rawNonselfProductiveTimes, List.range_succ, hprod, hnonself]

private theorem rawNonselfProductiveTimes_length_succ_of_not_mem
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat)
    (hnot : ¬ (RawProductiveAt w N start K ∧
      ¬ RawCurveSelfAt w start K)) :
    (rawNonselfProductiveTimes w N start (K + 1)).length =
      (rawNonselfProductiveTimes w N start K).length := by
  classical
  simp [rawNonselfProductiveTimes, List.range_succ, hnot]

/-! ## The unconditional global potential inequality -/

/-- **Finite-curve amortization.**  Over an arbitrary live raw prefix, every
productive non-self pivot consumes one unit of upward variation.  All upward
variation is paid for by the initial-to-final size difference plus the total
downward variation accumulated at self-pivots. -/
theorem raw_nonself_growth_amortized
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome) :
    rawFiniteCurveSizeAt w N start 0 +
        (rawNonselfProductiveTimes w N start K).length ≤
      rawFiniteCurveSizeAt w N start K +
        rawCurveDropMass w N start K := by
  induction K with
  | zero => simp [rawNonselfProductiveTimes]
  | succ K ih =>
      have hprev := ih (fun k hk => hlive k (by omega))
      by_cases hprod : RawProductiveAt w N start K
      · by_cases hself : RawCurveSelfAt w start K
        · have hsize := rawProductiveAt_self_curve_nonincrease
            hN hprod hself
          have hcount := rawNonselfProductiveTimes_length_succ_of_not_mem
            w N start K (by simp [hself])
          rw [hcount, rawCurveDropMass_succ]
          unfold rawCurveDropAt
          omega
        · have hsize := rawProductiveAt_nonself_curve_growth
            hN hprod hself
          have hcount := rawNonselfProductiveTimes_length_succ_of_mem
            w N start K hprod hself
          rw [hcount, rawCurveDropMass_succ]
          unfold rawCurveDropAt
          omega
      · have hsize := rawNonproductiveAt_curve_size_eq
          hN (hlive (K + 1) (by omega)) hprod
        have hcount := rawNonselfProductiveTimes_length_succ_of_not_mem
          w N start K (by simp [hprod])
        rw [hcount, rawCurveDropMass_succ]
        unfold rawCurveDropAt
        omega

/-- Port-cap corollary of `raw_nonself_growth_amortized`. -/
theorem raw_nonself_growth_le_three_mul_add_drop
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome) :
    (rawNonselfProductiveTimes w N start K).length ≤
      3 * N + rawCurveDropMass w N start K := by
  have hpotential := raw_nonself_growth_amortized hN start K hlive
  have hfinal : rawFiniteCurveSizeAt w N start K ≤ 3 * N := by
    unfold rawFiniteCurveSizeAt
    exact finiteCurvePorts_length_le w N
      ((stepN w K start).getD start).2
      ((stepN w K start).getD start).1
  omega

/-! ## Strict shrinks are paid for by drop mass -/

/-- Strict productive self-shrinks in `[0, K)`. -/
noncomputable def rawStrictSelfShrinkTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter
    (fun k => decide (RawStrictSelfShrinkAt w N start k))

noncomputable def rawDroppedCurvePortsAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : List Nat :=
  (rawFiniteCurvePortsAt w N start k).filter (fun p =>
    ! decide (p ∈ rawFiniteCurvePortsAt w N start (k + 1)))

theorem mem_rawDroppedCurvePortsAt_iff
    {w : Wiring} {N k p : Nat} {start : Nat × Tongues} :
    p ∈ rawDroppedCurvePortsAt w N start k ↔
      p ∈ rawFiniteCurvePortsAt w N start k ∧
      p ∉ rawFiniteCurvePortsAt w N start (k + 1) := by
  classical
  simp [rawDroppedCurvePortsAt]

private theorem nodup_subset_length_amortization
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    ∀ {xs ys : List alpha}, xs.Nodup →
      (∀ x, x ∈ xs → x ∈ ys) → xs.length ≤ ys.length := by
  intro xs
  induction xs with
  | nil => intro ys _ _; exact Nat.zero_le _
  | cons x rest ih =>
      intro ys hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hrest : ∀ y, y ∈ rest → y ∈ ys.erase x := by
        intro y hy
        have hyMem := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun heq => hnd.1 (heq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyMem
      have hle := ih hnd.2 hrest
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

private theorem filter_partition_length_amortization
    (p : Nat → Bool) : ∀ xs : List Nat,
      (xs.filter p).length +
        (xs.filter (fun x => ! p x)).length = xs.length := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      cases hpx : p x <;> simp [hpx] <;> omega

private theorem rawNonselfProductiveTimes_nodup
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawNonselfProductiveTimes w N start K).Nodup := by
  classical
  unfold rawNonselfProductiveTimes
  exact (List.nodup_range.filter _)

private theorem rawNonselfProductiveTimes_prefix_subset
    {w : Wiring} {N a b : Nat} {start : Nat × Tongues}
    (hab : a ≤ b) : ∀ k,
      k ∈ rawNonselfProductiveTimes w N start a →
      k ∈ rawNonselfProductiveTimes w N start b := by
  intro k hk
  have hdata := mem_rawNonselfProductiveTimes_iff.mp hk
  exact mem_rawNonselfProductiveTimes_iff.mpr
    ⟨by omega, hdata.2.1, hdata.2.2⟩

/-- The non-self epoch rank is monotone in raw time. -/
theorem rawNonselfRank_mono
    {w : Wiring} {N a b : Nat} {start : Nat × Tongues}
    (hab : a ≤ b) :
    rawNonselfRank w N start a ≤ rawNonselfRank w N start b := by
  unfold rawNonselfRank
  exact nodup_subset_length_amortization
    (rawNonselfProductiveTimes_nodup w N start a)
    (rawNonselfProductiveTimes_prefix_subset hab)

/-- Crossing one productive non-self pivot strictly increases the epoch
rank. -/
theorem rawNonselfRank_lt_of_event_between
    {w : Wiring} {N a j b : Nat} {start : Nat × Tongues}
    (haj : a ≤ j) (hjb : j < b)
    (hprod : RawProductiveAt w N start j)
    (hnonself : ¬ RawCurveSelfAt w start j) :
    rawNonselfRank w N start a < rawNonselfRank w N start b := by
  let earlier := rawNonselfProductiveTimes w N start a
  let later := rawNonselfProductiveTimes w N start b
  have hjLater : j ∈ later := by
    dsimp [later]
    exact mem_rawNonselfProductiveTimes_iff.mpr
      ⟨hjb, hprod, hnonself⟩
  have hjEarlier : j ∉ earlier := by
    intro hj
    have hjlt := (mem_rawNonselfProductiveTimes_iff.mp hj).1
    omega
  have hconsNodup : (j :: earlier).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hjEarlier,
      rawNonselfProductiveTimes_nodup w N start a⟩
  have hsub : ∀ p, p ∈ j :: earlier → p ∈ later := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hjLater
    · exact rawNonselfProductiveTimes_prefix_subset
        (Nat.le_trans haj (Nat.le_of_lt hjb)) p hp
  have hle := nodup_subset_length_amortization hconsNodup hsub
  dsimp [earlier, later] at hle
  unfold rawNonselfRank
  omega

/-! ## Raw-time shifting -/

/-- A reached configuration identifies every later shifted `stepN` value
with the corresponding absolute raw time. -/
theorem stepN_shift_eq
    {w : Wiring} {shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle) :
    stepN w d middle = stepN w (shift + d) start := by
  rw [stepN_add, hreach]
  rfl

private theorem stepN_prefix_some_amortization
    {w : Wiring} {start finish : Nat × Tongues} {d K : Nat}
    (hd : d ≤ K) (hfinish : stepN w K start = some finish) :
    ∃ middle, stepN w d start = some middle := by
  let rest := K - d
  have hsplit : K = d + rest := by
    dsimp [rest]
    omega
  rw [hsplit, stepN_add] at hfinish
  cases hprefix : stepN w d start with
  | none => simp [hprefix] at hfinish
  | some middle => exact ⟨middle, rfl⟩

theorem restrictedTonguesAt_shift_eq
    {w : Wiring} {N shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : ∃ finish, stepN w d middle = some finish) :
    restrictedTonguesAt w N middle d =
      restrictedTonguesAt w N start (shift + d) := by
  obtain ⟨finish, hfinish⟩ := hlive
  have hglobal : stepN w (shift + d) start = some finish := by
    rw [← stepN_shift_eq hreach]
    exact hfinish
  simp [restrictedTonguesAt, tonguesAt, hfinish, hglobal]

theorem rawEntryAt_shift_eq
    {w : Wiring} {shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : ∃ finish, stepN w d middle = some finish) :
    rawEntryAt w middle d = rawEntryAt w start (shift + d) := by
  obtain ⟨finish, hfinish⟩ := hlive
  have hglobal : stepN w (shift + d) start = some finish := by
    rw [← stepN_shift_eq hreach]
    exact hfinish
  simp [rawEntryAt, hfinish, hglobal]

theorem rawWriterAt_shift_eq
    {w : Wiring} {shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : ∃ finish, stepN w d middle = some finish) :
    rawWriterAt w middle d = rawWriterAt w start (shift + d) := by
  simp [rawWriterAt, rawEntryAt_shift_eq hreach hlive]

theorem RawProductiveAt.shift_iff
    {w : Wiring} {N shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : ∃ finish, stepN w (d + 1) middle = some finish) :
    RawProductiveAt w N middle d ↔
      RawProductiveAt w N start (shift + d) := by
  obtain ⟨finish, hfinish⟩ := hlive
  obtain ⟨current, hcurrent⟩ :=
    stepN_prefix_some_amortization (d := d) (K := d + 1)
      (by omega) hfinish
  have hnextLive : ∃ finish, stepN w (d + 1) middle = some finish :=
    ⟨finish, hfinish⟩
  have hcurrentLive : ∃ current, stepN w d middle = some current :=
    ⟨current, hcurrent⟩
  unfold RawProductiveAt
  have hnext : shift + (d + 1) = (shift + d) + 1 := by omega
  rw [restrictedTonguesAt_shift_eq hreach hnextLive,
    restrictedTonguesAt_shift_eq hreach hcurrentLive,
    stepN_shift_eq hreach, hnext]

theorem RawCurveSelfAt.shift_iff
    {w : Wiring} {shift d : Nat} {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : ∃ finish, stepN w d middle = some finish) :
    RawCurveSelfAt w middle d ↔
      RawCurveSelfAt w start (shift + d) := by
  obtain ⟨finish, hfinish⟩ := hlive
  have hglobal : stepN w (shift + d) start = some finish := by
    rw [← stepN_shift_eq hreach]
    exact hfinish
  unfold RawCurveSelfAt
  simp [hfinish, hglobal]

/-! ## Canonical self-epoch fibres -/

private def epochMinFrom : Nat → List Nat → Nat
  | x, [] => x
  | x, y :: ys => Nat.min x (epochMinFrom y ys)

private def epochMaxFrom : Nat → List Nat → Nat
  | x, [] => x
  | x, y :: ys => Nat.max x (epochMaxFrom y ys)

private theorem epochMinFrom_mem : ∀ x xs,
    epochMinFrom x xs ∈ x :: xs := by
  intro x xs
  induction xs generalizing x with
  | nil => simp [epochMinFrom]
  | cons y ys ih =>
      change x.min (epochMinFrom y ys) ∈ x :: y :: ys
      by_cases h : x ≤ epochMinFrom y ys
      · have hmin : x.min (epochMinFrom y ys) = x :=
          Nat.min_eq_left h
        exact hmin.symm ▸ List.mem_cons_self
      · have hle : epochMinFrom y ys ≤ x := by omega
        have hmin : x.min (epochMinFrom y ys) =
            epochMinFrom y ys := Nat.min_eq_right hle
        exact hmin.symm ▸ List.mem_cons_of_mem _ (ih y)

private theorem epochMaxFrom_mem : ∀ x xs,
    epochMaxFrom x xs ∈ x :: xs := by
  intro x xs
  induction xs generalizing x with
  | nil => simp [epochMaxFrom]
  | cons y ys ih =>
      change x.max (epochMaxFrom y ys) ∈ x :: y :: ys
      by_cases h : x ≤ epochMaxFrom y ys
      · have hmax : x.max (epochMaxFrom y ys) =
            epochMaxFrom y ys := Nat.max_eq_right h
        exact hmax.symm ▸ List.mem_cons_of_mem _ (ih y)
      · have hle : epochMaxFrom y ys ≤ x := by omega
        have hmax : x.max (epochMaxFrom y ys) = x :=
          Nat.max_eq_left hle
        exact hmax.symm ▸ List.mem_cons_self

private theorem epochMinFrom_le_mem : ∀ x xs y,
    y ∈ x :: xs → epochMinFrom x xs ≤ y := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · cases hy
  | cons z zs ih =>
      intro y hy
      change x.min (epochMinFrom z zs) ≤ y
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (ih z y hy)

private theorem mem_le_epochMaxFrom : ∀ x xs y,
    y ∈ x :: xs → y ≤ epochMaxFrom x xs := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · cases hy
  | cons z zs ih =>
      intro y hy
      change y ≤ x.max (epochMaxFrom z zs)
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih z y hy) (Nat.le_max_right _ _)

private theorem map_filter_nodup_amortization
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha → beta) (p : alpha → Bool) :
    ∀ {xs : List alpha}, (xs.map f).Nodup →
      ((xs.filter p).map f).Nodup := by
  intro xs hnd
  induction xs with
  | nil => simp
  | cons x rest ih =>
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

/-- **Four-state fibre theorem.**  Among any duplicate-free sample from a
live prefix, all times with the same number of preceding non-self pivots lie
in one self-only epoch and therefore contribute at most four vectors. -/
theorem rawNonselfRank_fibre_le_four
    {w : Wiring} {N K r : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (times : List Nat) (htimes : ∀ k, k ∈ times → k ≤ K)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    (times.filter (fun k => decide
      (rawNonselfRank w N start k = r))).length ≤ 4 := by
  classical
  let fibre := times.filter (fun k => decide
    (rawNonselfRank w N start k = r))
  change fibre.length ≤ 4
  cases hfibre : fibre with
  | nil => simp
  | cons x xs =>
      let a := epochMinFrom x xs
      let b := epochMaxFrom x xs
      have haMem : a ∈ fibre := by
        rw [hfibre]
        exact epochMinFrom_mem x xs
      have hbMem : b ∈ fibre := by
        rw [hfibre]
        exact epochMaxFrom_mem x xs
      have hmemBounds : ∀ k, k ∈ fibre → a ≤ k ∧ k ≤ b := by
        intro k hk
        rw [hfibre] at hk
        exact ⟨epochMinFrom_le_mem x xs k hk,
          mem_le_epochMaxFrom x xs k hk⟩
      have hab : a ≤ b := (hmemBounds a haMem).2
      have hfibreTimes : ∀ k, k ∈ fibre → k ∈ times := by
        intro k hk
        exact (List.mem_filter.mp hk).1
      have hrank : ∀ k, k ∈ fibre →
          rawNonselfRank w N start k = r := by
        intro k hk
        exact of_decide_eq_true (List.mem_filter.mp hk).2
      have hnoNonself : ∀ j, a ≤ j → j < b →
          RawProductiveAt w N start j → RawCurveSelfAt w start j := by
        intro j haj hjb hprod
        apply Classical.byContradiction
        intro hnonself
        have hlt := rawNonselfRank_lt_of_event_between
          haj hjb hprod hnonself
        have haRank := hrank a haMem
        have hbRank := hrank b hbMem
        omega
      have haK : a ≤ K := htimes a (hfibreTimes a haMem)
      obtain ⟨middle, hmiddle⟩ :=
        Option.isSome_iff_exists.mp (hlive a haK)
      let span := b - a
      have habEq : a + span = b := by
        dsimp [span]
        omega
      have hlocalLive : ∀ d, d ≤ span →
          (stepN w d middle).isSome := by
        intro d hd
        rw [stepN_shift_eq hmiddle]
        apply hlive
        have hbK : b ≤ K := htimes b (hfibreTimes b hbMem)
        omega
      have hlocalSelf : ∀ d, d < span →
          RawProductiveAt w N middle d →
          RawCurveSelfAt w middle d := by
        intro d hd hprod
        have hnextSome := hprod.1
        have hnextExists := Option.isSome_iff_exists.mp hnextSome
        have hglobalProd :=
          (RawProductiveAt.shift_iff hmiddle hnextExists).mp hprod
        have hglobalSelf := hnoNonself (a + d)
          (by omega) (by omega) hglobalProd
        have hcurSome := hlocalLive d (by omega)
        have hcurExists := Option.isSome_iff_exists.mp hcurSome
        exact (RawCurveSelfAt.shift_iff hmiddle hcurExists).mpr hglobalSelf
      let offsets := fibre.map (fun k => k - a)
      have hoffsetsBound : ∀ d, d ∈ offsets → d ≤ span := by
        intro d hd
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
        have hkBounds := hmemBounds k hk
        omega
      have hfibreNodup :
          (fibre.map (restrictedTonguesAt w N start)).Nodup := by
        dsimp [fibre]
        exact map_filter_nodup_amortization
          (restrictedTonguesAt w N start)
          (fun k => decide (rawNonselfRank w N start k = r)) hnd
      have hoffsetsMap :
          offsets.map (restrictedTonguesAt w N middle) =
            fibre.map (restrictedTonguesAt w N start) := by
        dsimp [offsets]
        rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        have hkBounds := hmemBounds k hk
        have hka : a + (k - a) = k := by omega
        have hlocalSome := hlocalLive (k - a) (by omega)
        have hlocalExists := Option.isSome_iff_exists.mp hlocalSome
        have hshift := restrictedTonguesAt_shift_eq
          (N := N) hmiddle hlocalExists
        simpa [Function.comp_apply, hka] using hshift
      have hoffsetsNodup :
          (offsets.map (restrictedTonguesAt w N middle)).Nodup := by
        rw [hoffsetsMap]
        exact hfibreNodup
      have hfour := rawSelfEpoch_distinct_le_four
        hN middle hlocalLive hlocalSelf hoffsetsBound hoffsetsNodup
      simpa [offsets, hfibre] using hfour

private theorem bounded_multiplicity_length_amortization
    (f : Nat → Nat) (cap : Nat) : ∀ (tags : List Nat) (xs : List Nat),
    (∀ tag, (xs.filter (fun x => decide (f x = tag))).length ≤ cap) →
    (∀ x, x ∈ xs → f x ∈ tags) →
    xs.length ≤ cap * tags.length := by
  intro tags
  induction tags with
  | nil =>
      intro xs _ hmem
      cases xs with
      | nil => simp
      | cons x rest => cases hmem x List.mem_cons_self
  | cons tag tags ih =>
      intro xs hcap hmem
      let yes := xs.filter (fun x => decide (f x = tag))
      let no := xs.filter (fun x => ! decide (f x = tag))
      have hyes : yes.length ≤ cap := by
        simpa [yes] using hcap tag
      have hcapNo : ∀ other,
          (no.filter (fun x => decide (f x = other))).length ≤ cap := by
        intro other
        have hle := List.length_filter_le
          (fun x => ! decide (f x = tag))
          (xs.filter (fun x => decide (f x = other)))
        have hcomm :
            no.filter (fun x => decide (f x = other)) =
              (xs.filter (fun x => decide (f x = other))).filter
                (fun x => ! decide (f x = tag)) := by
          simp [no, List.filter_filter, Bool.and_comm]
        rw [hcomm]
        exact Nat.le_trans hle (hcap other)
      have hmemNo : ∀ x, x ∈ no → f x ∈ tags := by
        intro x hx
        have hxData := List.mem_filter.mp hx
        have hne : f x ≠ tag := by
          simpa only [Bool.not_eq_true', decide_eq_false_iff_not]
            using hxData.2
        rcases List.mem_cons.mp (hmem x hxData.1) with heq | htail
        · exact (hne heq).elim
        · exact htail
      have hno := ih no hcapNo hmemNo
      have hsplit := filter_partition_length_amortization
        (fun x => decide (f x = tag)) xs
      change yes.length + no.length = xs.length at hsplit
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega


theorem raw_self_pivot_curve_ports_subset
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hprod : RawProductiveAt w N start k)
    (hself : RawCurveSelfAt w start k) :
    ∀ p, p ∈ rawFiniteCurvePortsAt w N start (k + 1) →
      p ∈ rawFiniteCurvePortsAt w N start k := by
  obtain ⟨cur, next, C, hCwriter, hcur, hnext, hstep,
      hentry, hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hCcur : C = cur.1 / 3 := by
    simpa [rawWriterAt, rawEntryAt, hcur] using hCwriter
  have hself' : CurveReach w cur.2 cur.1 (3 * C) := by
    unfold RawCurveSelfAt at hself
    simpa [hcur, hCcur] using hself
  have hlift := self_endpoint_pivot_curveReach_subset
    hstep hentry hexit hflip hself'
  intro p hp
  unfold rawFiniteCurvePortsAt at hp ⊢
  simp only [hcur, hnext, Option.getD_some] at hp ⊢
  rw [mem_finiteCurvePorts_iff] at hp ⊢
  exact ⟨hp.1, hlift p hp.2⟩

/-- On a productive self-pivot, filtering the old carrier by absence from
the new carrier measures exactly the cardinality drop. -/
theorem rawDroppedCurvePortsAt_length_eq_drop
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hprod : RawProductiveAt w N start k)
    (hself : RawCurveSelfAt w start k) :
    (rawDroppedCurvePortsAt w N start k).length =
      rawCurveDropAt w N start k := by
  classical
  let old := rawFiniteCurvePortsAt w N start k
  let new := rawFiniteCurvePortsAt w N start (k + 1)
  let kept := old.filter (fun p => decide (p ∈ new))
  have holdNodup : old.Nodup := by
    dsimp [old, rawFiniteCurvePortsAt]
    exact finiteCurvePorts_nodup w N
      ((stepN w k start).getD start).2
      ((stepN w k start).getD start).1
  have hnewNodup : new.Nodup := by
    dsimp [new, rawFiniteCurvePortsAt]
    exact finiteCurvePorts_nodup w N
      ((stepN w (k + 1) start).getD start).2
      ((stepN w (k + 1) start).getD start).1
  have hnewOld : ∀ p, p ∈ new → p ∈ old := by
    intro p hp
    exact raw_self_pivot_curve_ports_subset hN hprod hself p hp
  have hkeptNodup : kept.Nodup := by
    exact holdNodup.filter _
  have hkeptNew : ∀ p, p ∈ kept → p ∈ new := by
    intro p hp
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  have hnewKept : ∀ p, p ∈ new → p ∈ kept := by
    intro p hp
    exact List.mem_filter.mpr ⟨hnewOld p hp, decide_eq_true hp⟩
  have hkeptLe := nodup_subset_length_amortization
    hkeptNodup hkeptNew
  have hnewLe := nodup_subset_length_amortization
    hnewNodup hnewKept
  have hkeptLength : kept.length = new.length := by omega
  have hkeptLengthRaw :
      (old.filter (fun p => decide (p ∈ new))).length = new.length := by
    simpa [kept] using hkeptLength
  have hpartition := filter_partition_length_amortization
    (fun p => decide (p ∈ new)) old
  change (old.filter (fun p => ! decide (p ∈ new))).length =
    old.length - new.length
  omega

/-- Every unit of curve-size drop, tagged by the concrete physical port
discarded at its strict self-shrink. -/
noncomputable def rawDroppedCurvePortUnits
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat :=
  (rawStrictSelfShrinkTimes w N start K).flatMap
    (rawDroppedCurvePortsAt w N start)

/-- For a live bounded run, the flattened physical lost-port list has length
exactly equal to total downward variation.  Thus global injectivity of this
list is precisely the missing finite-port charge, not a stronger numerical
assumption smuggled into the statement. -/
theorem rawDroppedCurvePortUnits_length_eq_dropMass
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome) :
    (rawDroppedCurvePortUnits w N start K).length =
      rawCurveDropMass w N start K := by
  induction K with
  | zero => simp [rawDroppedCurvePortUnits, rawStrictSelfShrinkTimes]
  | succ K ih =>
      have hprev := ih (fun k hk => hlive k (by omega))
      by_cases hshrink : RawStrictSelfShrinkAt w N start K
      · have hprod := hshrink.1
        have hself : RawCurveSelfAt w start K := hshrink.2.1
        have hdropped := rawDroppedCurvePortsAt_length_eq_drop
          hN hprod hself
        have hunits :
            rawDroppedCurvePortUnits w N start (K + 1) =
              rawDroppedCurvePortUnits w N start K ++
                rawDroppedCurvePortsAt w N start K := by
          simp [rawDroppedCurvePortUnits, rawStrictSelfShrinkTimes,
            List.range_succ, hshrink]
        rw [hunits, List.length_append, hdropped,
          rawCurveDropMass_succ, hprev]
      · have hdrop : rawCurveDropAt w N start K = 0 := by
          by_cases hprod : RawProductiveAt w N start K
          · by_cases hself : RawCurveSelfAt w start K
            · have hle := rawProductiveAt_self_curve_nonincrease
                hN hprod hself
              have heq : rawFiniteCurveSizeAt w N start (K + 1) =
                  rawFiniteCurveSizeAt w N start K := by
                by_cases hlt : rawFiniteCurveSizeAt w N start (K + 1) <
                    rawFiniteCurveSizeAt w N start K
                · exact (hshrink ⟨hprod, hself, hlt⟩).elim
                · omega
              unfold rawCurveDropAt
              omega
            · have hlt := rawProductiveAt_nonself_curve_growth
                hN hprod hself
              unfold rawCurveDropAt
              omega
          · have heq := rawNonproductiveAt_curve_size_eq
              hN (hlive (K + 1) (by omega)) hprod
            unfold rawCurveDropAt
            omega
        have hunits :
            rawDroppedCurvePortUnits w N start (K + 1) =
              rawDroppedCurvePortUnits w N start K := by
          simp [rawDroppedCurvePortUnits, rawStrictSelfShrinkTimes,
            List.range_succ, hshrink]
        rw [hunits, rawCurveDropMass_succ, hdrop, hprev]
        simp

/-- Every port appearing in the global lost-port unit list is one of the
physical `3 * N` ports. -/
theorem rawDroppedCurvePortUnits_mem_lt
    {w : Wiring} {N K p : Nat} {start : Nat × Tongues}
    (hp : p ∈ rawDroppedCurvePortUnits w N start K) : p < 3 * N := by
  obtain ⟨k, _hk, hpk⟩ := List.mem_flatMap.mp hp
  have hpOld := (mem_rawDroppedCurvePortsAt_iff.mp hpk).1
  unfold rawFiniteCurvePortsAt at hpOld
  exact (mem_finiteCurvePorts_iff.mp hpOld).1

/-- **Finite physical drop charge.**  If no represented carrier port is
discarded twice, total downward variation is at most the `3 * N` physical
ports. -/
theorem rawCurveDropMass_le_three_mul_of_lost_ports_nodup
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hcharge : (rawDroppedCurvePortUnits w N start K).Nodup) :
    rawCurveDropMass w N start K ≤ 3 * N := by
  have hports := nodup_nat_lt_length hcharge
    (fun p hp => rawDroppedCurvePortUnits_mem_lt hp)
  rw [rawDroppedCurvePortUnits_length_eq_dropMass hN start K hlive]
    at hports
  exact hports


theorem rawCurveDropMass_le_two_mul_of_nested_restoration_charge
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    {m : Echo.Machine} {e r0 : Nat → Nat}
    {depth : Nat} {opening closing : Nat → Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (A : Echo.FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing)
    (slots : List Nat)
    (hroot : ∀ i, i < depth → Echo.oldSlot m e r0 (opening i) ∈ slots)
    (hslots : slots.length ≤ 2 * N)
    (hcompile : rawCurveDropMass w N start K ≤ depth) :
    rawCurveDropMass w N start K ≤ 2 * N := by
  have _hphysical := rawDroppedCurvePortUnits_length_eq_dropMass
    hN start K hlive
  have hdepth :=
    Echo.FiniteStrictNestedRestorationFamily.depth_le_two_mul
      m e r0 A slots hroot hslots
  exact Nat.le_trans hcompile hdepth


structure RawPermanentSelfTail
    (w : Wiring) (N : Nat) (start : Nat × Tongues) : Prop where
  live : ∀ k, (stepN w k start).isSome
  self : ∀ k, RawProductiveAt w N start k →
    RawCurveSelfAt w start k

/-- A permanent self tail exposes at most four distinct visible tongue
vectors, even when the observation times are unbounded and sparse. -/
theorem RawPermanentSelfTail.distinct_snapshots_le_four
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (T : RawPermanentSelfTail w N start)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 4 := by
  let K := maxRawTime times
  apply rawSelfEpoch_distinct_le_four
    (K := K) hN start
  · intro k _hk
    exact T.live k
  · intro k _hk hprod
    exact T.self k hprod
  · intro k hk
    exact le_maxRawTime_of_mem hk
  · exact hnd

end GeneralN
