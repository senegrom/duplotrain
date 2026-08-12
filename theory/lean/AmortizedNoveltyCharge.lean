import TrackFiniteAlternation
import KnownEdgeNAddFiveAlt
import EmptyCurvePotential
import SelfShrinkChargeClosure

/-!
# Exact charging form of the `N+4` target

For a horizon `K`, write `F` for productive first-writer events and `R`
for globally novel repeated-writer events. The sharp target is

`F.length + R.length <= N + 3`.

After dropping the first three members of `R`, this is exactly a finite
matching problem: the remaining events must inject into switch coordinates
absent from `F`. This file formalizes that matching equivalence and the
equivalence between the amortized law and the raw `N+4` state law.
-/

namespace GeneralN

/-- The exact raw `N+4` statement, copied proposition-for-proposition from
the currently unregistered `StateLawNAddFour.lean` target module. -/
def StateLawNAddFourTarget : Prop :=
  forall (w : Wiring) (N : Nat),
    (forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N) ->
    forall (start : Nat × Tongues) (times : List Nat),
      (forall k, k ∈ times -> (stepN w k start).isSome) ->
      (times.map (fun k => VectorCount.restrict N
        ((stepN w k start).getD start).2)).Nodup ->
      times.length <= N + 4

/-- The exact coefficient-one amortized target. -/
def AmortizedNoveltyNAddThreeTarget : Prop :=
  forall (w : Wiring) (N : Nat),
    (forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N) ->
    forall (start : Nat × Tongues) (K : Nat),
      (rawFirstWriterTimes w N start K).length +
        (rawRepeatedWriterNovelTimes w N start K).length <= N + 3

private theorem anc_nodup_map_of_injective_on_mem
    {alpha beta : Type}
    [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    {f : alpha -> beta} {xs : List alpha}
    (hnd : xs.Nodup)
    (hinj : forall a, a ∈ xs -> forall b, b ∈ xs ->
      f a = f b -> a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
        have hab := hinj a List.mem_cons_self b
          (List.mem_cons_of_mem _ hb) hfb.symm
        exact hnd.1 (hab ▸ hb)
      · exact ih hnd.2 (fun x hx y hy =>
          hinj x (List.mem_cons_of_mem _ hx)
            y (List.mem_cons_of_mem _ hy))

private theorem anc_nodup_subset_length
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall {xs ys : List alpha}, xs.Nodup ->
      (forall x, x ∈ xs -> x ∈ ys) -> xs.length <= ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _
      exact Nat.zero_le _
  | cons x rest ih =>
      intro ys hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hrest : forall y, y ∈ rest -> y ∈ ys.erase x := by
        intro y hy
        have hyMem := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun heq => hnd.1 (heq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyMem
      have hle := ih hnd.2 hrest
      rw [List.length_erase_of_mem hx] at hle
      have hpositive : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

private theorem rawFirstWriterTimes_nodup_charge
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawFirstWriterTimes w N start K).Nodup := by
  classical
  unfold rawFirstWriterTimes
  exact List.nodup_range.filter _

/-- Switch coordinates consumed by productive first-writer events. -/
noncomputable def rawFirstWriterSwitches
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List Nat :=
  (rawFirstWriterTimes w N start K).map (rawWriterAt w start)

theorem rawFirstWriterSwitches_nodup
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {K : Nat} :
    (rawFirstWriterSwitches w N start K).Nodup := by
  unfold rawFirstWriterSwitches
  apply anc_nodup_map_of_injective_on_mem
    (rawFirstWriterTimes_nodup_charge w N start K)
  intro i hi j hj hwriter
  have hiData := mem_rawFirstWriterTimes_iff.mp hi
  have hjData := mem_rawFirstWriterTimes_iff.mp hj
  exact rawFirstWriterAt_injective hiData.2 hjData.2 hwriter

theorem rawFirstWriterSwitches_bounded
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat) :
    forall C, C ∈ rawFirstWriterSwitches w N start K -> C < N := by
  intro C hC
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hC
  have hkData := mem_rawFirstWriterTimes_iff.mp hk
  exact rawProductiveAt_writer_lt hN hkData.2.1

/-- Coordinates not consumed by a productive first writer before `K`. -/
noncomputable def rawUnusedFirstWriterSwitches
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List Nat := by
  classical
  exact (List.range N).filter (fun C => decide
    (C ∉ rawFirstWriterSwitches w N start K))

theorem mem_rawUnusedFirstWriterSwitches_iff
    {w : Wiring} {N C K : Nat} {start : Nat × Tongues} :
    C ∈ rawUnusedFirstWriterSwitches w N start K ↔
      C < N ∧ C ∉ rawFirstWriterSwitches w N start K := by
  classical
  simp [rawUnusedFirstWriterSwitches]

theorem rawUnusedFirstWriterSwitches_nodup
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawUnusedFirstWriterSwitches w N start K).Nodup := by
  classical
  unfold rawUnusedFirstWriterSwitches
  exact List.nodup_range.filter _

/-- First-writer and unused coordinates partition `0,...,N-1` cardinally. -/
theorem firstWriter_add_unused_length_eq
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat) :
    (rawFirstWriterSwitches w N start K).length +
      (rawUnusedFirstWriterSwitches w N start K).length = N := by
  let first := rawFirstWriterSwitches w N start K
  let unused := rawUnusedFirstWriterSwitches w N start K
  have hfirstNodup : first.Nodup := by
    dsimp [first]
    exact rawFirstWriterSwitches_nodup
  have hunusedNodup : unused.Nodup := by
    dsimp [unused]
    exact rawUnusedFirstWriterSwitches_nodup w N start K
  have hdisjoint : forall a, a ∈ first -> forall b, b ∈ unused ->
      a ≠ b := by
    intro a ha b hb hab
    have hbData := mem_rawUnusedFirstWriterSwitches_iff.mp (by
      simpa [unused] using hb)
    apply hbData.2
    rw [← hab]
    exact ha
  have hallNodup : (first ++ unused).Nodup :=
    List.nodup_append.mpr
      ⟨hfirstNodup, hunusedNodup, hdisjoint⟩
  have hallBounded : forall C, C ∈ first ++ unused -> C < N := by
    intro C hC
    rcases List.mem_append.mp hC with hfirst | hunused
    · exact rawFirstWriterSwitches_bounded hN start K C (by
        simpa [first] using hfirst)
    · exact (mem_rawUnusedFirstWriterSwitches_iff.mp (by
        simpa [unused] using hunused)).1
  have hupper := nodup_nat_lt_length hallNodup hallBounded
  have hcomplete : forall C, C ∈ List.range N -> C ∈ first ++ unused := by
    intro C hC
    have hClt : C < N := List.mem_range.mp hC
    by_cases hfirst : C ∈ first
    · exact List.mem_append_left _ hfirst
    · apply List.mem_append_right
      apply mem_rawUnusedFirstWriterSwitches_iff.mpr
      exact ⟨hClt, by simpa [first] using hfirst⟩
  have hlower := anc_nodup_subset_length List.nodup_range hcomplete
  simp only [List.length_append, List.length_range] at hupper hlower
  change first.length + unused.length = N
  exact Nat.le_antisymm hupper hlower

/-- Repeated novelties after the three constant-sized exceptions. -/
noncomputable def repeatedNoveltyChargeTail
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List Nat :=
  (rawRepeatedWriterNovelTimes w N start K).drop 3

theorem repeatedNoveltyChargeTail_nodup
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (repeatedNoveltyChargeTail w N start K).Nodup := by
  unfold repeatedNoveltyChargeTail
  exact List.Pairwise.drop
    (rawRepeatedWriterNovelTimes_nodup w N start K)

theorem repeatedNovelty_length_le_chargeTail_add_three
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawRepeatedWriterNovelTimes w N start K).length <=
      (repeatedNoveltyChargeTail w N start K).length + 3 := by
  unfold repeatedNoveltyChargeTail
  rw [List.length_drop]
  omega

/-- A positional injection of `R.drop 3` into distinct unused switches. -/
structure AmortizedNoveltyChargeCertificate
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) where
  charges : List Nat
  length_eq : charges.length =
    (repeatedNoveltyChargeTail w N start K).length
  charges_nodup : charges.Nodup
  charges_bounded : forall C, C ∈ charges -> C < N
  charges_unused : forall C, C ∈ charges ->
    C ∉ rawFirstWriterSwitches w N start K

/-- A charge certificate implies the exact amortized inequality. -/
theorem amortizedNovelty_of_chargeCertificate
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (C : AmortizedNoveltyChargeCertificate w N start K) :
    (rawFirstWriterTimes w N start K).length +
      (rawRepeatedWriterNovelTimes w N start K).length <= N + 3 := by
  let first := rawFirstWriterSwitches w N start K
  have hfirstNodup : first.Nodup := by
    dsimp [first]
    exact rawFirstWriterSwitches_nodup
  have hdisjoint : forall a, a ∈ first -> forall b, b ∈ C.charges ->
      a ≠ b := by
    intro a ha b hb hab
    apply C.charges_unused b hb
    rw [← hab]
    exact ha
  have hcombinedNodup : (first ++ C.charges).Nodup :=
    List.nodup_append.mpr
      ⟨hfirstNodup, C.charges_nodup, hdisjoint⟩
  have hcombinedBounded : forall D, D ∈ first ++ C.charges -> D < N := by
    intro D hD
    rcases List.mem_append.mp hD with hfirst | hcharge
    · exact rawFirstWriterSwitches_bounded hN start K D (by
        simpa [first] using hfirst)
    · exact C.charges_bounded D hcharge
  have hcapacity := nodup_nat_lt_length hcombinedNodup hcombinedBounded
  have htail := repeatedNovelty_length_le_chargeTail_add_three
    w N start K
  have hfirstLength : first.length =
      (rawFirstWriterTimes w N start K).length := by
    simp [first, rawFirstWriterSwitches]
  have hchargeLength := C.length_eq
  simp only [List.length_append] at hcapacity
  omega

/-- The amortized inequality constructs a matching from the unused list. -/
theorem chargeCertificate_of_amortizedNovelty
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) (K : Nat)
    (hbudget :
      (rawFirstWriterTimes w N start K).length +
        (rawRepeatedWriterNovelTimes w N start K).length <= N + 3) :
    Nonempty (AmortizedNoveltyChargeCertificate w N start K) := by
  let first := rawFirstWriterSwitches w N start K
  let unused := rawUnusedFirstWriterSwitches w N start K
  let tail := repeatedNoveltyChargeTail w N start K
  have hpartition := firstWriter_add_unused_length_eq hN start K
  change first.length + unused.length = N at hpartition
  have hfirstLength : first.length =
      (rawFirstWriterTimes w N start K).length := by
    simp [first, rawFirstWriterSwitches]
  have htailLength : tail.length =
      (rawRepeatedWriterNovelTimes w N start K).length - 3 := by
    simp [tail, repeatedNoveltyChargeTail, List.length_drop]
  have htailUnused : tail.length <= unused.length := by
    omega
  let charges := unused.take tail.length
  have hchargesLength : charges.length = tail.length := by
    dsimp [charges]
    exact List.length_take_of_le htailUnused
  have hchargesNodup : charges.Nodup := by
    dsimp [charges, unused]
    exact List.Pairwise.take
      (rawUnusedFirstWriterSwitches_nodup w N start K)
  have hchargesBounded : forall C, C ∈ charges -> C < N := by
    intro C hC
    have hUnused : C ∈ unused := by
      dsimp [charges] at hC
      exact List.mem_of_mem_take hC
    exact (mem_rawUnusedFirstWriterSwitches_iff.mp (by
      simpa [unused] using hUnused)).1
  have hchargesUnused : forall C, C ∈ charges ->
      C ∉ rawFirstWriterSwitches w N start K := by
    intro C hC
    have hUnused : C ∈ unused := by
      dsimp [charges] at hC
      exact List.mem_of_mem_take hC
    exact (mem_rawUnusedFirstWriterSwitches_iff.mp (by
      simpa [unused] using hUnused)).2
  exact ⟨{
    charges := charges
    length_eq := by simpa [tail] using hchargesLength
    charges_nodup := hchargesNodup
    charges_bounded := hchargesBounded
    charges_unused := hchargesUnused
  }⟩

/-- The global charge formulation. -/
def AmortizedNoveltyChargeLaw : Prop :=
  forall (w : Wiring) (N : Nat),
    (forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N) ->
    forall (start : Nat × Tongues) (K : Nat),
      Nonempty (AmortizedNoveltyChargeCertificate w N start K)

theorem amortizedNovelty_iff_chargeLaw :
    AmortizedNoveltyNAddThreeTarget ↔ AmortizedNoveltyChargeLaw := by
  constructor
  · intro hamortized w N hN start K
    exact chargeCertificate_of_amortizedNovelty
      hN start K (hamortized w N hN start K)
  · intro hcharge w N hN start K
    exact amortizedNovelty_of_chargeCertificate
      hN start K (Classical.choice (hcharge w N hN start K))

/-! ## Canonical novelty sample and exact equivalence with `N+4` -/

noncomputable def rawNovelWriterTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List Nat :=
  rawFirstWriterTimes w N start K ++
    rawRepeatedWriterNovelTimes w N start K

theorem rawNovelWriterTimes_nodup
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawNovelWriterTimes w N start K).Nodup := by
  have hfirst := rawFirstWriterTimes_nodup_charge w N start K
  have hrepeat := rawRepeatedWriterNovelTimes_nodup w N start K
  apply List.nodup_append.mpr
  refine ⟨hfirst, hrepeat, ?_⟩
  intro i hi j hj hij
  subst j
  have hiData := mem_rawFirstWriterTimes_iff.mp hi
  have hjData := mem_rawRepeatedWriterNovelTimes_iff.mp hj
  exact hjData.2.2.1 hiData.2

theorem rawNovelWriterTimes_event_of_bounded
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (hk : k ∈ rawNovelWriterTimes w N start K) :
    RawProductiveAt w N start k ∧ RawNovelAt w N start k := by
  rcases List.mem_append.mp hk with hfirst | hrepeat
  · have hdata := mem_rawFirstWriterTimes_iff.mp hfirst
    exact ⟨hdata.2.1, rawFirstWriterAt_novel hN hdata.2⟩
  · have hdata := mem_rawRepeatedWriterNovelTimes_iff.mp hrepeat
    exact ⟨hdata.2.1, hdata.2.2.2⟩

/-- Time zero followed by every first-writer and repeated-novel post-time. -/
noncomputable def canonicalNoveltySampleTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    List Nat :=
  0 :: (rawNovelWriterTimes w N start K).map (fun k => k + 1)

theorem canonicalNoveltySampleTimes_live
    {w : Wiring} {N K : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) :
    forall t, t ∈ canonicalNoveltySampleTimes w N start K ->
      (stepN w t start).isSome := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | hpost
  · simp [stepN]
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hpost
    exact (rawNovelWriterTimes_event_of_bounded hN hk).1.1

theorem canonicalNoveltySampleVectors_nodup
    {w : Wiring} {N K : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    (start : Nat × Tongues) :
    ((canonicalNoveltySampleTimes w N start K).map
      (restrictedTonguesAt w N start)).Nodup := by
  let events := rawNovelWriterTimes w N start K
  have heventsNodup : events.Nodup := by
    dsimp [events]
    exact rawNovelWriterTimes_nodup w N start K
  have hpostNodup :
      (events.map (fun k =>
        restrictedTonguesAt w N start (k + 1))).Nodup := by
    apply anc_nodup_map_of_injective_on_mem heventsNodup
    intro i hi j hj hvector
    exact rawNovelAt_post_injective
      (rawNovelWriterTimes_event_of_bounded hN hi).2
      (rawNovelWriterTimes_event_of_bounded hN hj).2 hvector
  have hinitial : restrictedTonguesAt w N start 0 ∉
      events.map (fun k => restrictedTonguesAt w N start (k + 1)) := by
    intro hmem
    obtain ⟨k, hk, hvector⟩ := List.mem_map.mp hmem
    have hnovel := (rawNovelWriterTimes_event_of_bounded hN hk).2
    apply hnovel
    apply List.mem_map.mpr
    refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
    exact hvector.symm
  unfold canonicalNoveltySampleTimes
  simp only [List.map_cons, List.map_map, List.nodup_cons]
  exact ⟨hinitial, hpostNodup⟩

theorem canonicalNoveltySampleTimes_length
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (canonicalNoveltySampleTimes w N start K).length =
      (rawFirstWriterTimes w N start K).length +
        (rawRepeatedWriterNovelTimes w N start K).length + 1 := by
  simp [canonicalNoveltySampleTimes, rawNovelWriterTimes, Nat.add_assoc]

/-- Exact finite bookkeeping using the actual number of first writers. -/
theorem distinct_samples_le_of_amortizedNoveltyTarget
    (w : Wiring) (N : Nat)
    (start : Nat × Tongues) (K : Nat)
    (hbudget :
      (rawFirstWriterTimes w N start K).length +
        (rawRepeatedWriterNovelTimes w N start K).length <= N + 3)
    (times : List Nat)
    (htimes : forall k, k ∈ times -> k <= K)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length <= N + 4 := by
  let history := rawFirstWriterHistory w N start K
  let fresh := rawRepeatedWriterFresh w N start K
  have hhistory : history.length =
      (rawFirstWriterTimes w N start K).length + 1 := by
    simp [history, rawFirstWriterHistory]
  have hfresh : fresh.length =
      (rawRepeatedWriterNovelTimes w N start K).length := by
    simp [fresh, rawRepeatedWriterFresh]
  have hcover : NoveltyCoverOn w N start times history fresh.length := by
    refine ⟨fresh, Nat.le_refl _, ?_⟩
    intro k hk
    exact restrictedTonguesAt_mem_finite_writer_cover
      w N start K k (htimes k hk)
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  omega

/-- The amortized target implies the raw `N+4` target. -/
theorem stateLawNAddFourTarget_of_amortizedNovelty
    (hamortized : AmortizedNoveltyNAddThreeTarget) :
    StateLawNAddFourTarget := by
  intro w N hN start times _hlive hnd
  let K := maxRawTime times
  have htimes : forall k, k ∈ times -> k <= K := by
    intro k hk
    exact le_maxRawTime_of_mem hk
  have hnd' : (times.map
      (restrictedTonguesAt w N start)).Nodup := by
    change (times.map (fun k => VectorCount.restrict N
      ((stepN w k start).getD start).2)).Nodup
    exact hnd
  exact distinct_samples_le_of_amortizedNoveltyTarget
    w N start K (hamortized w N hN start K) times htimes hnd'

/-- Converse reduction: raw `N+4` forces `F+R <= N+3`. -/
theorem amortizedNovelty_of_stateLawNAddFourTarget
    (hsharp : StateLawNAddFourTarget) :
    AmortizedNoveltyNAddThreeTarget := by
  intro w N hN start K
  let times := canonicalNoveltySampleTimes w N start K
  have hlive : forall t, t ∈ times -> (stepN w t start).isSome := by
    dsimp [times]
    exact canonicalNoveltySampleTimes_live hN start
  have hnd : (times.map (fun k => VectorCount.restrict N
      ((stepN w k start).getD start).2)).Nodup := by
    change (times.map (restrictedTonguesAt w N start)).Nodup
    dsimp [times]
    exact canonicalNoveltySampleVectors_nodup hN start
  have hbound := hsharp w N hN start times hlive hnd
  have hlength := canonicalNoveltySampleTimes_length w N start K
  change times.length =
    (rawFirstWriterTimes w N start K).length +
      (rawRepeatedWriterNovelTimes w N start K).length + 1 at hlength
  omega

/-- Exact equivalence of the raw sharp law, amortized law, and charge law. -/
theorem stateLawNAddFourTarget_iff_amortizedNovelty :
    StateLawNAddFourTarget ↔ AmortizedNoveltyNAddThreeTarget := by
  exact ⟨amortizedNovelty_of_stateLawNAddFourTarget,
    stateLawNAddFourTarget_of_amortizedNovelty⟩

theorem stateLawNAddFourTarget_iff_chargeLaw :
    StateLawNAddFourTarget ↔ AmortizedNoveltyChargeLaw := by
  rw [stateLawNAddFourTarget_iff_amortizedNovelty,
    amortizedNovelty_iff_chargeLaw]

/-! ## Physical location of every still-required charge -/

/-- Every tail event contains a concrete productive self-pivot. At that
pivot the train-curve carrier cannot grow, its writer is one of at most two
current endpoint writers, and the writer stem is linked to the actual
post-pivot entry. -/
theorem repeatedNoveltyChargeTail_has_self_endpoint_pivot
    {w : Wiring} {N K right : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hright : right ∈ repeatedNoveltyChargeTail w N start K) :
    exists left pivot,
      RawLastWriterFrame w N start left right ∧
      left < pivot ∧ pivot <= right ∧
      RawProductiveAt w N start pivot ∧
      RawTrainCurveSelfAt w start pivot ∧
      rawFiniteCurveSizeAt w N start (pivot + 1) <=
        rawFiniteCurveSizeAt w N start pivot ∧
      rawWriterAt w start pivot ∈
        rawFiniteCurveEndpointWritersAt w N start pivot ∧
      (rawFiniteCurveEndpointWritersAt w N start pivot).length <= 2 ∧
      w.link (3 * rawWriterAt w start pivot) =
        some (rawEntryAt w start (pivot + 1)) := by
  have hrightAll : right ∈
      rawRepeatedWriterNovelTimes w N start K := by
    unfold repeatedNoveltyChargeTail at hright
    exact List.mem_of_mem_drop hright
  have hEvent := (mem_rawRepeatedWriterNovelTimes_iff.mp hrightAll).2
  obtain ⟨left, pivot, hframe, hleft, hpivot, hprod, hself, _⟩ :=
    hEvent.forced_self_strict_or_same_size hN
  have hnonincrease := rawProductiveAt_self_curve_nonincrease
    hN hprod hself
  have hendpoint := rawProductiveAt_writer_mem_endpointWritersAt
    hN hprod
  have hcap := rawFiniteCurveEndpointWritersAt_length_le_two
    w N start pivot
  obtain ⟨next, hnext, hedge⟩ :=
    rawProductiveAt_fixed_stem_successor hN hprod
  have hedge' : w.link (3 * rawWriterAt w start pivot) =
      some (rawEntryAt w start (pivot + 1)) := by
    simpa [rawEntryAt, hnext] using hedge
  exact ⟨left, pivot, hframe, hleft, hpivot, hprod, hself,
    hnonincrease, hendpoint, hcap, hedge'⟩

/-! ## A coefficient-one physical charge on reachable switch stems -/

/-- Reachable switch stems on the selected train curve at raw time `k`.
Unlike the earlier lost-port carrier, this list has capacity exactly `N`. -/
noncomputable def rawFiniteCurveStemsAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : List Nat :=
  let cur := (stepN w k start).getD start
  finiteCurveStems w N cur.2 cur.1

@[simp] theorem rawFiniteCurveStemsAt_length
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    (rawFiniteCurveStemsAt w N start k).length =
      rawFiniteCurveStemSizeAt w N start k := by
  rfl

/-- Stem membership is exactly membership of the corresponding physical
stem port in the full finite carrier. -/
theorem mem_rawFiniteCurveStemsAt_iff_stem_port
    {w : Wiring} {N C k : Nat} {start : Nat × Tongues} :
    C ∈ rawFiniteCurveStemsAt w N start k ↔
      3 * C ∈ rawFiniteCurvePortsAt w N start k := by
  let cur := (stepN w k start).getD start
  change C ∈ finiteCurveStems w N cur.2 cur.1 ↔
    3 * C ∈ finiteCurvePorts w N cur.2 cur.1
  rw [mem_finiteCurveStems_iff, mem_finiteCurvePorts_iff]
  constructor
  · intro h
    exact ⟨by omega, h.2⟩
  · intro h
    exact ⟨by omega, h.2⟩

/-- A productive self-pivot cannot add a reachable switch stem. -/
theorem rawProductiveAt_self_stems_subset
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hprod : RawProductiveAt w N start k)
    (hself : RawTrainCurveSelfAt w start k) :
    ∀ C, C ∈ rawFiniteCurveStemsAt w N start (k + 1) →
      C ∈ rawFiniteCurveStemsAt w N start k := by
  intro C hC
  have hpNew : 3 * C ∈ rawFiniteCurvePortsAt w N start (k + 1) :=
    mem_rawFiniteCurveStemsAt_iff_stem_port.mp hC
  have hpOld := raw_self_pivot_carrier_subset hN hprod
    (show RawCurveSelfAt w start k from hself) (3 * C) hpNew
  exact mem_rawFiniteCurveStemsAt_iff_stem_port.mpr hpOld

/-- A self-pivot which strictly removes at least one reachable switch stem.
This is the coefficient-one analogue of `RawStrictSelfShrinkAt`. -/
def RawStrictSelfStemShrinkAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Prop :=
  RawProductiveAt w N start k ∧
  RawTrainCurveSelfAt w start k ∧
  rawFiniteCurveStemSizeAt w N start (k + 1) <
    rawFiniteCurveStemSizeAt w N start k

/-- Every productive self-pivot either consumes stem potential or lies on a
stem-carrier plateau. -/
theorem raw_self_pivot_stem_strict_or_same_size
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hprod : RawProductiveAt w N start k)
    (hself : RawTrainCurveSelfAt w start k) :
    RawStrictSelfStemShrinkAt w N start k ∨
      rawFiniteCurveStemSizeAt w N start (k + 1) =
        rawFiniteCurveStemSizeAt w N start k := by
  have hle := rawProductiveAt_self_stem_nonincrease hN hprod
    (show RawCurveSelfAt w start k from hself)
  by_cases hlt : rawFiniteCurveStemSizeAt w N start (k + 1) <
      rawFiniteCurveStemSizeAt w N start k
  · exact Or.inl ⟨hprod, hself, hlt⟩
  · exact Or.inr (by omega)

/-- A strict stem shrink discards a literal switch coordinate from the
selected train component. -/
theorem RawStrictSelfStemShrinkAt.dropped_stem
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (h : RawStrictSelfStemShrinkAt w N start k) :
    ∃ C, C ∈ rawFiniteCurveStemsAt w N start k ∧
      C ∉ rawFiniteCurveStemsAt w N start (k + 1) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hsub : ∀ C, C ∈ rawFiniteCurveStemsAt w N start k →
      C ∈ rawFiniteCurveStemsAt w N start (k + 1) := by
    intro C hC
    apply Classical.byContradiction
    intro hCnew
    exact hnone ⟨C, hC, hCnew⟩
  have holdNodup : (rawFiniteCurveStemsAt w N start k).Nodup := by
    unfold rawFiniteCurveStemsAt
    exact finiteCurveStems_nodup w N
      ((stepN w k start).getD start).2
      ((stepN w k start).getD start).1
  have hle := anc_nodup_subset_length holdNodup hsub
  simp only [rawFiniteCurveStemsAt_length] at hle
  have hstrict := h.2.2
  omega

/-- Canonical coefficient-one switch charge chosen from the literal
old-stem/new-not-stem witness. -/
noncomputable def rawStrictSelfStemChargeOf
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Nat := by
  classical
  exact if h : ∃ C,
      C ∈ rawFiniteCurveStemsAt w N start k ∧
      C ∉ rawFiniteCurveStemsAt w N start (k + 1) then
    Classical.choose h
  else 0

theorem rawStrictSelfStemChargeOf_spec
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (h : RawStrictSelfStemShrinkAt w N start k) :
    rawStrictSelfStemChargeOf w N start k ∈
        rawFiniteCurveStemsAt w N start k ∧
      rawStrictSelfStemChargeOf w N start k ∉
        rawFiniteCurveStemsAt w N start (k + 1) := by
  unfold rawStrictSelfStemChargeOf
  have hexists := h.dropped_stem
  rw [dif_pos hexists]
  exact Classical.choose_spec hexists

theorem rawStrictSelfStemChargeOf_lt
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (h : RawStrictSelfStemShrinkAt w N start k) :
    rawStrictSelfStemChargeOf w N start k < N := by
  have hm := (rawStrictSelfStemChargeOf_spec h).1
  unfold rawFiniteCurveStemsAt at hm
  exact (mem_finiteCurveStems_iff.mp hm).1

/-- A repeated novelty whose closing event itself consumes a reachable
switch stem. -/
def RawNovelRepeatedStrictStemShrinkAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Prop :=
  RawRepeatedWriterNovelAt w N start k ∧
    RawStrictSelfStemShrinkAt w N start k

noncomputable def rawNovelRepeatedStrictStemShrinkTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter (fun k => decide
    (RawNovelRepeatedStrictStemShrinkAt w N start k))

theorem mem_rawNovelRepeatedStrictStemShrinkTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawNovelRepeatedStrictStemShrinkTimes w N start K ↔
      k < K ∧ RawNovelRepeatedStrictStemShrinkAt w N start k := by
  classical
  simp [rawNovelRepeatedStrictStemShrinkTimes]

/-- Concrete failure of injectivity of the stem charge, together with the
non-self restoration frame forced between the two losses. -/
structure RawStrictStemChargeRestoration
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : Type where
  first : Nat
  second : Nat
  first_mem : first ∈ rawNovelRepeatedStrictStemShrinkTimes w N start K
  second_mem : second ∈ rawNovelRepeatedStrictStemShrinkTimes w N start K
  order : first < second
  same_charge : rawStrictSelfStemChargeOf w N start first =
    rawStrictSelfStemChargeOf w N start second
  restore : Nat
  restore_after : first < restore
  restore_before : restore < second
  frame : RawPortRestorationFrame w N start first restore
    (3 * rawStrictSelfStemChargeOf w N start first)

private theorem anc_nodup_or_equal_pair
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) : ∀ {xs : List α}, xs.Nodup →
      (xs.map f).Nodup ∨
        ∃ a, a ∈ xs ∧ ∃ b, b ∈ xs ∧ a ≠ b ∧ f a = f b := by
  intro xs hxs
  induction xs with
  | nil => exact Or.inl (by simp)
  | cons a rest ih =>
      rw [List.nodup_cons] at hxs
      rcases ih hxs.2 with hrest | hpair
      · by_cases hmem : f a ∈ rest.map f
        · obtain ⟨b, hb, hEq⟩ := List.mem_map.mp hmem
          right
          refine ⟨a, List.mem_cons_self, b,
            List.mem_cons_of_mem _ hb, ?_, hEq.symm⟩
          intro hab
          exact hxs.1 (hab ▸ hb)
        · left
          simp only [List.map_cons, List.nodup_cons]
          exact ⟨hmem, hrest⟩
      · right
        obtain ⟨x, hx, y, hy, hxy, hEq⟩ := hpair
        exact ⟨x, List.mem_cons_of_mem _ hx,
          y, List.mem_cons_of_mem _ hy, hxy, hEq⟩

/-- Reusing one coefficient-one stem charge forces an intervening productive
non-self restoration. -/
theorem reused_strict_stem_charge_has_restoration
    {w : Wiring} {N i j : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hij : i < j)
    (hi : RawNovelRepeatedStrictStemShrinkAt w N start i)
    (hj : RawNovelRepeatedStrictStemShrinkAt w N start j)
    (heq : rawStrictSelfStemChargeOf w N start i =
      rawStrictSelfStemChargeOf w N start j) :
    ∃ restore, i < restore ∧ restore < j ∧
      RawPortRestorationFrame w N start i restore
        (3 * rawStrictSelfStemChargeOf w N start i) := by
  have hiSpec := rawStrictSelfStemChargeOf_spec hi.2
  have hjSpec := rawStrictSelfStemChargeOf_spec hj.2
  rw [← heq] at hjSpec
  have hiAbsentPort :
      3 * rawStrictSelfStemChargeOf w N start i ∉
        rawFiniteCurvePortsAt w N start (i + 1) := by
    intro hp
    exact hiSpec.2 (mem_rawFiniteCurveStemsAt_iff_stem_port.mpr hp)
  have hjPresentPort :
      3 * rawStrictSelfStemChargeOf w N start i ∈
        rawFiniteCurvePortsAt w N start j :=
    mem_rawFiniteCurveStemsAt_iff_stem_port.mp hjSpec.1
  have hjLive : (stepN w (j + 1) start).isSome := hj.2.1.1
  have hlive : ∀ k, k ≤ j → (stepN w k start).isSome := by
    intro k hk
    cases hfinish : stepN w (j + 1) start with
    | none => simp [hfinish] at hjLive
    | some finish =>
        obtain ⟨middle, hmiddle⟩ := stepN_prefix_some
          (d := k) (K := j + 1) (by omega) hfinish
        simp [hmiddle]
  exact lost_port_reuse_has_restoration_frame
    hN hij hlive hiAbsentPort hjPresentPort

/-- **Unconditional coefficient-one charge frontier.** Strict stem-shrink
novelties inject into the `N` switch coordinates, unless two losses of one
coordinate expose a literal intervening non-self restoration frame. -/
theorem strict_stem_charges_nodup_or_restoration
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) :
    let events := rawNovelRepeatedStrictStemShrinkTimes w N start K
    let charge := rawStrictSelfStemChargeOf w N start
    (events.map charge).Nodup ∨
      Nonempty (RawStrictStemChargeRestoration w N start K) := by
  classical
  dsimp only
  let events := rawNovelRepeatedStrictStemShrinkTimes w N start K
  let charge := rawStrictSelfStemChargeOf w N start
  have hevents : events.Nodup := by
    dsimp [events, rawNovelRepeatedStrictStemShrinkTimes]
    exact List.nodup_range.filter _
  rcases anc_nodup_or_equal_pair charge hevents with hnd | hpair
  · exact Or.inl hnd
  · right
    obtain ⟨i, hiMem, j, hjMem, hij, hEq⟩ := hpair
    have hiData := mem_rawNovelRepeatedStrictStemShrinkTimes_iff.mp
      (by simpa [events] using hiMem)
    have hjData := mem_rawNovelRepeatedStrictStemShrinkTimes_iff.mp
      (by simpa [events] using hjMem)
    by_cases hlt : i < j
    · obtain ⟨restore, hir, hrj, H⟩ :=
        reused_strict_stem_charge_has_restoration
          hN hlt hiData.2 hjData.2 (by simpa [charge] using hEq)
      exact ⟨{
        first := i
        second := j
        first_mem := by simpa [events] using hiMem
        second_mem := by simpa [events] using hjMem
        order := hlt
        same_charge := by simpa [charge] using hEq
        restore := restore
        restore_after := hir
        restore_before := hrj
        frame := H
      }⟩
    · have hjlt : j < i := by omega
      obtain ⟨restore, hjr, hri, H⟩ :=
        reused_strict_stem_charge_has_restoration
          hN hjlt hjData.2 hiData.2 (by simpa [charge] using hEq.symm)
      exact ⟨{
        first := j
        second := i
        first_mem := by simpa [events] using hjMem
        second_mem := by simpa [events] using hiMem
        order := hjlt
        same_charge := by simpa [charge] using hEq.symm
        restore := restore
        restore_after := hjr
        restore_before := hri
        frame := H
      }⟩

/-- Cardinal form of the same unconditional frontier. -/
theorem strict_stem_shrinks_le_N_or_restoration
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) :
    (rawNovelRepeatedStrictStemShrinkTimes w N start K).length ≤ N ∨
      Nonempty (RawStrictStemChargeRestoration w N start K) := by
  let events := rawNovelRepeatedStrictStemShrinkTimes w N start K
  let charge := rawStrictSelfStemChargeOf w N start
  rcases strict_stem_charges_nodup_or_restoration hN with
      hnd | hrestore
  · left
    have hbounded : ∀ C, C ∈ events.map charge → C < N := by
      intro C hC
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hC
      have hkData := mem_rawNovelRepeatedStrictStemShrinkTimes_iff.mp
        (by simpa [events] using hk)
      exact rawStrictSelfStemChargeOf_lt hkData.2.2
    have hle := nodup_nat_lt_length hnd hbounded
    simpa [events] using hle
  · exact Or.inr hrestore

/-! ## Exact physical residual for every event of `R.drop 3` -/

inductive RawTailPhysicalChargeShape
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (pivot : Nat) : Prop
  | stemShrink
      (strict : RawStrictSelfStemShrinkAt w N start pivot)
      (charge : Nat)
      (old_mem : charge ∈ rawFiniteCurveStemsAt w N start pivot)
      (new_not : charge ∉ rawFiniteCurveStemsAt w N start (pivot + 1))
  | endpointShrink
      (stem_plateau : rawFiniteCurveStemSizeAt w N start (pivot + 1) =
        rawFiniteCurveStemSizeAt w N start pivot)
      (strict : RawStrictSelfShrinkAt w N start pivot)
      (port : Nat)
      (old_mem : port ∈ rawFiniteCurvePortsAt w N start pivot)
      (new_not : port ∉ rawFiniteCurvePortsAt w N start (pivot + 1))
  | protectedPlateau
      (stem_plateau : rawFiniteCurveStemSizeAt w N start (pivot + 1) =
        rawFiniteCurveStemSizeAt w N start pivot)
      (port_plateau : rawFiniteCurveSizeAt w N start (pivot + 1) =
        rawFiniteCurveSizeAt w N start pivot)
      (endpoints_preserved : ∀ D,
        D ∈ rawFiniteCurveEndpointWritersAt w N start (pivot + 1) ↔
          D ∈ rawFiniteCurveEndpointWritersAt w N start pivot)

structure RawTailPhysicalCharge
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (right : Nat) : Type where
  left : Nat
  pivot : Nat
  frame : RawLastWriterFrame w N start left right
  after_left : left < pivot
  before_close : pivot ≤ right
  productive : RawProductiveAt w N start pivot
  self : RawTrainCurveSelfAt w start pivot
  shape : RawTailPhysicalChargeShape w N start pivot

/-- **Unconditional trichotomy for every still-unpaid repeated novelty.**
It either consumes one of the `N` reachable switch stems, consumes only a
physical endpoint fibre, or reaches an equal-carrier protected plateau with
the same two endpoint names. -/
theorem repeatedNoveltyChargeTail_physical_trichotomy
    {w : Wiring} {N K right : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hright : right ∈ repeatedNoveltyChargeTail w N start K) :
    Nonempty (RawTailPhysicalCharge w N start right) := by
  have hrightAll : right ∈
      rawRepeatedWriterNovelTimes w N start K := by
    unfold repeatedNoveltyChargeTail at hright
    exact List.mem_of_mem_drop hright
  have hEvent := (mem_rawRepeatedWriterNovelTimes_iff.mp hrightAll).2
  obtain ⟨left, pivot, hframe, hleft, hpivot, hprod, hself, _⟩ :=
    hEvent.forced_self_strict_or_same_size hN
  rcases raw_self_pivot_stem_strict_or_same_size hN hprod hself with
      hstemStrict | hstemPlateau
  · obtain ⟨C, hCold, hCnew⟩ := hstemStrict.dropped_stem
    exact ⟨{
      left := left
      pivot := pivot
      frame := hframe
      after_left := hleft
      before_close := hpivot
      productive := hprod
      self := hself
      shape := .stemShrink hstemStrict C hCold hCnew
    }⟩
  · rcases raw_self_pivot_strict_or_same_size hN hprod hself with
        hportStrict | hportPlateau
    · obtain ⟨p, hpOld, hpNew⟩ := hportStrict.dropped_carrier_port
      exact ⟨{
        left := left
        pivot := pivot
        frame := hframe
        after_left := hleft
        before_close := hpivot
        productive := hprod
        self := hself
        shape := .endpointShrink hstemPlateau hportStrict p hpOld hpNew
      }⟩
    · have hendpoints := raw_self_pivot_equal_size_endpoint_writers_iff
        hN hprod (show RawCurveSelfAt w start pivot from hself)
          hportPlateau
      exact ⟨{
        left := left
        pivot := pivot
        frame := hframe
        after_left := hleft
        before_close := hpivot
        productive := hprod
        self := hself
        shape := .protectedPlateau hstemPlateau hportPlateau hendpoints
      }⟩

/-! ## Exact endpoint-fibre and protected-retrace residuals -/

/-- At an endpoint-only shrink no switch stem is lost: every stem present
before the pivot is still present afterwards.  Thus its physical lost port
really lies in the two-branch fibre over an already retained switch. -/
theorem endpointShrink_stems_preserved
    {w : Wiring} {N pivot : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hprod : RawProductiveAt w N start pivot)
    (hself : RawTrainCurveSelfAt w start pivot)
    (hstemPlateau : rawFiniteCurveStemSizeAt w N start (pivot + 1) =
      rawFiniteCurveStemSizeAt w N start pivot) :
    ∀ C, C ∈ rawFiniteCurveStemsAt w N start (pivot + 1) ↔
      C ∈ rawFiniteCurveStemsAt w N start pivot := by
  classical
  have hsub := rawProductiveAt_self_stems_subset hN hprod hself
  have hnewNodup :
      (rawFiniteCurveStemsAt w N start (pivot + 1)).Nodup := by
    unfold rawFiniteCurveStemsAt
    exact finiteCurveStems_nodup w N
      ((stepN w (pivot + 1) start).getD start).2
      ((stepN w (pivot + 1) start).getD start).1
  intro C
  constructor
  · exact hsub C
  · intro hCold
    apply Classical.byContradiction
    intro hCnew
    have hconsNodup :
        (C :: rawFiniteCurveStemsAt w N start (pivot + 1)).Nodup := by
      rw [List.nodup_cons]
      exact ⟨hCnew, hnewNodup⟩
    have hconsSub : ∀ D,
        D ∈ C :: rawFiniteCurveStemsAt w N start (pivot + 1) →
          D ∈ rawFiniteCurveStemsAt w N start pivot := by
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact hCold
      · exact hsub D hD
    have hle := anc_nodup_subset_length hconsNodup hconsSub
    simp only [List.length_cons, rawFiniteCurveStemsAt_length,
      hstemPlateau] at hle
    omega

/-- If a self-pivot preserves the stem carrier but loses a physical port,
the lost port lies over one of the at-most-two endpoint writers of the old
train curve.  A non-endpoint switch would retain its stem and selected
branch, hence could not lose the port. -/
theorem endpointShrink_lost_port_is_endpoint_writer
    {w : Wiring} {N pivot port : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hprod : RawProductiveAt w N start pivot)
    (hself : RawTrainCurveSelfAt w start pivot)
    (hstemPlateau : rawFiniteCurveStemSizeAt w N start (pivot + 1) =
      rawFiniteCurveStemSizeAt w N start pivot)
    (hold : port ∈ rawFiniteCurvePortsAt w N start pivot)
    (hnew : port ∉ rawFiniteCurvePortsAt w N start (pivot + 1)) :
    port / 3 ∈ rawFiniteCurveEndpointWritersAt w N start pivot := by
  obtain ⟨cur, next, writer, hwriter, hcur, hnext, _hstep,
      _hentry, _hexit, hflip, _hback⟩ :=
    rawProductiveAt_is_endpoint_pivot hN hprod
  have hreach : CurveReach w cur.2 cur.1 port := by
    unfold rawFiniteCurvePortsAt at hold
    simp only [hcur, Option.getD_some] at hold
    exact (mem_finiteCurvePorts_iff.mp hold).2
  have hportLt : port < 3 * N := by
    unfold rawFiniteCurvePortsAt at hold
    simp only [hcur, Option.getD_some] at hold
    exact (mem_finiteCurvePorts_iff.mp hold).1
  let C := port / 3
  have hC : C < N := by
    dsimp [C]
    omega
  by_cases hCwriter : C = rawWriterAt w start pivot
  · change C ∈ rawFiniteCurveEndpointWritersAt w N start pivot
    rw [hCwriter]
    exact rawProductiveAt_writer_mem_endpointWritersAt hN hprod
  have hCwriter' : C ≠ writer := by
    intro hEq
    apply hCwriter
    rw [← hwriter, hEq]
  by_cases hpBranch : port % 3 ≠ 0
  · have hbranch : branchPort C (bval port) = port := by
      dsimp [C]
      exact branchPort_bval hpBranch
    by_cases hselected : cur.2 C = bval port
    · have hpSelected : selectedBranch cur.2 C = port := by
        unfold selectedBranch
        rw [hselected, hbranch]
      have hstemReach : CurveReach w cur.2 cur.1 (3 * C) := by
        have hedge : CurveReach w cur.2 port (3 * C) := by
          have hlocal : CurveReach w cur.2
              (selectedBranch cur.2 C) (3 * C) :=
            curveReach_edge (w := w)
              (Or.inr (arrive_selected_stem cur.2 C))
          simpa [hpSelected] using hlocal
        exact curveReach_trans hreach hedge
      have holdStem : C ∈ rawFiniteCurveStemsAt w N start pivot := by
        unfold rawFiniteCurveStemsAt
        simp only [hcur, Option.getD_some]
        rw [mem_finiteCurveStems_iff]
        exact ⟨hC, hstemReach⟩
      have hnewStem := (endpointShrink_stems_preserved
        hN hprod hself hstemPlateau C).2 holdStem
      have hnewStemPort :=
        mem_rawFiniteCurveStemsAt_iff_stem_port.mp hnewStem
      have hsameSelected : selectedBranch next.2 C = port := by
        rw [hflip]
        unfold selectedBranch
        simp [flipAt, hCwriter', hselected, hbranch]
      have hnewReachStem : CurveReach w next.2 next.1 (3 * C) := by
        unfold rawFiniteCurvePortsAt at hnewStemPort
        simp only [hnext, Option.getD_some] at hnewStemPort
        exact (mem_finiteCurvePorts_iff.mp hnewStemPort).2
      have hnewReachPort : CurveReach w next.2 next.1 port := by
        have hedge : CurveReach w next.2 (3 * C) port := by
          have hlocal : CurveReach w next.2
              (3 * C) (selectedBranch next.2 C) :=
            curveReach_edge (w := w)
              (Or.inr (arrive_stem_selected next.2 C))
          simpa [hsameSelected] using hlocal
        exact curveReach_trans hnewReachStem hedge
      exfalso
      apply hnew
      unfold rawFiniteCurvePortsAt
      simp only [hnext, Option.getD_some]
      rw [mem_finiteCurvePorts_iff]
      exact ⟨hportLt, hnewReachPort⟩
    · have hunmatched : unmatchedBranch cur.2 C = port := by
        unfold unmatchedBranch
        cases hc : cur.2 C <;>
          simp [branchPort, bval, hc] at hselected hbranch ⊢ <;>
          omega
      unfold rawFiniteCurveEndpointWritersAt
      simp only [hcur, Option.getD_some]
      rw [mem_finiteCurveEndpointWriters_iff]
      refine ⟨hC, ?_⟩
      rw [hunmatched]
      exact hreach
  · have hpStem : port = 3 * C := by
      dsimp [C]
      omega
    have holdStem : C ∈ rawFiniteCurveStemsAt w N start pivot := by
      apply mem_rawFiniteCurveStemsAt_iff_stem_port.mpr
      simpa [hpStem] using hold
    have hnewStem := (endpointShrink_stems_preserved
      hN hprod hself hstemPlateau C).2 holdStem
    exfalso
    apply hnew
    have hpNew := mem_rawFiniteCurveStemsAt_iff_stem_port.mp hnewStem
    simpa [hpStem] using hpNew

/-- The fully charged physical outcome for one event in `R.drop 3`.
The endpoint-only branch is now charged to a list of capacity two, while a
protected plateau names the productive endpoint in the same preserved list. -/
inductive RawTailChargedOutcome
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (right : Nat) : Type
  | stem
      (pivot charge : Nat)
      (strict : RawStrictSelfStemShrinkAt w N start pivot)
      (old_mem : charge ∈ rawFiniteCurveStemsAt w N start pivot)
      (new_not : charge ∉ rawFiniteCurveStemsAt w N start (pivot + 1))
      (charge_lt : charge < N)
  | endpoint
      (pivot port : Nat)
      (strict : RawStrictSelfShrinkAt w N start pivot)
      (old_mem : port ∈ rawFiniteCurvePortsAt w N start pivot)
      (new_not : port ∉ rawFiniteCurvePortsAt w N start (pivot + 1))
      (writer_mem : port / 3 ∈
        rawFiniteCurveEndpointWritersAt w N start pivot)
      (capacity :
        (rawFiniteCurveEndpointWritersAt w N start pivot).length ≤ 2)
  | plateau
      (pivot : Nat)
      (stem_plateau : rawFiniteCurveStemSizeAt w N start (pivot + 1) =
        rawFiniteCurveStemSizeAt w N start pivot)
      (port_plateau : rawFiniteCurveSizeAt w N start (pivot + 1) =
        rawFiniteCurveSizeAt w N start pivot)
      (writer_mem : rawWriterAt w start pivot ∈
        rawFiniteCurveEndpointWritersAt w N start pivot)
      (writer_mem_after : rawWriterAt w start pivot ∈
        rawFiniteCurveEndpointWritersAt w N start (pivot + 1))
      (capacity :
        (rawFiniteCurveEndpointWritersAt w N start pivot).length ≤ 2)

/-- Strengthen the raw trichotomy into actual coefficient-one/constant
charges.  The only branch without a consumed carrier element is now the
literal protected plateau. -/
theorem RawTailPhysicalCharge.toChargedOutcome
    {w : Wiring} {N right : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (T : RawTailPhysicalCharge w N start right) :
    Nonempty (RawTailChargedOutcome w N start right) := by
  cases T.shape with
  | stemShrink strict charge old_mem new_not =>
      have hchargeLt : charge < N := by
        unfold rawFiniteCurveStemsAt at old_mem
        exact (mem_finiteCurveStems_iff.mp old_mem).1
      exact Nonempty.intro
        (.stem T.pivot charge strict old_mem new_not hchargeLt)
  | endpointShrink stem_plateau strict port old_mem new_not =>
      have hwriter := endpointShrink_lost_port_is_endpoint_writer
        hN T.productive T.self stem_plateau old_mem new_not
      exact Nonempty.intro
        (.endpoint T.pivot port strict old_mem new_not hwriter
          (rawFiniteCurveEndpointWritersAt_length_le_two
            w N start T.pivot))
  | protectedPlateau stem_plateau port_plateau endpoints_preserved =>
      have hwriter := rawProductiveAt_writer_mem_endpointWritersAt
        hN T.productive
      have hwriterAfter := (endpoints_preserved
        (rawWriterAt w start T.pivot)).2 hwriter
      exact Nonempty.intro
        (.plateau T.pivot stem_plateau port_plateau hwriter
          hwriterAfter
          (rawFiniteCurveEndpointWritersAt_length_le_two
            w N start T.pivot))

theorem repeatedNoveltyChargeTail_charged_outcome
    {w : Wiring} {N K right : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hright : right ∈ repeatedNoveltyChargeTail w N start K) :
    Nonempty (RawTailChargedOutcome w N start right) := by
  obtain ⟨T⟩ := repeatedNoveltyChargeTail_physical_trichotomy hN hright
  exact T.toChargedOutcome hN

/-- A self-only continuation realizes at most four vectors total, hence at
most three novel post-vectors.  Therefore it has no unpaid event in
`R.drop 3`. -/
theorem RawSelfTailCertificate.repeatedNoveltyChargeTail_eq_nil
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    (T : RawSelfTailCertificate w N start K)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) :
    repeatedNoveltyChargeTail w N start K = [] := by
  let samples := canonicalNoveltySampleTimes w N start K
  have hsamplesBound : ∀ t, t ∈ samples → t ≤ K := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · omega
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
      unfold rawNovelWriterTimes at hk
      rcases List.mem_append.mp hk with hfirst | hrepeat
      · have hkData := mem_rawFirstWriterTimes_iff.mp hfirst
        omega
      · have hkData := mem_rawRepeatedWriterNovelTimes_iff.mp hrepeat
        omega
  have hsamplesNodup :
      (samples.map (restrictedTonguesAt w N start)).Nodup := by
    dsimp [samples]
    exact canonicalNoveltySampleVectors_nodup hN start
  have hfour := T.distinct_snapshots_le_four hN
    samples hsamplesBound hsamplesNodup
  have hlength := canonicalNoveltySampleTimes_length w N start K
  change samples.length =
    (rawFirstWriterTimes w N start K).length +
      (rawRepeatedWriterNovelTimes w N start K).length + 1 at hlength
  have hrepeat :
      (rawRepeatedWriterNovelTimes w N start K).length ≤ 3 := by
    omega
  cases htail : repeatedNoveltyChargeTail w N start K with
  | nil => rfl
  | cons x xs =>
      have hpositive : 0 <
          (repeatedNoveltyChargeTail w N start K).length := by
        rw [htail]
        simp
      unfold repeatedNoveltyChargeTail at hpositive
      rw [List.length_drop] at hpositive
      omega

/-- Consequently any nonempty unpaid tail in a live prefix forces a
productive non-self growth event.  This is the exact remaining separator
between the two-endpoint constant regime and the coefficient-one charge. -/
theorem repeatedNoveltyChargeTail_nonempty_forces_nonself
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome)
    (hnonempty : repeatedNoveltyChargeTail w N start K ≠ []) :
    ∃ k, k < K ∧ RawProductiveAt w N start k ∧
      ¬ RawCurveSelfAt w start k := by
  apply Classical.byContradiction
  intro hnone
  have hself : ∀ k, k < K → RawProductiveAt w N start k →
      RawCurveSelfAt w start k := by
    intro k hk hprod
    apply Classical.byContradiction
    intro hnot
    exact hnone ⟨k, hk, hprod, hnot⟩
  let T : RawSelfTailCertificate w N start K := {
    live := hlive
    self := hself
  }
  exact hnonempty (T.repeatedNoveltyChargeTail_eq_nil hN)




/-! ## The exact uncharged protected-plateau invariant -/

/-- If two represented vectors differ, some in-range tongue coordinate
differs.  This local copy is public to the amortized charging argument rather
than relying on the private parity helper in RepeatedNoveltyDecomposition. -/
private theorem anc_restrict_ne_has_coordinate
    {N : Nat} {u v : Tongues}
    (hne : VectorCount.restrict N u ≠ VectorCount.restrict N v) :
    ∃ C, C < N ∧ u C ≠ v C := by
  apply Classical.byContradiction
  intro hnone
  apply hne
  unfold VectorCount.restrict
  apply List.map_congr_left
  intro C hC
  apply Classical.byContradiction
  intro hneC
  exact hnone ⟨C, List.mem_range.mp hC, hneC⟩

/-- If a coordinate is not productively written on a live half-open
interval, its tongue is unchanged across that interval. -/
private theorem anc_tongueAt_eq_of_no_writer_interval
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start finish : Nat × Tongues} {first span : Nat}
    (hfinish : stepN w (first + span) start = some finish)
    (hno : ∀ j, first ≤ j → j < first + span →
      RawProductiveAt w N start j → rawWriterAt w start j ≠ C) :
    (tonguesAt w start (first + span)) C =
      (tonguesAt w start first) C := by
  induction span generalizing finish with
  | zero => simp
  | succ n ih =>
      have harith : first + (n + 1) = first + n + 1 := by omega
      have hprefix : ∃ middle,
          stepN w (first + n) start = some middle :=
        stepN_prefix_some
          (d := first + n) (K := first + (n + 1))
          (by omega) hfinish
      obtain ⟨middle, hmiddle⟩ := hprefix
      have hprev := ih hmiddle
        (fun j hj hbound hprod => hno j hj (by omega) hprod)
      have hlive : (stepN w (first + n + 1) start).isSome := by
        rw [← harith, hfinish]
        simp
      obtain ⟨cur, next, hcur, hnext, hstep⟩ :=
        live_successor_configs hlive
      have hcurEq : cur = middle := by
        exact (Option.some.inj (hmiddle.symm.trans hcur)).symm
      subst cur
      have hfinish' : stepN w (first + n + 1) start = some finish := by
        rwa [← harith]
      have hnextEq : next = finish := by
        exact Option.some.inj (hnext.symm.trans hfinish')
      subst next
      have hbit : finish.2 C = middle.2 C := by
        apply Classical.byContradiction
        intro hchange
        obtain ⟨hprod, hwriter⟩ :=
          raw_tongue_change_is_productive_writer
            hC hmiddle hfinish' hstep hchange
        exact hno (first + n) (by omega) (by omega) hprod hwriter
      calc
        (tonguesAt w start (first + (n + 1))) C = finish.2 C := by
          rw [harith]
          simp [tonguesAt, hfinish']
        _ = middle.2 C := hbit
        _ = (tonguesAt w start (first + n)) C := by
          simp [tonguesAt, hmiddle]
        _ = (tonguesAt w start first) C := hprev

/-- A changed coordinate over a live interval names an actual intervening
productive writer. -/
theorem raw_tongue_change_has_writer_between
    {w : Wiring} {N C : Nat} (hC : C < N)
    {start : Nat × Tongues} {first last : Nat}
    (horder : first ≤ last)
    (hlast : (stepN w last start).isSome)
    (hchange : (tonguesAt w start last) C ≠
      (tonguesAt w start first) C) :
    ∃ k, first ≤ k ∧ k < last ∧
      RawProductiveAt w N start k ∧ rawWriterAt w start k = C := by
  obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hlast
  let span := last - first
  have hsum : first + span = last := by
    dsimp [span]
    omega
  apply Classical.byContradiction
  intro hnone
  have hno : ∀ j, first ≤ j → j < first + span →
      RawProductiveAt w N start j → rawWriterAt w start j ≠ C := by
    intro j hjlo hjhi hprod hwriter
    apply hnone
    exact ⟨j, hjlo, by simpa [hsum] using hjhi, hprod, hwriter⟩
  have hstable := anc_tongueAt_eq_of_no_writer_interval
    hC (by simpa [hsum] using hfinish) hno
  apply hchange
  simpa [hsum] using hstable

/-- The exact protected-phase charge.

Fix any set of protected endpoint writers.  If two configurations have the
same phase on that set, then either their complete restricted tongue vectors
are equal (literal recurrence), or an intervening productive write names a
switch outside the protected set.  There is no third source of plateau
novelty. -/
theorem endpointPhase_recurrence_or_foreign_charge
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {first last : Nat} (endpoints : List Nat)
    (horder : first ≤ last)
    (hlast : (stepN w last start).isSome)
    (hphase : ∀ C, C ∈ endpoints →
      (tonguesAt w start last) C = (tonguesAt w start first) C) :
    restrictedTonguesAt w N start last =
        restrictedTonguesAt w N start first ∨
      ∃ C, C < N ∧ C ∉ endpoints ∧
        ∃ k, first ≤ k ∧ k < last ∧
          RawProductiveAt w N start k ∧ rawWriterAt w start k = C := by
  by_cases hrec : restrictedTonguesAt w N start last =
      restrictedTonguesAt w N start first
  · exact Or.inl hrec
  · right
    have hvector : VectorCount.restrict N (tonguesAt w start last) ≠
        VectorCount.restrict N (tonguesAt w start first) := by
      simpa [restrictedTonguesAt] using hrec
    obtain ⟨C, hC, hchange⟩ :=
      anc_restrict_ne_has_coordinate hvector
    have houtside : C ∉ endpoints := by
      intro hmem
      exact hchange (hphase C hmem)
    obtain ⟨k, hklo, hkhi, hprod, hwriter⟩ :=
      raw_tongue_change_has_writer_between
        hC horder hlast hchange
    exact ⟨C, hC, houtside, k, hklo, hkhi, hprod, hwriter⟩

/-- If no productive write leaves the protected endpoint set, matching the
endpoint phase forces literal recurrence of the full restricted vector. -/
theorem endpointPhase_no_foreign_writer_forces_recurrence
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {first last : Nat} (endpoints : List Nat)
    (horder : first ≤ last)
    (hlast : (stepN w last start).isSome)
    (hphase : ∀ C, C ∈ endpoints →
      (tonguesAt w start last) C = (tonguesAt w start first) C)
    (hinside : ∀ k, first ≤ k → k < last →
      RawProductiveAt w N start k →
      rawWriterAt w start k ∈ endpoints) :
    restrictedTonguesAt w N start last =
      restrictedTonguesAt w N start first := by
  rcases endpointPhase_recurrence_or_foreign_charge
      endpoints horder hlast hphase with hrec |
      ⟨C, _hC, houtside, k, hklo, hkhi, hprod, hwriter⟩
  · exact hrec
  · have hmem := hinside k hklo hkhi hprod
    rw [hwriter] at hmem
    exact (houtside hmem).elim

/-- Protected-plateau specialization.  An equal-carrier self pivot preserves
an endpoint set of capacity two.  Reusing a phase on that pair therefore
either repeats the complete vector or exports a concrete productive charge to
a foreign switch.  Globally injecting those exported charges, or proving
recurrence when one is recycled, is the remaining sharp invariant. -/
theorem protectedPlateau_recycled_phase_recurrence_or_foreign_charge
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {pivot first last : Nat}
    (hprod : RawProductiveAt w N start pivot)
    (hself : RawCurveSelfAt w start pivot)
    (hplateau : rawFiniteCurveSizeAt w N start (pivot + 1) =
      rawFiniteCurveSizeAt w N start pivot)
    (horder : first ≤ last)
    (hlast : (stepN w last start).isSome)
    (hphase : ∀ C,
      C ∈ rawFiniteCurveEndpointWritersAt w N start pivot →
      (tonguesAt w start last) C = (tonguesAt w start first) C) :
    (∀ D,
      D ∈ rawFiniteCurveEndpointWritersAt w N start (pivot + 1) ↔
        D ∈ rawFiniteCurveEndpointWritersAt w N start pivot) ∧
    (rawFiniteCurveEndpointWritersAt w N start pivot).length ≤ 2 ∧
    (restrictedTonguesAt w N start last =
        restrictedTonguesAt w N start first ∨
      ∃ C, C < N ∧
        C ∉ rawFiniteCurveEndpointWritersAt w N start pivot ∧
        ∃ k, first ≤ k ∧ k < last ∧
          RawProductiveAt w N start k ∧
          rawWriterAt w start k = C) := by
  exact ⟨raw_self_pivot_equal_size_endpoint_writers_iff
      hN hprod hself hplateau,
    rawFiniteCurveEndpointWritersAt_length_le_two
      w N start pivot,
    endpointPhase_recurrence_or_foreign_charge
      (rawFiniteCurveEndpointWritersAt w N start pivot)
      horder hlast hphase⟩

end GeneralN

namespace GeneralN

/-- Endpoint writers can only disappear throughout a half-open interval
whose productive steps are all train-curve self pivots. -/
private theorem anc_endpointWriters_subset_self_interval
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {first span : Nat}
    (hlive : (stepN w (first + span) start).isSome)
    (hself : ∀ k, first ≤ k → k < first + span →
      RawProductiveAt w N start k → RawCurveSelfAt w start k) :
    ∀ D,
      D ∈ rawFiniteCurveEndpointWritersAt w N start (first + span) →
      D ∈ rawFiniteCurveEndpointWritersAt w N start first := by
  induction span with
  | zero =>
      intro D hD
      simpa using hD
  | succ n ih =>
      have harith : first + (n + 1) = first + n + 1 := by omega
      have hlastLive : (stepN w (first + n + 1) start).isSome := by
        simpa [harith] using hlive
      have hstepSubset :=
        rawSelfOnlyStep_endpointWriters_subset hN hlastLive
          (fun hprod => hself (first + n) (by omega) (by omega) hprod)
      obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hlive
      obtain ⟨middle, hmiddle⟩ := stepN_prefix_some
        (d := first + n) (K := first + (n + 1))
        (by omega) hfinish
      have hprefixLive : (stepN w (first + n) start).isSome := by
        simp [hmiddle]
      intro D hD
      have hprev : D ∈
          rawFiniteCurveEndpointWritersAt w N start (first + n) := by
        apply hstepSubset D
        simpa [harith] using hD
      exact ih hprefixLive
        (fun k hklo hkhi hprod =>
          hself k hklo (by omega) hprod)
        D hprev

/-- A new endpoint writer appearing over a live interval forces a concrete
productive non-self pivot in that interval.  Thus changing the protected
endpoint pair is itself a physical restoration/growth charge. -/
theorem endpointWriter_appearance_forces_nonself_between
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {first last D : Nat}
    (horder : first ≤ last)
    (hlast : (stepN w last start).isSome)
    (hlater : D ∈ rawFiniteCurveEndpointWritersAt w N start last)
    (hearlier : D ∉ rawFiniteCurveEndpointWritersAt w N start first) :
    ∃ k, first ≤ k ∧ k < last ∧
      RawProductiveAt w N start k ∧
      ¬ RawCurveSelfAt w start k := by
  let span := last - first
  have hsum : first + span = last := by
    dsimp [span]
    omega
  apply Classical.byContradiction
  intro hnone
  have hself : ∀ k, first ≤ k → k < first + span →
      RawProductiveAt w N start k → RawCurveSelfAt w start k := by
    intro k hklo hkhi hprod
    apply Classical.byContradiction
    intro hnot
    apply hnone
    exact ⟨k, hklo, by simpa [hsum] using hkhi, hprod, hnot⟩
  apply hearlier
  exact anc_endpointWriters_subset_self_interval
    (w := w) (N := N) (start := start)
    (first := first) (span := span)
    hN (by simpa [hsum] using hlast) hself D
    (by simpa [hsum] using hlater)

/-- At a protected plateau, a globally novel later state which reuses an
earlier endpoint phase cannot be a local two-endpoint novelty: it exports an
actual productive write to a foreign switch. -/
theorem protectedPlateau_novel_recycled_phase_exports_foreign_charge
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues} {pivot earlier right : Nat}
    (hprod : RawProductiveAt w N start pivot)
    (hself : RawCurveSelfAt w start pivot)
    (hplateau : rawFiniteCurveSizeAt w N start (pivot + 1) =
      rawFiniteCurveSizeAt w N start pivot)
    (hright : RawRepeatedWriterNovelAt w N start right)
    (hearlier : earlier < right + 1)
    (hphase : ∀ C,
      C ∈ rawFiniteCurveEndpointWritersAt w N start pivot →
      (tonguesAt w start (right + 1)) C =
        (tonguesAt w start earlier) C) :
    (∀ D,
      D ∈ rawFiniteCurveEndpointWritersAt w N start (pivot + 1) ↔
        D ∈ rawFiniteCurveEndpointWritersAt w N start pivot) ∧
    (rawFiniteCurveEndpointWritersAt w N start pivot).length ≤ 2 ∧
    ∃ C, C < N ∧
      C ∉ rawFiniteCurveEndpointWritersAt w N start pivot ∧
      ∃ k, earlier ≤ k ∧ k < right + 1 ∧
        RawProductiveAt w N start k ∧
        rawWriterAt w start k = C := by
  have H := protectedPlateau_recycled_phase_recurrence_or_foreign_charge
    hN hprod hself hplateau
      (show earlier ≤ right + 1 by omega)
      hright.1.1 hphase
  refine ⟨H.1, H.2.1, ?_⟩
  rcases H.2.2 with hrec | hforeign
  · exfalso
    apply hright.2.2
    apply List.mem_map.mpr
    exact ⟨earlier, List.mem_range.mpr hearlier, hrec.symm⟩
  · exact hforeign

