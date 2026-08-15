import KoizumiFramePersistence
import SelfEpochFour

/-!
# Self-pivot shrinkage and the serial one-shot obstruction

This file isolates the raw facts needed by the sharp finite-alternation
argument.

First, every globally novel repeated-writer frame contains a productive
self-pivot.  At that pivot the represented train curve either becomes
strictly smaller or keeps exactly the same finite carrier.  This is the
precise, non-vacuous size dichotomy; no future-tail premise is hidden in the
equal-size branch.

Second, the tempting serial `C,D,C` one-shot construction cannot hand the
train forward to an independent copy when its physical passage trace is
switch-simple.  The immutable external matching gives the general
cycle-or-retrace fork; because the two `C` visits are productive, both leave
through the same stem and the exact `C,D,C` case is forced into the absorbing
cycle branch.

Third, equal size is upgraded to equality of the complete physical carrier
and equality of its at-most-two endpoint-writer names.  In the strict branch
a concrete discarded port remains train-free throughout every self-only
continuation.

Thus any alleged forward concatenation must already repeat a switch passage
inside the first gadget.  That repeated passage is exactly the
interlacement/nesting contact consumed by the raw novelty-frame programme.

Finally, `rawNovelRepeatedStrictShrinks_le_three_mul` proves the global
`3*N` charge bound from one exact raw restoration statement:
`ReusedNovelStrictShrinkPortForcesReplay`.  The file still does not claim
`FiveRepeatedWriterNovelty`; that replay statement and the separately named
equal-size obligation `NovelEqualSelfPivotEntersEndpointEpoch` remain open.
-/

namespace GeneralN

/-! ## A forced self-pivot has a genuine finite-carrier dichotomy -/

/-- A productive self-pivot which strictly reduces the represented finite
train-curve carrier. -/
def RawStrictSelfShrinkAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Prop :=
  RawProductiveAt w N start k ∧
  RawTrainCurveSelfAt w start k ∧
  rawFiniteCurveSizeAt w N start (k + 1) <
    rawFiniteCurveSizeAt w N start k


structure RawSelfTailCertificate
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : Prop where
  live : ∀ k, k ≤ K → (stepN w k start).isSome
  self : ∀ k, k < K → RawProductiveAt w N start k →
    RawCurveSelfAt w start k

/-- A certified self-only continuation has at most four distinct visible
tongue vectors, with no recurrence or planarity hypothesis. -/
theorem RawSelfTailCertificate.distinct_snapshots_le_four
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    (T : RawSelfTailCertificate w N start K)
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (ks : List Nat) (hks : ∀ k, k ∈ ks → k ≤ K)
    (hnd : (ks.map (restrictedTonguesAt w N start)).Nodup) :
    ks.length ≤ 4 := by
  exact rawSelfOnlyEpoch_distinct_snapshots_le_four
    hN start K T.live T.self ks hks hnd

noncomputable def rawFiniteCurvePortsAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : List Nat :=
  let cur := (stepN w k start).getD start
  finiteCurvePorts w N cur.2 cur.1

@[simp] theorem rawFiniteCurvePortsAt_length
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) :
    (rawFiniteCurvePortsAt w N start k).length =
      rawFiniteCurveSizeAt w N start k := by
  rfl

/-- Pointwise raw form of self-pivot shrinkage: the post-pivot carrier is a
subset of the pre-pivot carrier.  Keeping the set statement explicit is
essential in the equal-size branch, where cardinality alone would hide a
possible rerooting. -/
theorem raw_self_pivot_carrier_subset
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


theorem raw_nonproductive_carrier_subset
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hlive : (stepN w (k + 1) start).isSome)
    (hnot : ¬ RawProductiveAt w N start k) :
    ∀ p, p ∈ rawFiniteCurvePortsAt w N start (k + 1) →
      p ∈ rawFiniteCurvePortsAt w N start k := by
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
  intro p hp
  unfold rawFiniteCurvePortsAt at hp ⊢
  simp only [hcur, hnext, Option.getD_some] at hp ⊢
  rw [mem_finiteCurvePorts_iff] at hp ⊢
  rw [hstate] at hp
  exact ⟨hp.1, curveReach_trans hcurNext hp.2⟩


theorem RawStrictSelfShrinkAt.dropped_carrier_port
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {k : Nat}
    (h : RawStrictSelfShrinkAt w N start k) :
    ∃ p, p ∈ rawFiniteCurvePortsAt w N start k ∧
      p ∉ rawFiniteCurvePortsAt w N start (k + 1) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hsub : ∀ p, p ∈ rawFiniteCurvePortsAt w N start k →
      p ∈ rawFiniteCurvePortsAt w N start (k + 1) := by
    intro p hp
    apply Classical.byContradiction
    intro hpnew
    exact hnone ⟨p, hp, hpnew⟩
  have hnd : (rawFiniteCurvePortsAt w N start k).Nodup := by
    exact finiteCurvePorts_nodup w N
      ((stepN w k start).getD start).2
      ((stepN w k start).getD start).1
  have hle : (rawFiniteCurvePortsAt w N start k).length ≤
      (rawFiniteCurvePortsAt w N start (k + 1)).length :=
    nodup_subset_length_nat hnd hsub
  rw [rawFiniteCurvePortsAt_length,
    rawFiniteCurvePortsAt_length] at hle
  exact (Nat.not_lt_of_ge hle) h.2.2

def RawNovelRepeatedStrictShrinkAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Prop :=
  RawRepeatedWriterNovelAt w N start k ∧
    RawStrictSelfShrinkAt w N start k

/-- Such strict-shrink novelty times in the half-open prefix `[0, K)`. -/
noncomputable def rawNovelRepeatedStrictShrinkTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (List.range K).filter (fun k => decide
    (RawNovelRepeatedStrictShrinkAt w N start k))

theorem mem_rawNovelRepeatedStrictShrinkTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawNovelRepeatedStrictShrinkTimes w N start K ↔
      k < K ∧ RawNovelRepeatedStrictShrinkAt w N start k := by
  classical
  simp [rawNovelRepeatedStrictShrinkTimes]

/-- Choose one concrete old-carrier port discarded by a strict self-shrink.
The value outside strict-shrink events is irrelevant. -/
noncomputable def rawNovelStrictShrinkCharge
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Nat := by
  classical
  exact if h : RawStrictSelfShrinkAt w N start k then
      Classical.choose h.dropped_carrier_port
    else 0

theorem rawNovelStrictShrinkCharge_spec
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (h : RawStrictSelfShrinkAt w N start k) :
    rawNovelStrictShrinkCharge w N start k ∈
        rawFiniteCurvePortsAt w N start k ∧
      rawNovelStrictShrinkCharge w N start k ∉
        rawFiniteCurvePortsAt w N start (k + 1) := by
  unfold rawNovelStrictShrinkCharge
  rw [dif_pos h]
  exact Classical.choose_spec h.dropped_carrier_port

/-- **Exact raw restoration hypothesis.**  If one physical carrier port is
discarded by two chronologically distinct globally novel repeated-writer
strict shrinks, then the later post-vector already occurred earlier.

This statement contains no compiler, curve certificate, charge function, or
counting conclusion.  Proving it is exactly the missing global
track-matching obstruction: re-entering a previously train-free subcurve
must restore a prior visible vector. -/
def ReusedNovelStrictShrinkPortForcesReplay
    (w : Wiring) (N : Nat) (start : Nat × Tongues) : Prop :=
  ∀ {i j p : Nat}, i < j →
    RawNovelRepeatedStrictShrinkAt w N start i →
    RawNovelRepeatedStrictShrinkAt w N start j →
    p ∈ rawFiniteCurvePortsAt w N start i →
    p ∉ rawFiniteCurvePortsAt w N start (i + 1) →
    p ∈ rawFiniteCurvePortsAt w N start j →
    p ∉ rawFiniteCurvePortsAt w N start (j + 1) →
    restrictedTonguesAt w N start (j + 1) ∈
      (List.range (j + 1)).map (restrictedTonguesAt w N start)

theorem rawNovelStrictShrinkCharge_injective
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (hreplay : ReusedNovelStrictShrinkPortForcesReplay w N start)
    {i j : Nat}
    (hi : RawNovelRepeatedStrictShrinkAt w N start i)
    (hj : RawNovelRepeatedStrictShrinkAt w N start j)
    (hcharge : rawNovelStrictShrinkCharge w N start i =
      rawNovelStrictShrinkCharge w N start j) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  by_cases hlt : i < j
  · have hiSpec := rawNovelStrictShrinkCharge_spec hi.2
    have hjSpec := rawNovelStrictShrinkCharge_spec hj.2
    rw [← hcharge] at hjSpec
    have hprior := hreplay hlt hi hj
      hiSpec.1 hiSpec.2 hjSpec.1 hjSpec.2
    exact (hj.1.2.2 hprior).elim
  · have hji : j < i := by omega
    have hiSpec := rawNovelStrictShrinkCharge_spec hi.2
    have hjSpec := rawNovelStrictShrinkCharge_spec hj.2
    rw [hcharge] at hiSpec
    have hprior := hreplay hji hj hi
      hjSpec.1 hjSpec.2 hiSpec.1 hiSpec.2
    exact (hi.1.2.2 hprior).elim

private theorem map_nodup_of_injective_on_mem_self_pivot
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) : ∀ {xs : List α}, xs.Nodup →
      (∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) →
      (xs.map f).Nodup := by
  intro xs hnd hinj
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
      · exact ih hnd.2
          (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx)
            y (List.mem_cons_of_mem _ hy))

/-- **Global strict-shrink charge/termination theorem.**  Once the exact raw
reuse-implies-replay statement is supplied, globally novel repeated-writer
strict shrinks inject into the `3*N` physical ports.  Hence no finite run can
contain more than `3*N` of them.

The sole unproved input is `ReusedNovelStrictShrinkPortForcesReplay`; the
cardinality and termination argument below is unconditional Lean. -/
theorem rawNovelRepeatedStrictShrinks_le_three_mul
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (hreplay : ReusedNovelStrictShrinkPortForcesReplay w N start)
    (K : Nat) :
    (rawNovelRepeatedStrictShrinkTimes w N start K).length ≤ 3 * N := by
  classical
  let events := rawNovelRepeatedStrictShrinkTimes w N start K
  let charge := rawNovelStrictShrinkCharge w N start
  have heventsNodup : events.Nodup := by
    dsimp [events, rawNovelRepeatedStrictShrinkTimes]
    exact List.nodup_range.filter _
  have hchargesNodup : (events.map charge).Nodup := by
    apply map_nodup_of_injective_on_mem_self_pivot charge heventsNodup
    intro i hi j hj hEq
    have hiData := mem_rawNovelRepeatedStrictShrinkTimes_iff.mp hi
    have hjData := mem_rawNovelRepeatedStrictShrinkTimes_iff.mp hj
    exact rawNovelStrictShrinkCharge_injective hreplay
      hiData.2 hjData.2 hEq
  have hchargeBound : ∀ p, p ∈ events.map charge → p < 3 * N := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hkData := mem_rawNovelRepeatedStrictShrinkTimes_iff.mp hk
    have hspec := rawNovelStrictShrinkCharge_spec hkData.2.2
    unfold rawFiniteCurvePortsAt at hspec
    exact (mem_finiteCurvePorts_iff.mp hspec.1).1
  have hle := nodup_subset_length_nat hchargesNodup
    (fun p hp => List.mem_range.mpr (hchargeBound p hp))
  dsimp [events, charge] at hle ⊢
  simpa only [List.length_map, List.length_range] using hle

end GeneralN
