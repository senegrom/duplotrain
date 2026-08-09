import SelfEpochAmortization

/-!
# Closing the physical-port side of the self-shrink charge

This file proves the unconditional raw statement which sits immediately
before the still-open global nesting argument.

A port discarded by a strict self-pivot cannot re-enter the represented
train curve through a quiet step or through another self-pivot: both kinds
of step make the represented carrier smaller.  Consequently, if the same
physical port is present at a later strict shrink, some intervening step is
a productive non-self pivot and strictly enlarges the carrier.  We package
that event as a raw restoration frame.

For a finite list of globally novel repeated-writer strict shrinks, either
the canonical lost-port charges are duplicate-free, or two charged shrinks
are joined by such a restoration frame.  Thus reuse has been reduced to an
actual raw restoration event; it is not hidden in a cardinality premise.

This does not claim `StateLaw`.  The remaining global theorem must charge
the resulting restoration frames injectively (or show that their reuse
enters a permanent self-only tail).
-/

namespace GeneralN

/-- A carrier port which is absent at raw time `restore` and present one
step later has been restored at `restore`.  The remaining fields record the
physical fact that this transition is necessarily a productive non-self
pivot and hence a strict carrier growth. -/
structure RawPortRestorationAt
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (restore port : Nat) : Prop where
  absent_before : port ∉ rawFiniteCurvePortsAt w N start restore
  present_after : port ∈ rawFiniteCurvePortsAt w N start (restore + 1)
  productive : RawProductiveAt w N start restore
  nonself : ¬ RawCurveSelfAt w start restore
  strict_growth :
    rawFiniteCurveSizeAt w N start restore <
      rawFiniteCurveSizeAt w N start (restore + 1)

/-- A concrete loss/restoration interval for one physical carrier port. -/
structure RawPortRestorationFrame
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (lost restore port : Nat) : Prop where
  order : lost < restore
  lost_after : port ∉ rawFiniteCurvePortsAt w N start (lost + 1)
  restored : RawPortRestorationAt w N start restore port

/-! ## A finite false-to-true boundary -/

private theorem exists_false_true_boundary
    (P : Nat → Prop) [DecidablePred P] (a : Nat) :
    ∀ d, ¬ P a → P (a + d) →
      ∃ r, a ≤ r ∧ r < a + d ∧ ¬ P r ∧ P (r + 1) := by
  intro d
  induction d with
  | zero =>
      intro ha hb
      exact (ha (by simpa using hb)).elim
  | succ d ih =>
      intro ha hb
      by_cases hprev : P (a + d)
      · obtain ⟨r, har, hrd, hr0, hr1⟩ := ih ha hprev
        exact ⟨r, har, by omega, hr0, hr1⟩
      · refine ⟨a + d, by omega, by omega, hprev, ?_⟩
        simpa [Nat.add_assoc] using hb

/-! ## Re-entry forces productive non-self growth -/

/-- If a represented carrier port is absent at one time and present later,
one intervening raw step restores it.  That step is productively non-self;
quiet steps and self-pivots are excluded by carrier monotonicity. -/
theorem absent_port_restored_by_nonself_growth
    {w : Wiring} {N a later port : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (horder : a < later)
    (hlive : ∀ k, k ≤ later → (stepN w k start).isSome)
    (habsent : port ∉ rawFiniteCurvePortsAt w N start a)
    (hpresent : port ∈ rawFiniteCurvePortsAt w N start later) :
    ∃ restore, a ≤ restore ∧ restore < later ∧
      RawPortRestorationAt w N start restore port := by
  let d := later - a
  have hlater : a + d = later := by
    dsimp [d]
    omega
  have hboundary := exists_false_true_boundary
    (fun k => port ∈ rawFiniteCurvePortsAt w N start k) a d
    habsent (by simpa [hlater] using hpresent)
  obtain ⟨restore, ha, hlt, hbefore, hafter⟩ := hboundary
  have hrestoreLt : restore < later := by omega
  have hrestoreLive : (stepN w (restore + 1) start).isSome :=
    hlive (restore + 1) (by omega)
  have hprod : RawProductiveAt w N start restore := by
    apply Classical.byContradiction
    intro hquiet
    have hsubset := raw_nonproductive_carrier_subset
      hN hrestoreLive hquiet port hafter
    exact hbefore hsubset
  have hnonself : ¬ RawCurveSelfAt w start restore := by
    intro hself
    have hsubset := raw_self_pivot_carrier_subset
      hN hprod hself port hafter
    exact hbefore hsubset
  refine ⟨restore, ha, hrestoreLt, ?_⟩
  exact {
    absent_before := hbefore
    present_after := hafter
    productive := hprod
    nonself := hnonself
    strict_growth := rawProductiveAt_nonself_curve_growth
      hN hprod hnonself
  }

/-- A concrete port discarded at `lost` and present again at `later`
determines an intervening raw restoration frame. -/
theorem lost_port_reuse_has_restoration_frame
    {w : Wiring} {N lost later port : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (horder : lost < later)
    (hlive : ∀ k, k ≤ later → (stepN w k start).isSome)
    (hlost : port ∉ rawFiniteCurvePortsAt w N start (lost + 1))
    (hreused : port ∈ rawFiniteCurvePortsAt w N start later) :
    ∃ restore, lost < restore ∧ restore < later ∧
      RawPortRestorationFrame w N start lost restore port := by
  have hgap : lost + 1 < later := by
    by_cases heq : lost + 1 = later
    · subst later
      exact (hlost hreused).elim
    · omega
  obtain ⟨restore, hlo, hhi, H⟩ :=
    absent_port_restored_by_nonself_growth hN hgap hlive hlost hreused
  exact ⟨restore, by omega, hhi, {
    order := by omega
    lost_after := hlost
    restored := H
  }⟩

/-- Reusing the same canonical physical charge at two chronologically
ordered globally novel strict shrinks exposes a productive non-self
restoration frame strictly between them. -/
theorem reused_novel_strict_shrink_charge_has_restoration_frame
    {w : Wiring} {N i j : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hij : i < j)
    (hlive : ∀ k, k ≤ j → (stepN w k start).isSome)
    (hi : RawNovelRepeatedStrictShrinkAt w N start i)
    (hj : RawNovelRepeatedStrictShrinkAt w N start j)
    (heq : rawNovelStrictShrinkCharge w N start i =
      rawNovelStrictShrinkCharge w N start j) :
    ∃ restore, i < restore ∧ restore < j ∧
      RawPortRestorationFrame w N start i restore
        (rawNovelStrictShrinkCharge w N start i) := by
  have hiSpec := rawNovelStrictShrinkCharge_spec hi.2
  have hjSpec := rawNovelStrictShrinkCharge_spec hj.2
  rw [← heq] at hjSpec
  exact lost_port_reuse_has_restoration_frame
    hN hij hlive hiSpec.2 hjSpec.1

/-- A reused charge necessarily leaves the self-only regime between its two
losses.  In particular, reuse does *not* itself imply the four-state tail;
it supplies the productive non-self escape which a later global argument
must charge. -/
theorem reused_novel_strict_shrink_charge_forces_nonself_between
    {w : Wiring} {N i j : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hij : i < j)
    (hlive : ∀ k, k ≤ j → (stepN w k start).isSome)
    (hi : RawNovelRepeatedStrictShrinkAt w N start i)
    (hj : RawNovelRepeatedStrictShrinkAt w N start j)
    (heq : rawNovelStrictShrinkCharge w N start i =
      rawNovelStrictShrinkCharge w N start j) :
    ∃ restore, i < restore ∧ restore < j ∧
      RawProductiveAt w N start restore ∧
      ¬ RawCurveSelfAt w start restore := by
  obtain ⟨restore, hir, hrj, H⟩ :=
    reused_novel_strict_shrink_charge_has_restoration_frame
      hN hij hlive hi hj heq
  exact ⟨restore, hir, hrj,
    H.restored.productive, H.restored.nonself⟩

/-- Successive reuses of one physical charge expose chronologically
disjoint restoration frames.  This is the serial-order part of the missing
global frame charge; what remains is to control interactions between the
serial families belonging to different physical ports. -/
theorem three_same_charge_shrinks_have_disjoint_restorations
    {w : Wiring} {N i j k : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hij : i < j) (hjk : j < k)
    (hlive : ∀ d, d ≤ k → (stepN w d start).isSome)
    (hi : RawNovelRepeatedStrictShrinkAt w N start i)
    (hj : RawNovelRepeatedStrictShrinkAt w N start j)
    (hk : RawNovelRepeatedStrictShrinkAt w N start k)
    (heqij : rawNovelStrictShrinkCharge w N start i =
      rawNovelStrictShrinkCharge w N start j)
    (heqjk : rawNovelStrictShrinkCharge w N start j =
      rawNovelStrictShrinkCharge w N start k) :
    ∃ restore₁ restore₂,
      i < restore₁ ∧ restore₁ < j ∧
      j < restore₂ ∧ restore₂ < k ∧
      RawPortRestorationFrame w N start i restore₁
        (rawNovelStrictShrinkCharge w N start i) ∧
      RawPortRestorationFrame w N start j restore₂
        (rawNovelStrictShrinkCharge w N start j) := by
  obtain ⟨restore₁, hi₁, h₁j, H₁⟩ :=
    reused_novel_strict_shrink_charge_has_restoration_frame
      hN hij (fun d hd => hlive d (by omega)) hi hj heqij
  obtain ⟨restore₂, hj₂, h₂k, H₂⟩ :=
    reused_novel_strict_shrink_charge_has_restoration_frame
      hN hjk hlive hj hk heqjk
  exact ⟨restore₁, restore₂, hi₁, h₁j, hj₂, h₂k, H₁, H₂⟩

/-! ## Compiling every shrink into a first port or a restoration frame -/

/-- The canonical charge of `k` was already used by an earlier globally
novel repeated-writer strict shrink. -/
def HasEarlierNovelStrictShrinkCharge
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Prop :=
  ∃ i, i < k ∧ RawNovelRepeatedStrictShrinkAt w N start i ∧
    rawNovelStrictShrinkCharge w N start i =
      rawNovelStrictShrinkCharge w N start k

/-- Every novel strict shrink receives one of two disjoint keys.

* the even key `2*port` is the first loss charged to that physical port;
* the odd key `2*k+1` is a reuse at time `k`.  The theorem below supplies the
  restoration frame which certifies every odd key.

Including `k` in the reuse key records the closing shrink of the frame and
makes the compilation genuinely injective, rather than merely a cover. -/
noncomputable def rawNovelStrictShrinkFrameKey
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (k : Nat) : Nat := by
  classical
  exact if HasEarlierNovelStrictShrinkCharge w N start k then
    2 * k + 1
  else
    2 * rawNovelStrictShrinkCharge w N start k

/-- The port/frame key is injective on all globally novel repeated-writer
strict shrink events.  Two first-use keys with the same port are impossible
because the chronologically later event would be a reuse; reuse keys retain
their closing time. -/
theorem rawNovelStrictShrinkFrameKey_injective
    {w : Wiring} {N i j : Nat} {start : Nat × Tongues}
    (hi : RawNovelRepeatedStrictShrinkAt w N start i)
    (hj : RawNovelRepeatedStrictShrinkAt w N start j)
    (hkey : rawNovelStrictShrinkFrameKey w N start i =
      rawNovelStrictShrinkFrameKey w N start j) :
    i = j := by
  classical
  by_cases hEi : HasEarlierNovelStrictShrinkCharge w N start i
  · by_cases hEj : HasEarlierNovelStrictShrinkCharge w N start j
    · simp [rawNovelStrictShrinkFrameKey, hEi, hEj] at hkey
      omega
    · simp [rawNovelStrictShrinkFrameKey, hEi, hEj] at hkey
      omega
  · by_cases hEj : HasEarlierNovelStrictShrinkCharge w N start j
    · simp [rawNovelStrictShrinkFrameKey, hEi, hEj] at hkey
      omega
    · have hcharge : rawNovelStrictShrinkCharge w N start i =
          rawNovelStrictShrinkCharge w N start j := by
        simp [rawNovelStrictShrinkFrameKey, hEi, hEj] at hkey
        omega
      by_cases hij : i = j
      · exact hij
      by_cases hlt : i < j
      · exact (hEj ⟨i, hlt, hi, hcharge⟩).elim
      · have hjlt : j < i := by omega
        exact (hEi ⟨j, hjlt, hj, hcharge.symm⟩).elim

/-- A reuse key carries an actual intervening restoration frame.  A first
key is bounded by the physical `3*N` port universe. -/
theorem rawNovelStrictShrinkFrameKey_spec
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hlive : ∀ d, d ≤ k → (stepN w d start).isSome)
    (hk : RawNovelRepeatedStrictShrinkAt w N start k) :
    (∃ port,
      rawNovelStrictShrinkFrameKey w N start k = 2 * port ∧
      port < 3 * N ∧
      ¬ HasEarlierNovelStrictShrinkCharge w N start k) ∨
    (∃ port previous restore,
      previous < restore ∧ restore < k ∧
      RawNovelRepeatedStrictShrinkAt w N start previous ∧
      rawNovelStrictShrinkCharge w N start previous = port ∧
      rawNovelStrictShrinkCharge w N start k = port ∧
      rawNovelStrictShrinkFrameKey w N start k = 2 * k + 1 ∧
      RawPortRestorationFrame w N start previous restore port) := by
  classical
  by_cases hEarlier : HasEarlierNovelStrictShrinkCharge w N start k
  · right
    obtain ⟨previous, hprev, hpEvent, hpCharge⟩ := hEarlier
    obtain ⟨restore, hpr, hrk, H⟩ :=
      reused_novel_strict_shrink_charge_has_restoration_frame
        hN hprev hlive hpEvent hk hpCharge
    have hEarlier' : HasEarlierNovelStrictShrinkCharge w N start k :=
      ⟨previous, hprev, hpEvent, hpCharge⟩
    refine ⟨rawNovelStrictShrinkCharge w N start k,
      previous, restore, hpr, hrk, hpEvent, hpCharge, rfl, ?_, ?_⟩
    · simp [rawNovelStrictShrinkFrameKey, hEarlier']
    · simpa [hpCharge] using H
  · left
    refine ⟨rawNovelStrictShrinkCharge w N start k, ?_, ?_, hEarlier⟩
    · simp [rawNovelStrictShrinkFrameKey, hEarlier]
    · have hspec := rawNovelStrictShrinkCharge_spec hk.2
      unfold rawFiniteCurvePortsAt at hspec
      exact (mem_finiteCurvePorts_iff.mp hspec.1).1

private theorem map_nodup_of_injective_on_mem_charge
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
        obtain ⟨b, hb, hEq⟩ := List.mem_map.mp hm
        have hab := hinj a List.mem_cons_self b
          (List.mem_cons_of_mem _ hb) hEq.symm
        exact hnd.1 (hab ▸ hb)
      · exact ih hnd.2
          (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx)
            y (List.mem_cons_of_mem _ hy))

/-- The complete finite key compilation is duplicate-free.  This is the
promised unconditional injection into first physical ports and certified
restoration-frame closings. -/
theorem rawNovelStrictShrinkFrameKeys_nodup
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    ((rawNovelRepeatedStrictShrinkTimes w N start K).map
      (rawNovelStrictShrinkFrameKey w N start)).Nodup := by
  classical
  have hevents :
      (rawNovelRepeatedStrictShrinkTimes w N start K).Nodup := by
    dsimp [rawNovelRepeatedStrictShrinkTimes]
    exact List.nodup_range.filter _
  apply map_nodup_of_injective_on_mem_charge
    (rawNovelStrictShrinkFrameKey w N start) hevents
  intro i hi j hj hkey
  have hiData := mem_rawNovelRepeatedStrictShrinkTimes_iff.mp hi
  have hjData := mem_rawNovelRepeatedStrictShrinkTimes_iff.mp hj
  exact rawNovelStrictShrinkFrameKey_injective
    hiData.2 hjData.2 hkey

/-! ## Exact first-port/reuse accounting -/

/-- Novel strict shrinks carrying a first-use physical-port charge. -/
noncomputable def rawFreshNovelStrictShrinkTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (rawNovelRepeatedStrictShrinkTimes w N start K).filter
    (fun k => ! decide (HasEarlierNovelStrictShrinkCharge w N start k))

/-- Novel strict shrinks carrying a reuse/restoration-frame charge. -/
noncomputable def rawReusedNovelStrictShrinkTimes
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) : List Nat := by
  classical
  exact (rawNovelRepeatedStrictShrinkTimes w N start K).filter
    (fun k => decide (HasEarlierNovelStrictShrinkCharge w N start k))

theorem mem_rawFreshNovelStrictShrinkTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawFreshNovelStrictShrinkTimes w N start K ↔
      k < K ∧ RawNovelRepeatedStrictShrinkAt w N start k ∧
        ¬ HasEarlierNovelStrictShrinkCharge w N start k := by
  classical
  simp [rawFreshNovelStrictShrinkTimes,
    mem_rawNovelRepeatedStrictShrinkTimes_iff]
  constructor
  · rintro ⟨⟨hK, hEvent⟩, hFresh⟩
    exact ⟨hK, hEvent, hFresh⟩
  · rintro ⟨hK, hEvent, hFresh⟩
    exact ⟨⟨hK, hEvent⟩, hFresh⟩

theorem mem_rawReusedNovelStrictShrinkTimes_iff
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues} :
    k ∈ rawReusedNovelStrictShrinkTimes w N start K ↔
      k < K ∧ RawNovelRepeatedStrictShrinkAt w N start k ∧
        HasEarlierNovelStrictShrinkCharge w N start k := by
  classical
  simp [rawReusedNovelStrictShrinkTimes,
    mem_rawNovelRepeatedStrictShrinkTimes_iff]
  constructor
  · rintro ⟨⟨hK, hEvent⟩, hReuse⟩
    exact ⟨hK, hEvent, hReuse⟩
  · rintro ⟨hK, hEvent, hReuse⟩
    exact ⟨⟨hK, hEvent⟩, hReuse⟩

private theorem filter_complement_length_charge
    {α : Type} (p : α → Bool) : ∀ xs : List α,
      (xs.filter (fun x => ! p x)).length +
        (xs.filter p).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons x rest ih =>
      cases hx : p x <;> simp [hx] at * <;> omega

/-- The first-use and reused charge lists form an exact partition. -/
theorem fresh_add_reused_novel_strict_shrinks_length
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawFreshNovelStrictShrinkTimes w N start K).length +
      (rawReusedNovelStrictShrinkTimes w N start K).length =
        (rawNovelRepeatedStrictShrinkTimes w N start K).length := by
  classical
  exact filter_complement_length_charge
    (fun k => decide (HasEarlierNovelStrictShrinkCharge w N start k))
    (rawNovelRepeatedStrictShrinkTimes w N start K)

/-- First-use charges inject into the `3*N` physical ports. -/
theorem fresh_novel_strict_shrinks_le_three_mul
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawFreshNovelStrictShrinkTimes w N start K).length ≤ 3 * N := by
  classical
  let fresh := rawFreshNovelStrictShrinkTimes w N start K
  let charge := rawNovelStrictShrinkCharge w N start
  have hfreshNodup : fresh.Nodup := by
    dsimp [fresh, rawFreshNovelStrictShrinkTimes]
    exact (List.nodup_range.filter _).filter _
  have hchargeNodup : (fresh.map charge).Nodup := by
    apply map_nodup_of_injective_on_mem_charge charge hfreshNodup
    intro i hi j hj hEq
    have hiData := mem_rawFreshNovelStrictShrinkTimes_iff.mp hi
    have hjData := mem_rawFreshNovelStrictShrinkTimes_iff.mp hj
    by_cases hij : i = j
    · exact hij
    by_cases hlt : i < j
    · exact (hjData.2.2 ⟨i, hlt, hiData.2.1, hEq⟩).elim
    · have hjlt : j < i := by omega
      exact (hiData.2.2 ⟨j, hjlt, hjData.2.1, hEq.symm⟩).elim
  have hbound : ∀ port, port ∈ fresh.map charge → port < 3 * N := by
    intro port hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hkData := mem_rawFreshNovelStrictShrinkTimes_iff.mp hk
    have hspec := rawNovelStrictShrinkCharge_spec hkData.2.1.2
    unfold rawFiniteCurvePortsAt at hspec
    exact (mem_finiteCurvePorts_iff.mp hspec.1).1
  have hle := nodup_nat_lt_length hchargeNodup hbound
  dsimp [fresh, charge] at hle ⊢
  simpa only [List.length_map] using hle

/-- **Exact unconditional global charge accounting.**

Every globally novel repeated-writer strict shrink is either one of at most
`3*N` first physical-port losses, or is a reuse event carrying a concrete
restoration frame.  No no-reuse or nesting premise appears here. -/
theorem novel_strict_shrinks_le_three_mul_add_reuses
    (w : Wiring) (N : Nat) (start : Nat × Tongues) (K : Nat) :
    (rawNovelRepeatedStrictShrinkTimes w N start K).length ≤
      3 * N + (rawReusedNovelStrictShrinkTimes w N start K).length := by
  have hfirst := fresh_novel_strict_shrinks_le_three_mul w N start K
  have hpartition :=
    fresh_add_reused_novel_strict_shrinks_length w N start K
  omega

/-- Every member of the reuse list has an earlier loss of the same physical
port and an intervening productive non-self restoration frame. -/
theorem reused_novel_strict_shrink_has_certified_restoration
    {w : Wiring} {N K k : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hlive : ∀ d, d ≤ K → (stepN w d start).isSome)
    (hk : k ∈ rawReusedNovelStrictShrinkTimes w N start K) :
    ∃ previous restore,
      previous < restore ∧ restore < k ∧
      RawNovelRepeatedStrictShrinkAt w N start previous ∧
      rawNovelStrictShrinkCharge w N start previous =
        rawNovelStrictShrinkCharge w N start k ∧
      RawPortRestorationFrame w N start previous restore
        (rawNovelStrictShrinkCharge w N start k) := by
  have hkData := mem_rawReusedNovelStrictShrinkTimes_iff.mp hk
  obtain ⟨previous, hprev, hpEvent, hpCharge⟩ := hkData.2.2
  obtain ⟨restore, hpr, hrk, H⟩ :=
    reused_novel_strict_shrink_charge_has_restoration_frame
      hN hprev (fun d hd => hlive d (by omega))
        hpEvent hkData.2.1 hpCharge
  refine ⟨previous, restore, hpr, hrk, hpEvent, hpCharge, ?_⟩
  simpa [hpCharge] using H

/-! ## The finite global charge dichotomy -/

private theorem nodup_or_equal_pair
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

/-- **Unconditional global lost-port/restoration-frame dichotomy.**

For every live finite raw prefix, canonical physical charges of globally
novel repeated-writer strict shrinks are either duplicate-free, or two
distinct charged events expose an actual productive non-self restoration
frame between their chronological positions.

This is the precise raw replacement for assuming silently that lost ports
never recur.  The remaining sharp theorem is now only the global charge of
these explicit restoration frames (or their collapse into a permanent
four-state self-only tail). -/
theorem novel_strict_shrink_charges_nodup_or_restoration_frame
    {w : Wiring} {N K : Nat} {start : Nat × Tongues}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (hlive : ∀ k, k ≤ K → (stepN w k start).isSome) :
    let events := rawNovelRepeatedStrictShrinkTimes w N start K
    let charge := rawNovelStrictShrinkCharge w N start
    (events.map charge).Nodup ∨
      ∃ i, i ∈ events ∧ ∃ j, j ∈ events ∧ i < j ∧
        charge i = charge j ∧
        ∃ restore, i < restore ∧ restore < j ∧
          RawPortRestorationFrame w N start i restore (charge i) := by
  classical
  dsimp only
  let events := rawNovelRepeatedStrictShrinkTimes w N start K
  let charge := rawNovelStrictShrinkCharge w N start
  have heventsNodup : events.Nodup := by
    dsimp [events, rawNovelRepeatedStrictShrinkTimes]
    exact List.nodup_range.filter _
  rcases nodup_or_equal_pair charge heventsNodup with hnd | hpair
  · exact Or.inl hnd
  · right
    obtain ⟨i, hiMem, j, hjMem, hij, hEq⟩ := hpair
    have hiData := mem_rawNovelRepeatedStrictShrinkTimes_iff.mp hiMem
    have hjData := mem_rawNovelRepeatedStrictShrinkTimes_iff.mp hjMem
    by_cases hlt : i < j
    · refine ⟨i, hiMem, j, hjMem, hlt, hEq, ?_⟩
      exact reused_novel_strict_shrink_charge_has_restoration_frame
        hN hlt (fun k hk => hlive k (by omega))
          hiData.2 hjData.2 hEq
    · have hjlt : j < i := by omega
      refine ⟨j, hjMem, i, hiMem, hjlt, hEq.symm, ?_⟩
      exact reused_novel_strict_shrink_charge_has_restoration_frame
        hN hjlt (fun k hk => hlive k (by omega))
          hjData.2 hiData.2 hEq.symm

end GeneralN
