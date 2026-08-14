import Alternation
import RestorationFrames

/-!
# Ordering a stable blocker inside a minimal restoration crossing

This file isolates the exact order-theoretic residue left by
`RestorationFrames`.  Let `(t0,u0)` and `(t1,u1)` be an inclusion-minimal
foreign/foreign crossing, so `t0 < t1 < u0 < u1`, and let `b` be a stable
productive blocker with `t1 < b < u0`.

Periodicity supplies the first restoration `(b,r)` before `b+p`.  If that
restoration is foreign and crosses `u0` while ending before `u1`, then
`(t0,u0)` and `(b,r)` are a strictly smaller foreign crossing.  Therefore
the only possibilities are:

* one endpoint of `(b,r)` is a same-edge write;
* the restoration is nested, `r <= u0`; or
* it exits the crossing, `u1 <= r < b+p`.

For the exit case we prove every period-shift identity needed to move a
foreign frame back by one period.  If the blocker is not in the first tail
period, the shifted frame exists and must avoid crossing either original
frame.  Periodicity alone does not determine on which side of those two
crossing windows the shifted endpoints lie; that precise order alternative
is the residual implication recorded here.
-/

namespace Echo

variable (m : Machine) (e : Nat -> Nat) (r0 : Nat -> Nat)

/-- Exact entry/register recurrence on a periodic tail. -/
structure RestorationPeriodicTail (K p : Nat) : Prop where
  positive : 0 < p
  entry : forall q, K <= q -> e (q+p) = e q
  register : forall q c, K <= q ->
    reg m e r0 (q+p) c = reg m e r0 q c

/-- `b` is productive and no later productive write before `j` writes its
cell.  This is exactly the stability conclusion supplied by the last-blocker
witness in `bar_retrace_or_first_overwrite`. -/
structure StableBlockerUntil (b j : Nat) : Prop where
  productive : ProductiveStep m e r0 b
  before : b < j
  stable : forall s, b < s -> s < j -> ProductiveStep m e r0 s ->
    writerAt m e s ≠ writerAt m e b

/-- A write replaces its register by a slot on the same physical edge. -/
def SameEdgeWrite (k : Nat) : Prop :=
  SameEdge m (oldSlot m e r0 k) (e (k+1))

/-- Exact lobe-reflector form of a productive same-edge write. -/
def ExactLobeWrite (k : Nat) : Prop :=
  e (k+1) = m.bar (oldSlot m e r0 k) ∧
  oldSlot m e r0 k = m.bar (e (k+1)) ∧
  m.cellOf (m.bar (oldSlot m e r0 k)) =
    m.cellOf (oldSlot m e r0 k)

/-- At a productive step, a same-edge write is exactly a flip across a lobe
edge.  The first SameEdge alternative `new = old` is excluded by
productivity; the common-cell fact comes from the register invariant. -/
theorem productive_sameEdgeWrite_exact_lobe
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {k : Nat}
    (hprod : ProductiveStep m e r0 k)
    (hsame : SameEdgeWrite m e r0 k) :
    ExactLobeWrite m e r0 k := by
  have hne : e (k+1) ≠ oldSlot m e r0 k := by
    simpa [ProductiveStep, oldSlot] using hprod
  rcases hsame with heq | hbar
  · exact (hne heq).elim
  · have hback : oldSlot m e r0 k = m.bar (e (k+1)) := by
      have h := congrArg m.bar hbar
      rw [m.bar_invol] at h
      exact h.symm
    have hcell := old_new_cell m e r0 hr0 k
    rw [hbar] at hcell
    exact ⟨hbar, hback, hcell.symm⟩



def crossingOverlap (_t0 u0 t1 _u1 : Nat) : Nat :=
  u0 - t1

/-- A foreign crossing represented on the universal time cover of a period
`p`, with each constituent restoration shorter than one period.  Endpoints
may pass the chosen period cut; this is essential for wrapped crossings. -/
def PeriodLiftedForeignRestorationCrossing
    (p t0 u0 t1 u1 : Nat) : Prop :=
  ForeignRestorationCrossing m e r0 t0 u0 t1 u1 ∧
  u0 < t0+p ∧
  u1 < t1+p

/-- A canonical lift of a cyclic crossing: the first opening is in the
half-open fundamental window `[K,K+p)`. -/
def PeriodNormalizedForeignRestorationCrossing
    (K p t0 u0 t1 u1 : Nat) : Prop :=
  PeriodLiftedForeignRestorationCrossing m e r0 p t0 u0 t1 u1 ∧
  K <= t0 ∧ t0 < K+p

/-- Cyclic minimality uses the interleaving overlap, not linear inclusion of
the containing hull.  The competitors are all canonical period lifts. -/
def CyclicOverlapMinimalForeignRestorationCrossing
    (K p t0 u0 t1 u1 : Nat) : Prop :=
  PeriodNormalizedForeignRestorationCrossing
    m e r0 K p t0 u0 t1 u1 ∧
  forall a0 b0 a1 b1,
    PeriodNormalizedForeignRestorationCrossing
      m e r0 K p a0 b0 a1 b1 ->
    crossingOverlap a0 b0 a1 b1 < crossingOverlap t0 u0 t1 u1 ->
    False


theorem cyclic_overlap_descent
    {K p t0 u0 t1 u1 b r : Nat}
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hframe : ForeignRestorationFrame m e r0 b r)
    (ht1b : t1 < b) (hbu0 : b < u0)
    (hu0r : u0 < r) (hrperiod : r < b+p) : False := by
  rcases hmin with ⟨hnorm, hminimal⟩
  rcases hnorm with ⟨hlift, hKt0, ht0Kp⟩
  rcases hlift with ⟨hcross, hu0period, _hu1period⟩
  rcases hcross with ⟨hframe0, _hframe1, horder⟩
  rcases horder with ⟨ht0t1, _ht1u0, _hu0u1⟩
  have hnewCross : ForeignRestorationCrossing m e r0 t0 u0 b r :=
    ⟨hframe0, hframe, ⟨by omega, hbu0, hu0r⟩⟩
  have hnewLift : PeriodLiftedForeignRestorationCrossing
      m e r0 p t0 u0 b r :=
    ⟨hnewCross, hu0period, hrperiod⟩
  have hnewNorm : PeriodNormalizedForeignRestorationCrossing
      m e r0 K p t0 u0 b r :=
    ⟨hnewLift, hKt0, ht0Kp⟩
  apply hminimal t0 u0 b r hnewNorm
  unfold crossingOverlap
  omega

/-- Consequently, every foreign first restoration of a middle blocker is
nested by the first closing time.  This is the modular span descent which
linear inclusion-minimality could not express. -/
theorem cyclic_minimal_middle_foreign_restoration_nested
    {K p t0 u0 t1 u1 b r : Nat}
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hframe : ForeignRestorationFrame m e r0 b r)
    (ht1b : t1 < b) (hbu0 : b < u0)
    (hrperiod : r < b+p) :
    r <= u0 := by
  by_cases hru0 : r <= u0
  · exact hru0
  · exfalso
    exact cyclic_overlap_descent m e r0 hmin hframe ht1b hbu0
      (by omega) hrperiod


theorem stable_blocker_restoration_after_read
    {b j r : Nat}
    (hstable : StableBlockerUntil m e r0 b j)
    (hframe : RestorationFrame m e r0 b r) :
    j <= r := by
  rcases hframe with ⟨_hpb, hbr, hpr, hwriter, _hreturn⟩
  by_cases hjr : j <= r
  · exact hjr
  · exfalso
    exact (hstable.stable r hbr (by omega) hpr) hwriter

/-- Entries one step after a time also repeat with the same period. -/
theorem period_entry_succ
    {K p q : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hq : K <= q) :
    e ((q+p)+1) = e (q+1) := by
  have h := hper.entry (q+1) (by omega)
  have harith : (q+1)+p = (q+p)+1 := by omega
  rw [harith] at h
  exact h

/-- The written cell is period invariant. -/
theorem writerAt_periodic
    {K p q : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hq : K <= q) :
    writerAt m e (q+p) = writerAt m e q := by
  unfold writerAt
  rw [period_entry_succ m e r0 hper hq]

/-- The evicted slot is period invariant. -/
theorem oldSlot_periodic
    {K p q : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hq : K <= q) :
    oldSlot m e r0 (q+p) = oldSlot m e r0 q := by
  unfold oldSlot
  rw [period_entry_succ m e r0 hper hq, hper.register q _ hq]

/-- Productivity is period invariant from the tail base onward. -/
theorem productiveStep_periodic
    {K p q : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hq : K <= q) :
    ProductiveStep m e r0 (q+p) ↔ ProductiveStep m e r0 q := by
  exact productive_periodic m e r0 hper.entry hper.register hq

/-- The same-edge/foreign identity of a write is period invariant. -/
theorem sameEdgeWrite_periodic
    {K p q : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hq : K <= q) :
    SameEdgeWrite m e r0 (q+p) ↔ SameEdgeWrite m e r0 q := by
  unfold SameEdgeWrite
  rw [oldSlot_periodic m e r0 hper hq,
    period_entry_succ m e r0 hper hq]

/-- Restoration frames are invariant under a simultaneous one-period shift
of both endpoints. -/
theorem restorationFrame_periodic
    {K p t u : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (ht : K <= t) :
    RestorationFrame m e r0 (t+p) (u+p) ↔
      RestorationFrame m e r0 t u := by
  constructor
  · rintro ⟨hpt, htu, hpu, hwriter, hreturn⟩
    have hut : K <= u := by omega
    refine ⟨(productiveStep_periodic m e r0 hper ht).mp hpt,
      by omega, (productiveStep_periodic m e r0 hper hut).mp hpu, ?_, ?_⟩
    · rw [writerAt_periodic m e r0 hper hut,
        writerAt_periodic m e r0 hper ht] at hwriter
      exact hwriter
    · rw [period_entry_succ m e r0 hper hut,
        oldSlot_periodic m e r0 hper ht] at hreturn
      exact hreturn
  · rintro ⟨hpt, htu, hpu, hwriter, hreturn⟩
    have hut : K <= u := by omega
    refine ⟨(productiveStep_periodic m e r0 hper ht).mpr hpt,
      by omega, (productiveStep_periodic m e r0 hper hut).mpr hpu, ?_, ?_⟩
    · rw [writerAt_periodic m e r0 hper hut,
        writerAt_periodic m e r0 hper ht]
      exact hwriter
    · rw [period_entry_succ m e r0 hper hut,
        oldSlot_periodic m e r0 hper ht]
      exact hreturn

/-- Firstness is also invariant under a simultaneous period shift. -/
theorem firstRestorationFrame_periodic
    {K p t u : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (ht : K <= t) :
    FirstRestorationFrame m e r0 (t+p) (u+p) ↔
      FirstRestorationFrame m e r0 t u := by
  constructor
  · rintro ⟨hframe, hfirst⟩
    have hbase := (restorationFrame_periodic m e r0 hper ht).mp hframe
    refine ⟨hbase, ?_⟩
    intro v htv hvu heq
    have hne := hfirst (v+p) (by omega) (by omega)
    apply hne
    rw [period_entry_succ m e r0 hper (by omega),
      oldSlot_periodic m e r0 hper ht]
    exact heq
  · rintro ⟨hframe, hfirst⟩
    have hshift := (restorationFrame_periodic m e r0 hper ht).mpr hframe
    refine ⟨hshift, ?_⟩
    intro v htv hvu heq
    have hpv : p <= v := by omega
    let v0 := v-p
    have hv0p : v0+p = v := by
      dsimp [v0]
      exact Nat.sub_add_cancel hpv
    have htv0 : t < v0 := by
      dsimp [v0]
      omega
    have hv0u : v0 < u := by
      dsimp [v0]
      omega
    have hne := hfirst v0 htv0 hv0u
    apply hne
    have hentry := period_entry_succ m e r0 hper (q := v0) (by omega)
    have hold := oldSlot_periodic m e r0 hper ht
    rw [hv0p] at hentry
    rw [hentry, hold] at heq
    exact heq

/-- Foreign restoration frames are invariant under a simultaneous period
shift, including both physical-edge identities. -/
theorem foreignRestorationFrame_periodic
    {K p t u : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (ht : K <= t) :
    ForeignRestorationFrame m e r0 (t+p) (u+p) ↔
      ForeignRestorationFrame m e r0 t u := by
  constructor
  · rintro ⟨hframe, hopen, hclose⟩
    have hbase := (firstRestorationFrame_periodic m e r0 hper ht).mp hframe
    have hut : K <= u := by
      rcases hbase.1 with ⟨_hp, htu, _⟩
      omega
    exact ⟨hbase,
      fun h => hopen ((sameEdgeWrite_periodic m e r0 hper ht).mpr h),
      fun h => hclose ((sameEdgeWrite_periodic m e r0 hper hut).mpr h)⟩
  · rintro ⟨hframe, hopen, hclose⟩
    have hut : K <= u := by
      rcases hframe.1 with ⟨_hp, htu, _⟩
      omega
    exact ⟨(firstRestorationFrame_periodic m e r0 hper ht).mpr hframe,
      fun h => hopen ((sameEdgeWrite_periodic m e r0 hper ht).mp h),
      fun h => hclose ((sameEdgeWrite_periodic m e r0 hper hut).mp h)⟩

theorem periodLiftedForeignRestorationCrossing_periodic
    {K p t0 u0 t1 u1 : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (ht0 : K <= t0) :
    PeriodLiftedForeignRestorationCrossing m e r0 p
      (t0+p) (u0+p) (t1+p) (u1+p) ↔
    PeriodLiftedForeignRestorationCrossing m e r0 p
      t0 u0 t1 u1 := by
  constructor
  · rintro ⟨hcross, hu0period, hu1period⟩
    rcases hcross with ⟨hframe0, hframe1, horder⟩
    have horder0 : RestorationFramesCross t0 u0 t1 u1 := by
      rcases horder with ⟨h01, h10, h01'⟩
      exact ⟨by omega, by omega, by omega⟩
    have ht1 : K <= t1 := by
      rcases horder0 with ⟨ht0t1, _⟩
      omega
    have hframe0' :=
      (foreignRestorationFrame_periodic m e r0 hper ht0).mp hframe0
    have hframe1' :=
      (foreignRestorationFrame_periodic m e r0 hper ht1).mp hframe1
    exact ⟨⟨hframe0', hframe1', horder0⟩, by omega, by omega⟩
  · rintro ⟨hcross, hu0period, hu1period⟩
    rcases hcross with ⟨hframe0, hframe1, horder⟩
    rcases horder with ⟨ht0t1, ht1u0, hu0u1⟩
    have ht1 : K <= t1 := by omega
    have hframe0' :=
      (foreignRestorationFrame_periodic m e r0 hper ht0).mpr hframe0
    have hframe1' :=
      (foreignRestorationFrame_periodic m e r0 hper ht1).mpr hframe1
    exact ⟨⟨hframe0', hframe1', ⟨by omega, by omega, by omega⟩⟩,
      by omega, by omega⟩

/-- A foreign restoration frame can be shifted back one period whenever its
opening endpoint remains on the periodic tail. -/
theorem foreignRestorationFrame_shift_back
    {K p b r : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hpb : p <= b) (hK : K <= b-p)
    (hframe : ForeignRestorationFrame m e r0 b r) :
    ForeignRestorationFrame m e r0 (b-p) (r-p) := by
  have hbr : b < r := hframe.1.1.2.1
  have hpr : p <= r := by omega
  have hbadd : (b-p)+p = b := Nat.sub_add_cancel hpb
  have hradd : (r-p)+p = r := Nat.sub_add_cancel hpr
  have hshift : ForeignRestorationFrame m e r0
      ((b-p)+p) ((r-p)+p) := by
    simpa [hbadd, hradd] using hframe
  exact (foreignRestorationFrame_periodic m e r0 hper hK).mp hshift

/-- A period-sized crossing can be shifted back whenever its first opening
remains on the recurrent tail. -/
theorem periodLiftedForeignRestorationCrossing_shift_back
    {K p t0 u0 t1 u1 : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hK : K <= t0-p) (hp0 : p <= t0)
    (hlift : PeriodLiftedForeignRestorationCrossing
      m e r0 p t0 u0 t1 u1) :
    PeriodLiftedForeignRestorationCrossing m e r0 p
      (t0-p) (u0-p) (t1-p) (u1-p) := by
  rcases hlift with ⟨hcross, hu0period, hu1period⟩
  rcases hcross with ⟨hframe0, hframe1, horder⟩
  rcases horder with ⟨ht0t1, ht1u0, hu0u1⟩
  have hp1 : p <= t1 := by omega
  have hK1 : K <= t1-p := by omega
  have hframe0' :=
    foreignRestorationFrame_shift_back m e r0 hper hp0 hK hframe0
  have hframe1' :=
    foreignRestorationFrame_shift_back m e r0 hper hp1 hK1 hframe1
  exact ⟨⟨hframe0', hframe1', ⟨by omega, by omega, by omega⟩⟩,
    by omega, by omega⟩

/-- Back-shifting a lifted crossing does not change its overlap. -/
theorem crossingOverlap_shift_back
    {p t0 u0 t1 u1 : Nat}
    (hp0 : p <= t0) (ht0t1 : t0 < t1) :
    crossingOverlap (t0-p) (u0-p) (t1-p) (u1-p) =
      crossingOverlap t0 u0 t1 u1 := by
  unfold crossingOverlap
  omega

/-- Repeated backward period shifts place the first opening into the
fundamental window without changing the lifted crossing or its overlap. -/
theorem periodLifted_crossing_has_normalized_lift
    {K p t0 u0 t1 u1 : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hKt0 : K <= t0)
    (hlift : PeriodLiftedForeignRestorationCrossing
      m e r0 p t0 u0 t1 u1) :
    exists a0 b0 a1 b1,
      PeriodNormalizedForeignRestorationCrossing
        m e r0 K p a0 b0 a1 b1 ∧
      crossingOverlap a0 b0 a1 b1 =
        crossingOverlap t0 u0 t1 u1 := by
  by_cases hwindow : t0 < K+p
  · exact ⟨t0, u0, t1, u1, ⟨hlift, hKt0, hwindow⟩, rfl⟩
  · have hKp : K+p <= t0 := by omega
    have hp0 : p <= t0 := by omega
    have hKprev : K <= t0-p := by omega
    have hprev := periodLiftedForeignRestorationCrossing_shift_back
      m e r0 hper hKprev hp0 hlift
    obtain ⟨a0, b0, a1, b1, hnorm, hover⟩ :=
      periodLifted_crossing_has_normalized_lift
        hper hKprev hprev
    refine ⟨a0, b0, a1, b1, hnorm, hover.trans ?_⟩
    exact crossingOverlap_shift_back hp0 hlift.1.2.2.1
termination_by t0
decreasing_by
  have hp := hper.positive
  omega

theorem cyclic_minimal_stable_blocker_order
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b j : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hKb : K <= b)
    (ht1b : t1 < b) (hbu0 : b < u0)
    (hstable : StableBlockerUntil m e r0 b j) :
    exists r,
      b < r ∧ r < b+p ∧
      FirstRestorationFrame m e r0 b r ∧
      j <= r ∧
      (SameEdgeWrite m e r0 b ∨
       SameEdgeWrite m e r0 r ∨
       r <= u0) := by
  obtain ⟨r, hbr, hrperiod, hfirst⟩ :=
    productive_has_first_restoration_before_period m e r0 hr0
      hper.positive hKb hper.register hstable.productive
  have hjr := stable_blocker_restoration_after_read m e r0 hstable hfirst.1
  refine ⟨r, hbr, hrperiod, hfirst, hjr, ?_⟩
  by_cases hopen : SameEdgeWrite m e r0 b
  · exact Or.inl hopen
  · by_cases hclose : SameEdgeWrite m e r0 r
    · exact Or.inr (Or.inl hclose)
    · have hforeign : ForeignRestorationFrame m e r0 b r :=
        ⟨hfirst, hopen, hclose⟩
      exact Or.inr (Or.inr
        (cyclic_minimal_middle_foreign_restoration_nested
          m e r0 hmin hforeign ht1b hbu0 hrperiod))
theorem first_restoration_forbids_early_returned_register
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {t0 u0 b : Nat}
    (houter : FirstRestorationFrame m e r0 t0 u0)
    (hgap : t0+1 < b) (hbu0 : b < u0)
    (hwriter : writerAt m e b = writerAt m e t0)
    (hold : oldSlot m e r0 b = oldSlot m e r0 t0) : False := by
  have hreturn : reg m e r0 b (writerAt m e t0) =
      oldSlot m e r0 t0 := by
    calc
      reg m e r0 b (writerAt m e t0) =
          reg m e r0 b (writerAt m e b) := by rw [hwriter]
      _ = oldSlot m e r0 b := by rfl
      _ = oldSlot m e r0 t0 := hold
  obtain ⟨v, hvb, hvframe⟩ :=
    exists_first_restoration_frame_of_register_return
      m e r0 hr0 houter.1.1 hgap hreturn
  have hne := houter.2 v hvframe.1.2.1 (by omega)
  exact hne hvframe.1.2.2.2.2

end Echo
