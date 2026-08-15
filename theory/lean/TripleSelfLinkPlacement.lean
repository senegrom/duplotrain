import TripleSelfLinkReplay

/-!
# Locating the fixed self-link inside the selected triple

The fixed-entry alternative in `TripleInterlacementObstruction` used to
discard the time at which the fixed entry is found.  That loss is material:
the raw five-frame closure needs to know that the physical self-link lies
inside the selected `ABCABC` window.

This file strengthens the recursive obstruction without adding any new
hypothesis.  A fixed entry produced while eliminating a nested restoration
is kept between the opening blocker and its restoration.  Consequently the
self-link forced by a certified selected triple occurs strictly after the
third selected opening and strictly before the first selected closing.

This is a genuine raw-physical placement theorem, but it is deliberately not
yet advertised as the full `KnownEdgeABCABCSelfLinkReplayOrTailClosure`: the
remaining step is to transport this certified-ascent interval through the raw
clock and extract the corresponding replay or manufactured tail.
-/

namespace Echo

variable (m : Machine) (e : Nat -> Nat) (r0 : Nat -> Nat)

/-- Bounded form of `consecutive_same_writer_earlier_replay_or_fixed`.
The fixed entry is not merely somewhere in the run: it lies after the first
write and no later than the second write. -/
theorem consecutive_same_writer_earlier_replay_or_bounded_fixed
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p C t1 t2 : Nat}
    (hK : K <= t1)
    (h12 : t1 < t2)
    (ht2period : t2 < t1 + p)
    (hquiet : forall s, t1 < s -> s < t2 ->
      Not (ProductiveStep m e r0 s))
    (hc1 : m.cellOf (e (t1 + 1)) = C)
    (hc2 : m.cellOf (e (t2 + 1)) = C) :
    EarlierCompleteStateReplay m e r0 K p ∨
    exists q, t1 < q ∧ q <= t2 ∧ m.bar (e q) = e q := by
  rcases consecutive_same_write_replay_or_visit
      m e r0 hrun h12 hquiet hc1 hc2 with hloop | hvisit
  · left
    refine ⟨t2 + 1, t2 - t1, ?_⟩
    exact (by
      constructor
      · omega
      constructor
      · omega
      constructor
      · omega
      · exact hloop)
  · obtain ⟨l, hl1, hl2, hcell | hmouth⟩ := hvisit
    · left
      let start := t1 + 1
      have hsegment : forall t, start <= t -> t < start + l ->
          Not (ProductiveStep m e r0 t) := by
        intro t hlow hhigh
        exact hquiet t (by dsimp [start] at hlow; omega)
          (by dsimp [start] at hhigh; omega)
      have hreturn :
          m.cellOf (e (start + l)) = m.cellOf (e start) := by
        dsimp [start]
        rw [hc1]
        exact hcell
      refine ⟨start, l, ?_⟩
      exact (by
        constructor
        · dsimp [start]
          omega
        constructor
        · omega
        constructor
        · omega
        · exact quiet_return_complete_state
            m e r0 hsegment hreturn)
    · right
      let start := t1 + 1
      have hsegment : forall t, start <= t -> t < start + l ->
          Not (ProductiveStep m e r0 t) := by
        intro t hlow hhigh
        exact hquiet t (by dsimp [start] at hlow; omega)
          (by dsimp [start] at hhigh; omega)
      have hmouth' :
          m.cellOf (e (start + l)) =
            m.star (m.cellOf (e start)) := by
        dsimp [start]
        rw [hc1]
        exact hmouth
      obtain ⟨q, hqlo, hqhi, hfix⟩ :=
        quiet_mouth_forces_fixed_entry
          m e r0 hrun hr0 hsegment hmouth'
      refine ⟨q, ?_, ?_, hfix⟩
      · dsimp [start] at hqlo
        omega
      · dsimp [start] at hqhi
        omega

/-- Bounded recursive nested-restoration obstruction.  If recursion ends in
the fixed-entry branch, its witness remains inside the original restoration
frame. -/
theorem cyclic_minimal_nested_foreign_obstruction_bounded
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b r : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hKb : K <= b)
    (ht1b : t1 < b)
    (hbr : b < r)
    (hrperiod : r < b + p)
    (hru0 : r < u0)
    (hframe : ForeignRestorationFrame m e r0 b r) :
    (exists k, ExactLobeWrite m e r0 k) ∨
    EarlierCompleteStateReplay m e r0 K p ∨
    (exists q, b < q ∧ q <= r ∧ m.bar (e q) = e q) := by
  by_cases hinter : exists d, b < d ∧ d < r ∧
      ProductiveStep m e r0 d
  · obtain ⟨d, hbd, hdr, hprodD⟩ := hinter
    have hKd : K <= d := by omega
    obtain ⟨s, hds, hsperiod, hfirstD⟩ :=
      productive_has_first_restoration_before_period
        m e r0 hr0 hper.positive hKd hper.register hprodD
    by_cases hopen : SameEdgeWrite m e r0 d
    · exact Or.inl ⟨d, productive_sameEdgeWrite_exact_lobe
        m e r0 hr0 hprodD hopen⟩
    · by_cases hclose : SameEdgeWrite m e r0 s
      · exact Or.inl ⟨s, productive_sameEdgeWrite_exact_lobe
          m e r0 hr0 hfirstD.1.2.2.1 hclose⟩
      · have hforeignD : ForeignRestorationFrame m e r0 d s :=
          ⟨hfirstD, hopen, hclose⟩
        by_cases hsr : s < r
        · rcases cyclic_minimal_nested_foreign_obstruction_bounded
              hrun hr0 hper hmin hKd (by omega)
              hds hsperiod (by omega) hforeignD with
            hlobe | hreplay | hfixed
          · exact Or.inl hlobe
          · exact Or.inr (Or.inl hreplay)
          · obtain ⟨q, hdq, hqs, hfix⟩ := hfixed
            exact Or.inr (Or.inr ⟨q, by omega, by omega, hfix⟩)
        · by_cases hEq : s = r
          · subst s
            exact (nested_foreign_frames_shared_close_impossible
              m e r0 hr0 hframe.1 hfirstD hbd).elim
          · have hrs : r < s := by omega
            have hcross : ForeignRestorationCrossing
                m e r0 b r d s :=
              ⟨hframe, hforeignD, ⟨hbd, hdr, hrs⟩⟩
            have hlift : PeriodLiftedForeignRestorationCrossing
                m e r0 p b r d s :=
              ⟨hcross, hrperiod, hsperiod⟩
            obtain ⟨a0, z0, a1, z1, hnorm, hover⟩ :=
              periodLifted_crossing_has_normalized_lift
                m e r0 hper hKb hlift
            have hstrict :
                crossingOverlap a0 z0 a1 z1 <
                  crossingOverlap t0 u0 t1 u1 := by
              rw [hover]
              unfold crossingOverlap
              omega
            exact (hmin.2 a0 z0 a1 z1 hnorm hstrict).elim
  · have hquiet : forall s, b < s -> s < r ->
        Not (ProductiveStep m e r0 s) := by
      intro s hbs hsr hprod
      exact hinter ⟨s, hbs, hsr, hprod⟩
    have hc2 : m.cellOf (e (r + 1)) =
        m.cellOf (e (b + 1)) := by
      exact hframe.1.1.2.2.2.1
    rcases consecutive_same_writer_earlier_replay_or_bounded_fixed
        m e r0 hrun hr0 hKb hbr hrperiod hquiet rfl hc2 with
      hreplay | hfixed
    · exact Or.inr (Or.inl hreplay)
    · exact Or.inr (Or.inr hfixed)
termination_by r - b
decreasing_by omega

/-- The fixed entry in the stable-blocker obstruction lies in the selected
overlap, rather than at an unlocated time in the certified run. -/
theorem cyclic_minimal_stable_blocker_obstruction_bounded
    (hrun : IsRun m e r0)
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {K p t0 u0 t1 u1 b j : Nat}
    (hper : RestorationPeriodicTail m e r0 K p)
    (hmin : CyclicOverlapMinimalForeignRestorationCrossing
      m e r0 K p t0 u0 t1 u1)
    (hKb : K <= b)
    (ht1b : t1 < b)
    (hbu0 : b < u0)
    (hstable : StableBlockerUntil m e r0 b j) :
    (exists k, ExactLobeWrite m e r0 k) ∨
    EarlierCompleteStateReplay m e r0 K p ∨
    (exists q, b < q ∧ q < u0 ∧ m.bar (e q) = e q) := by
  obtain ⟨r, hbr, hrperiod, hfirst, _hjr, hout⟩ :=
    cyclic_minimal_stable_blocker_order
      m e r0 hr0 hper hmin hKb ht1b hbu0 hstable
  by_cases hopen : SameEdgeWrite m e r0 b
  · exact Or.inl ⟨b, productive_sameEdgeWrite_exact_lobe
      m e r0 hr0 hstable.productive hopen⟩
  · by_cases hclose : SameEdgeWrite m e r0 r
    · exact Or.inl ⟨r, productive_sameEdgeWrite_exact_lobe
        m e r0 hr0 hfirst.1.2.2.1 hclose⟩
    · have hforeign : ForeignRestorationFrame m e r0 b r :=
        ⟨hfirst, hopen, hclose⟩
      have hru0 : r <= u0 := by
        rcases hout with h | h | h
        · exact (hopen h).elim
        · exact (hclose h).elim
        · exact h
      have hrlt : r < u0 := by
        by_cases hre : r = u0
        · have houter : FirstRestorationFrame m e r0 t0 u0 :=
            hmin.1.1.1.1.1
          have ht0b : t0 < b := by
            have ht0t1 : t0 < t1 := hmin.1.1.1.2.2.1
            exact Nat.lt_trans ht0t1 ht1b
          subst r
          exact (nested_foreign_frames_shared_close_impossible
            m e r0 hr0 houter hfirst ht0b).elim
        · omega
      rcases cyclic_minimal_nested_foreign_obstruction_bounded
          m e r0 hrun hr0 hper hmin hKb ht1b hbr
            hrperiod hrlt hforeign with
        hlobe | hreplay | hfixed
      · exact Or.inl hlobe
      · exact Or.inr (Or.inl hreplay)
      · obtain ⟨q, hbq, hqr, hfix⟩ := hfixed
        exact Or.inr (Or.inr ⟨q, hbq, by omega, hfix⟩)

end Echo

namespace GeneralN

/-! ## Certified ascents are genuine positive raw journeys -/


structure RawCycleThroughSelfLink
    (w : Wiring) (start : Nat × Tongues) (close : Nat) where
  closeConfig : Nat × Tongues
  branch : Nat
  state : Tongues
  offset : Nat
  period : Nat
  period_positive : 0 < period
  cycle : stepN w period closeConfig = some closeConfig
  self_at : stepN w offset closeConfig = some (branch, state)
  self_link : w.link branch = some branch

/-- Rotate the raw period from its recorded closing configuration to the
actual self-linked branch configuration. -/
theorem RawCycleThroughSelfLink.self_period
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    stepN w R.period (R.branch, R.state) =
      some (R.branch, R.state) := by
  have hcloseThenSelf :
      stepN w (R.period + R.offset) R.closeConfig =
        some (R.branch, R.state) := by
    rw [stepN_add, R.cycle]
    exact R.self_at
  have hselfThenPeriod := stepN_add w R.offset R.period R.closeConfig
  rw [R.self_at] at hselfThenPeriod
  simp only [Option.bind_some] at hselfThenPeriod
  rw [Nat.add_comm R.offset R.period, hcloseThenSelf] at hselfThenPeriod
  exact hselfThenPeriod.symm


structure RawTwoVectorTail
    (w : Wiring) (N : Nat) (start : Nat × Tongues) where
  shift : Nat
  localStart : Nat × Tongues
  phase₀ : List Bool
  phase₁ : List Bool
  reached : stepN w shift start = some localStart
  live : ∀ d, ∃ finish, stepN w d localStart = some finish

end GeneralN
