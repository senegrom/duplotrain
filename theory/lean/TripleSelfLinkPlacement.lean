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

/-- One step of the certified echo run is not an abstract transition.  Its
recorded descent followed by the certified facing retrace is a nonempty raw
train journey from one ascent boundary to the next. -/
theorem CertifiedConcreteEchoRun.one_ascent_raw_reach
    {w : Wiring} (run : CertifiedConcreteEchoRun w) (k : Nat) :
    exists travel, 0 < travel /\
      stepN w travel (run.entry k, run.boundary k) =
        some (run.entry (k + 1), run.boundary (k + 1)) := by
  have hrun := certifiedConcreteEcho_isRun run
  have hwitness := Echo.witness
    (canonicalEchoMachine w) (encodedEntries run.entry)
      run.initialRegister hrun run.initialWellFormed k
  have hpartner :
      (canonicalEchoMachine w).star
          ((canonicalEchoMachine w).cellOf
            (encodedEntries run.entry k)) =
        tracePartnerCell run.toConcreteAscentTrace k := by
    simp [encodedEntries, canonicalEchoMachine, encodedMachine,
      encodedCellOf_encodeSlot, tracePartnerCell, physicalCell,
      canonicalPhysicalCellOf]
  have hreg :
      Echo.reg (canonicalEchoMachine w) (encodedEntries run.entry)
          run.initialRegister k
          (tracePartnerCell run.toConcreteAscentTrace k) =
        encodeSlot (wireBar w (run.entry (k + 1))) := by
    rw [<- hpartner]
    simpa [encodedEntries, canonicalEchoMachine, encodedMachine,
      encodedBar_encodeSlot] using hwitness.2
  have hdescent := descent_sound (run.toConcreteAscentTrace.descent k)
  have hfacing := run.facing k
    (wireBar w (run.entry (k + 1))) hreg
  refine ⟨(run.tail k).length + 1 +
      (entryAction w (wireBar w (run.entry (k + 1)))).length,
    ?_, ?_⟩
  · omega
  · rw [stepN_add, hdescent]
    exact hfacing

/-- Iterating the preceding compiler fact gives a raw journey across any
finite interval of certified ascent indices.  The lower bound records that
every ascent consumes at least one physical train step. -/
theorem CertifiedConcreteEchoRun.ascent_interval_raw_reach
    {w : Wiring} (run : CertifiedConcreteEchoRun w) :
    forall i count, exists travel, count <= travel /\
      stepN w travel (run.entry i, run.boundary i) =
        some (run.entry (i + count), run.boundary (i + count)) := by
  intro i count
  induction count with
  | zero =>
      exact ⟨0, Nat.le_refl _, by simp [stepN]⟩
  | succ n ih =>
      obtain ⟨lead, hn, hlead⟩ := ih
      obtain ⟨finalLeg, hfinalPos, hfinal⟩ :=
        run.one_ascent_raw_reach (i + n)
      refine ⟨lead + finalLeg, ?_, ?_⟩
      · omega
      · rw [stepN_add, hlead]
        simpa [Nat.add_assoc] using hfinal

/-- Ordered certified indices therefore expose the later certified
configuration at a positive raw distance from the earlier one. -/
theorem CertifiedConcreteEchoRun.ascent_order_raw_reach
    {w : Wiring} (run : CertifiedConcreteEchoRun w) {i j : Nat}
    (hij : i < j) :
    exists travel, 0 < travel /\
      stepN w travel (run.entry i, run.boundary i) =
        some (run.entry j, run.boundary j) := by
  obtain ⟨travel, hbound, hreach⟩ :=
    run.ascent_interval_raw_reach i (j - i)
  refine ⟨travel, by omega, ?_⟩
  have hindex : i + (j - i) = j := by omega
  simpa [hindex] using hreach

/-! ## Endpoint-only raw transport -/

/-- A raw productive event guarantees that the configuration represented by
`rawEntryAt` and `tonguesAt` is genuinely reached; the defaults in those
definitions are therefore irrelevant at this time. -/
private theorem raw_configuration_at_of_productive
    {w : Wiring} {N k : Nat} {start : Nat × Tongues}
    (hprod : RawProductiveAt w N start k) :
    stepN w k start =
      some (rawEntryAt w start k, tonguesAt w start k) := by
  obtain ⟨post, hpost⟩ := Option.isSome_iff_exists.mp hprod.1
  obtain ⟨current, hcurrent⟩ := stepN_prefix_some
    (d := k) (K := k + 1) (by omega) hpost
  simpa [rawEntryAt, tonguesAt, hcurrent] using hcurrent

/-- The opening selected by an arbitrary `Fin 5` index is productive. -/
private theorem FiveRawClosingFrames.opening_productiveAt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4)
    (i : Fin 5) :
    RawProductiveAt w N start (F.openingAt i) := by
  rcases i with ⟨i, hi⟩
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    omega
  rcases hcases with h | h | h | h | h
  · subst i
    simpa [FiveRawClosingFrames.openingAt] using
      F.frame₀.outer.open_productive
  · subst i
    simpa [FiveRawClosingFrames.openingAt] using
      F.frame₁.outer.open_productive
  · subst i
    simpa [FiveRawClosingFrames.openingAt] using
      F.frame₂.outer.open_productive
  · subst i
    simpa [FiveRawClosingFrames.openingAt] using
      F.frame₃.outer.open_productive
  · subst i
    simpa [FiveRawClosingFrames.openingAt] using
      F.frame₄.outer.open_productive

/-- The closing selected by an arbitrary `Fin 5` index is productive. -/
private theorem FiveRawClosingFrames.closing_productiveAt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4)
    (i : Fin 5) :
    RawProductiveAt w N start (F.closingAt i) := by
  rcases i with ⟨i, hi⟩
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    omega
  rcases hcases with h | h | h | h | h
  · subst i
    simpa [FiveRawClosingFrames.closingAt] using
      F.frame₀.outer.close_productive
  · subst i
    simpa [FiveRawClosingFrames.closingAt] using
      F.frame₁.outer.close_productive
  · subst i
    simpa [FiveRawClosingFrames.closingAt] using
      F.frame₂.outer.close_productive
  · subst i
    simpa [FiveRawClosingFrames.closingAt] using
      F.frame₃.outer.close_productive
  · subst i
    simpa [FiveRawClosingFrames.closingAt] using
      F.frame₄.outer.close_productive

/-- A raw periodic orbit whose interior contains a physical self-link.  This
is the exact endpoint-only residual when a certified journey reaches the raw
closing endpoint only after wrapping around it. -/
structure RawCycleThroughSelfLink
    (w : Wiring) (start : Nat × Tongues) (close : Nat) where
  closeConfig : Nat × Tongues
  branch : Nat
  state : Tongues
  offset : Nat
  period : Nat
  close_at : stepN w close start = some closeConfig
  period_positive : 0 < period
  offset_positive : 0 < offset
  offset_before_period : offset < period
  cycle : stepN w period closeConfig = some closeConfig
  self_at : stepN w offset closeConfig = some (branch, state)
  branch_port : branch % 3 ≠ 0
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

/-- The state recorded at a reached self-linked branch really selects that
branch.  This is obtained from the actual preceding raw step; it is not an
extra orientation hypothesis. -/
theorem RawCycleThroughSelfLink.self_selected
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    R.state (R.branch / 3) = bval R.branch := by
  let previous := R.offset - 1
  have hpreviousLe : previous ≤ R.offset := by
    dsimp [previous]
    omega
  obtain ⟨before, hbefore⟩ :=
    stepN_prefix_some hpreviousLe R.self_at
  have hoffset : R.offset = previous + 1 := by
    have hoffsetPositive : 0 < R.offset := R.offset_positive
    dsimp [previous]
    omega
  have hone : stepN w 1 before = some (R.branch, R.state) := by
    have hself := R.self_at
    rw [hoffset, stepN_add, hbefore] at hself
    exact hself
  have hstep : step w before = some (R.branch, R.state) := by
    simpa [stepN] using hone
  have hparts := step_some_parts hstep
  have hexit : exitPort before = R.branch :=
    w.link_injective hparts.1 R.self_link
  rcases before with ⟨p, state⟩
  have hexit' : (arrive state p).1 = R.branch := by
    simpa [exitPort] using hexit
  have hswitch := arrive_exit_switch state p
  rw [hexit'] at hswitch
  have hpSwitch : p / 3 = R.branch / 3 := hswitch.symm
  have hstemCases := arrive_stem_endpoint state p
  rw [hexit'] at hstemCases
  have hpStem : p = 3 * (p / 3) := by
    rcases hstemCases with hp | hbranchStem
    · exact hp
    · have : R.branch % 3 = 0 := by omega
      exact (R.branch_port this).elim
  have hpMod : p % 3 = 0 := by omega
  have hbranchEq :
      branchPort (p / 3) (state (p / 3)) = R.branch := by
    unfold arrive at hexit'
    rw [if_pos hpMod] at hexit'
    exact hexit'
  have hselectedBefore :
      state (R.branch / 3) = bval R.branch := by
    rw [hpSwitch] at hbranchEq
    have hcanonical :
        branchPort (R.branch / 3) (bval R.branch) = R.branch :=
      branchPort_bval R.branch_port
    cases hs : state (R.branch / 3) <;>
      cases hb : bval R.branch <;>
      simp [hs, hb, branchPort] at hbranchEq hcanonical ⊢ <;>
      omega
  have harrived : arrivedTongues (p, state) = state := by
    unfold arrivedTongues arrive
    rw [if_pos hpMod]
  have hstate : R.state = state := by
    exact hparts.2.trans harrived
  rw [hstate]
  exact hselectedBefore

/-- One live step from the self-linked branch exits through the stem edge,
with exactly the same tongue vector. -/
theorem RawCycleThroughSelfLink.branch_step
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    ∃ outside,
      w.link (3 * (R.branch / 3)) = some outside ∧
      stepN w 1 (R.branch, R.state) = some (outside, R.state) := by
  have hperiod := R.self_period
  obtain ⟨next, hnext⟩ := stepN_prefix_some
    (d := 1) (K := R.period) (by
      have hperiodPositive : 0 < R.period := R.period_positive
      omega) hperiod
  have hstep : step w (R.branch, R.state) = some next := by
    simpa [stepN] using hnext
  have hparts := step_some_parts hstep
  have harrive : arrive R.state R.branch =
      (3 * (R.branch / 3), R.state) := by
    have hpin : pin R.state R.branch = R.state :=
      pin_of_agrees R.self_selected
    simp [arrive, R.branch_port, hpin]
  rcases next with ⟨outside, nextState⟩
  have hmouth : w.link (3 * (R.branch / 3)) = some outside := by
    have hlink := hparts.1
    unfold exitPort at hlink
    rw [harrive] at hlink
    exact hlink
  have hnextState : nextState = R.state := by
    have hs := hparts.2
    unfold arrivedTongues at hs
    rw [harrive] at hs
    exact hs
  subst nextState
  exact ⟨outside, hmouth, hnext⟩

/-- Rotate once more to the outside of the self-link stem edge.  Thus the
cycle branch is already a literal raw periodic suffix at that outside
configuration. -/
theorem RawCycleThroughSelfLink.outside_period
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    ∃ outside,
      w.link (3 * (R.branch / 3)) = some outside ∧
      stepN w 1 (R.branch, R.state) = some (outside, R.state) ∧
      stepN w R.period (outside, R.state) = some (outside, R.state) := by
  obtain ⟨outside, hmouth, hout⟩ := R.branch_step
  have hperiod := R.self_period
  have hperiodPositive : 0 < R.period := R.period_positive
  have hsplit : R.period = 1 + (R.period - 1) := by omega
  have hreturn :
      stepN w (R.period - 1) (outside, R.state) =
        some (R.branch, R.state) := by
    rw [hsplit, stepN_add, hout] at hperiod
    exact hperiod
  have hsplit' : R.period = (R.period - 1) + 1 := by omega
  refine ⟨outside, hmouth, hout, ?_⟩
  rw [hsplit', stepN_add, hreturn]
  exact hout

/-- The self-link on the periodic orbit is an actual empty-runway identity
reflector, based at the state in which the raw orbit reaches it. -/
theorem RawCycleThroughSelfLink.stay_reflector
    {w : Wiring} {start : Nat × Tongues} {close : Nat}
    (R : RawCycleThroughSelfLink w start close) :
    ∃ outside,
      w.link (3 * (R.branch / 3)) = some outside ∧
      Nonempty (ManufacturedStayReflector w
        (3 * (R.branch / 3)) outside) := by
  obtain ⟨outside, hmouth, _hstep⟩ := R.branch_step
  exact ⟨outside, hmouth,
    self_link_core_stay_reflector
      R.branch_port R.self_link hmouth R.self_selected⟩

/-- Honest raw-time outcome of the certified placement theorem.  It does not
claim that the certified witness is in the image of `clock`.  Instead,
starting at the represented third opening, the independently certified raw
journey either encounters the self-link by the represented first closing, or
the closing configuration lies on a raw cycle which encounters that
self-link strictly inside one period. -/
def CertifiedSelfLinkRawEndpointOutcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S) : Prop :=
  (exists q shift,
    T.frames.openingAt S.i2 < shift ∧
    shift <= T.frames.closingAt S.i0 ∧
    stepN w shift start =
      some (C.run.entry q, C.run.boundary q) ∧
    w.link (C.run.entry q) = some (C.run.entry q)) ∨
  Nonempty (RawCycleThroughSelfLink w start
    (T.frames.closingAt S.i0))

/-- The physical self-link forced by the non-irreflexive branch, retaining
its exact location in the selected certified-ascent window. -/
def CertifiedSelfLinkInSelectedWindow
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S) : Prop :=
  exists q,
    C.clock (T.frames.openingAt S.i2) < q ∧
    q < C.clock (T.frames.closingAt S.i0) ∧
    w.link (C.run.entry q) = some (C.run.entry q)

/-- Unconditional certified placement of the self-link.  This is the timing
information that `forces_used_self_link` previously erased. -/
theorem CertifiedEndpointEmptyABCABC.forces_windowed_self_link
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S) :
    CertifiedSelfLinkInSelectedWindow C := by
  have hKb : C.K <= C.clock (T.frames.openingAt S.i2) := by
    exact Nat.le_trans C.base_before_first
      (Nat.le_of_lt (Nat.lt_trans C.selected_clock_order.1
        C.selected_clock_order.2.1))
  have hout := Echo.cyclic_minimal_stable_blocker_obstruction_bounded
    (canonicalEchoMachine w) (encodedEntries C.run.entry)
      C.run.initialRegister
      (certifiedConcreteEcho_isRun C.run) C.run.initialWellFormed
      C.tail C.crossing hKb C.selected_clock_order.2.1
      C.selected_clock_order.2.2 C.stable
  rcases hout with hlobe | hreplay | hfixed
  · obtain ⟨k, hk⟩ := hlobe
    exact (C.no_lobe k hk).elim
  · exact (C.no_replay hreplay).elim
  · obtain ⟨q, hqlo, hqhi, hfix⟩ := hfixed
    exact ⟨q, hqlo, hqhi,
      certified_fixed_encoded_entry_has_self_link C.run hfix⟩

/-- The certified placement has an unconditional raw endpoint
interpretation.  No surjectivity, monotonicity, or interpolation property of
`clock` is used. -/
theorem CertifiedEndpointEmptyABCABC.self_link_raw_endpoint_outcome
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    {S : SelectedFiveFrameABCABC T}
    (C : CertifiedEndpointEmptyABCABC S) :
    CertifiedSelfLinkRawEndpointOutcome C := by
  obtain ⟨q, hqOpen, hqClose, hself⟩ :=
    C.forces_windowed_self_link
  have hopenRaw := raw_configuration_at_of_productive
    (T.frames.opening_productiveAt S.i2)
  have hopen :
      stepN w (T.frames.openingAt S.i2) start =
        some
          (C.run.entry (C.clock (T.frames.openingAt S.i2)),
           C.run.boundary (C.clock (T.frames.openingAt S.i2))) := by
    rw [C.represents_open2.1, C.represents_open2.2]
    exact hopenRaw
  have hcloseRaw := raw_configuration_at_of_productive
    (T.frames.closing_productiveAt S.i0)
  have hclose :
      stepN w (T.frames.closingAt S.i0) start =
        some
          (C.run.entry (C.clock (T.frames.closingAt S.i0)),
           C.run.boundary (C.clock (T.frames.closingAt S.i0))) := by
    rw [C.represents_close0.1, C.represents_close0.2]
    exact hcloseRaw
  obtain ⟨toSelf, htoSelfPos, htoSelf⟩ :=
    C.run.ascent_order_raw_reach hqOpen
  obtain ⟨toClose, htoClosePos, htoClose⟩ :=
    C.run.ascent_order_raw_reach hqClose
  have hselfAbsolute :
      stepN w (T.frames.openingAt S.i2 + toSelf) start =
        some (C.run.entry q, C.run.boundary q) := by
    rw [stepN_add, hopen]
    exact htoSelf
  have hcloseCertified :
      stepN w ((T.frames.openingAt S.i2 + toSelf) + toClose) start =
        some
          (C.run.entry (C.clock (T.frames.closingAt S.i0)),
           C.run.boundary (C.clock (T.frames.closingAt S.i0))) := by
    rw [stepN_add, hselfAbsolute]
    exact htoClose
  by_cases hearly :
      T.frames.openingAt S.i2 + toSelf <=
        T.frames.closingAt S.i0
  · exact Or.inl ⟨q,
      T.frames.openingAt S.i2 + toSelf,
      by omega, hearly, hselfAbsolute, hself⟩
  · right
    let offset := T.frames.openingAt S.i2 + toSelf -
      T.frames.closingAt S.i0
    let period :=
      (T.frames.openingAt S.i2 + toSelf + toClose) -
        T.frames.closingAt S.i0
    have hoffsetPos : 0 < offset := by
      dsimp [offset]
      omega
    have hperiodPos : 0 < period := by
      dsimp [period]
      omega
    have hoffsetPeriod : offset < period := by
      dsimp [offset, period]
      omega
    have hperiodSum :
        T.frames.closingAt S.i0 + period =
          (T.frames.openingAt S.i2 + toSelf) + toClose := by
      dsimp [period]
      omega
    have hoffsetSum :
        T.frames.closingAt S.i0 + offset =
          T.frames.openingAt S.i2 + toSelf := by
      dsimp [offset]
      omega
    have hcycle :
        stepN w period
          (C.run.entry (C.clock (T.frames.closingAt S.i0)),
           C.run.boundary (C.clock (T.frames.closingAt S.i0))) =
          some
            (C.run.entry (C.clock (T.frames.closingAt S.i0)),
             C.run.boundary (C.clock (T.frames.closingAt S.i0))) := by
      have hadd := stepN_add w
        (T.frames.closingAt S.i0) period start
      rw [hclose] at hadd
      simp only [Option.bind_some] at hadd
      rw [hperiodSum, hcloseCertified] at hadd
      exact hadd.symm
    have hselfOnCycle :
        stepN w offset
          (C.run.entry (C.clock (T.frames.closingAt S.i0)),
           C.run.boundary (C.clock (T.frames.closingAt S.i0))) =
          some (C.run.entry q, C.run.boundary q) := by
      have hadd := stepN_add w
        (T.frames.closingAt S.i0) offset start
      rw [hclose] at hadd
      simp only [Option.bind_some] at hadd
      rw [hoffsetSum, hselfAbsolute] at hadd
      exact hadd.symm
    exact ⟨{
      closeConfig :=
        (C.run.entry (C.clock (T.frames.closingAt S.i0)),
         C.run.boundary (C.clock (T.frames.closingAt S.i0)))
      branch := C.run.entry q
      state := C.run.boundary q
      offset := offset
      period := period
      close_at := hclose
      period_positive := hperiodPos
      offset_positive := hoffsetPos
      offset_before_period := hoffsetPeriod
      cycle := hcycle
      self_at := hselfOnCycle
      branch_port := isDescentEntry_branch (C.run.freeSlot q).1
      self_link := hself
    }⟩

/-! ## Exact accounting at the five raw closes -/

/-- The five post-close sampling times, in their original chronological
order.  This is the literal finite set which the sharp argument must cover;
an eventual-tail statement is not a substitute for this list. -/
def FiveFixedStemNovelFrames.closePostTimes
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (F : FiveFixedStemNovelFrames w N start) : List Nat :=
  [F.z₀ + 1, F.z₁ + 1, F.z₂ + 1, F.z₃ + 1, F.z₄ + 1]

/-- A raw suffix whose restricted tongue vector is always one of two
explicit vectors.  The reach and liveness fields make the time shift exact;
there is no use of `getD` defaults. -/
structure RawTwoVectorTail
    (w : Wiring) (N : Nat) (start : Nat × Tongues) where
  shift : Nat
  localStart : Nat × Tongues
  phase₀ : List Bool
  phase₁ : List Bool
  reached : stepN w shift start = some localStart
  live : ∀ d, ∃ finish, stepN w d localStart = some finish
  two_vectors : ∀ d,
    restrictedTonguesAt w N localStart d ∈ [phase₀, phase₁]

/-- Closing times reflect the order of their `Fin 5` indices. -/
private theorem FiveRawClosingFrames.closingAt_lt_of_val_lt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4)
    (h01 : z0 < z1) (h12 : z1 < z2)
    (h23 : z2 < z3) (h34 : z3 < z4)
    {i j : Fin 5} (hij : i.1 < j.1) :
    F.closingAt i < F.closingAt j := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    omega
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    omega
  rcases hiCases with h | h | h | h | h <;> subst i <;>
    rcases hjCases with h | h | h | h | h <;> subst j <;>
    simp [FiveRawClosingFrames.closingAt] at hij ⊢ <;> omega

/-- Conversely, strict closing-time order forces strict index order. -/
private theorem FiveRawClosingFrames.val_lt_of_closingAt_lt
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    (F : FiveRawClosingFrames w N start z0 z1 z2 z3 z4)
    (h01 : z0 < z1) (h12 : z1 < z2)
    (h23 : z2 < z3) (h34 : z3 < z4)
    {i j : Fin 5} (hij : F.closingAt i < F.closingAt j) :
    i.1 < j.1 := by
  by_cases hval : i.1 < j.1
  · exact hval
  · have hji : j.1 ≤ i.1 := Nat.le_of_not_gt hval
    by_cases heq : j.1 = i.1
    · have hfin : j = i := Fin.ext heq
      subst j
      exact (Nat.lt_irrefl _ hij).elim
    · have hstrict : j.1 < i.1 := by omega
      have hback := F.closingAt_lt_of_val_lt
        h01 h12 h23 h34 hstrict
      omega

/-- In every selected chronological triple, the first selected frame is one
of the first three global frames.  Hence at most two close vectors precede
the selected raw window. -/
theorem SelectedFiveFrameABCABC.first_index_le_two
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {z0 z1 z2 z3 z4 : Nat}
    {T : FiveFrameTripleCase w N start z0 z1 z2 z3 z4}
    (h01 : z0 < z1) (h12 : z1 < z2)
    (h23 : z2 < z3) (h34 : z3 < z4)
    (S : SelectedFiveFrameABCABC T) : S.i0.1 ≤ 2 := by
  have hclose01 :
      T.frames.closingAt S.i0 < T.frames.closingAt S.i1 :=
    S.shape.2.2.2.1
  have hclose12 :
      T.frames.closingAt S.i1 < T.frames.closingAt S.i2 :=
    S.shape.2.2.2.2
  have hi01 := T.frames.val_lt_of_closingAt_lt
    h01 h12 h23 h34 hclose01
  have hi12 := T.frames.val_lt_of_closingAt_lt
    h01 h12 h23 h34 hclose12
  have hi2 : S.i2.1 < 5 := S.i2.2
  omega

/-- **Literal five-close four-cover.**  If a two-vector raw tail is reached
by the first close of the selected `ABCABC` triple, then all five original
post-close vectors have a `NoveltyCoverOn` of budget four.  The vectors before
the selected close are counted explicitly: there are respectively zero, one,
or two of them according as `i0 = 0, 1, 2`; the two tail vectors use the
remaining budget. -/
theorem five_close_noveltyCoverOn_four_of_two_vector_tail
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    (F : FiveFixedStemNovelFrames w N start)
    (T : FiveFrameTripleCase w N start
      F.z₀ F.z₁ F.z₂ F.z₃ F.z₄)
    (S : SelectedFiveFrameABCABC T)
    (P : RawTwoVectorTail w N start)
    (hbefore : P.shift ≤ T.frames.closingAt S.i0 + 1) :
    NoveltyCoverOn w N start F.closePostTimes [] 4 := by
  have hindex := S.first_index_le_two
    F.order₀₁ F.order₁₂ F.order₂₃ F.order₃₄
  have htail : ∀ t, P.shift ≤ t →
      restrictedTonguesAt w N start t ∈ [P.phase₀, P.phase₁] := by
    intro t ht
    let d := t - P.shift
    obtain ⟨finish, hfinish⟩ := P.live d
    have htransport := restrictedTonguesAt_add_of_reach
      (N := N) P.reached hfinish
    have hsum : P.shift + d = t := by
      dsimp [d]
      omega
    rw [hsum] at htransport
    rw [htransport]
    exact P.two_vectors d
  have hiCases : S.i0.1 = 0 ∨ S.i0.1 = 1 ∨ S.i0.1 = 2 := by
    omega
  have hz01 : F.z₀ < F.z₁ := F.order₀₁
  have hz12 : F.z₁ < F.z₂ := F.order₁₂
  have hz23 : F.z₂ < F.z₃ := F.order₂₃
  have hz34 : F.z₃ < F.z₄ := F.order₃₄
  rcases hiCases with hi0 | hi1 | hi2
  · have hfin : S.i0 = (0 : Fin 5) := Fin.ext hi0
    have hshift0 : P.shift ≤ F.z₀ + 1 := by
      simpa [hfin] using hbefore
    refine ⟨[P.phase₀, P.phase₁], by simp, ?_⟩
    intro t ht
    simp [FiveFixedStemNovelFrames.closePostTimes] at ht
    simp only [List.nil_append]
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact htail _ hshift0
    · exact htail _ (by omega)
    · exact htail _ (by omega)
    · exact htail _ (by omega)
    · exact htail _ (by omega)
  · have hfin : S.i0 = (1 : Fin 5) := Fin.ext hi1
    have hshift1 : P.shift ≤ F.z₁ + 1 := by
      simpa [hfin] using hbefore
    let pre := restrictedTonguesAt w N start (F.z₀ + 1)
    refine ⟨[pre, P.phase₀, P.phase₁], by simp, ?_⟩
    intro t ht
    simp [FiveFixedStemNovelFrames.closePostTimes] at ht
    simp only [List.nil_append]
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · simp [pre]
    · exact List.mem_cons_of_mem _ (htail _ hshift1)
    · exact List.mem_cons_of_mem _ (htail _ (by omega))
    · exact List.mem_cons_of_mem _ (htail _ (by omega))
    · exact List.mem_cons_of_mem _ (htail _ (by omega))
  · have hfin : S.i0 = (2 : Fin 5) := Fin.ext hi2
    have hshift2 : P.shift ≤ F.z₂ + 1 := by
      simpa [hfin] using hbefore
    let pre₀ := restrictedTonguesAt w N start (F.z₀ + 1)
    let pre₁ := restrictedTonguesAt w N start (F.z₁ + 1)
    refine ⟨[pre₀, pre₁, P.phase₀, P.phase₁], by simp, ?_⟩
    intro t ht
    simp [FiveFixedStemNovelFrames.closePostTimes] at ht
    simp only [List.nil_append]
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · simp [pre₀]
    · simp [pre₁]
    · exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (htail _ hshift2))
    · exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (htail _ (by omega)))
    · exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (htail _ (by omega)))

end GeneralN
