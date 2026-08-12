import TwoHistoryUnionChargeSharp

/-!
# The remaining flip-history surcharge is the old action switch

For a flip reflector the reusable support deliberately omits its facing
action switch, which is the unique source of the extra `+1` in the general
`N+3` two-history estimate.  If the second exploration never uses that
coordinate as one of its productive first-writer coordinates, then the action
switch itself can be inserted into the disjoint coordinate list.  The old
reusable coordinates plus the second first-writer coordinates therefore use
at most `N-1` switches, and the preserved history again has size `N+2`.
-/

namespace GeneralN

private theorem nplus4_nodup_filter_nat (p : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hm => hnd.1 ((List.mem_filter.mp hm).1), ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem nplus4_nodup_map_nat_of_injective_on
    {f : Nat → Nat} {xs : List Nat}
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y)
    (hnd : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
        have hxy := hinj x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih
          (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb)) hnd.2

/-- If the second first-writer coordinates avoid the first flip action switch,
then the reusable/fresh coordinate charge improves by one. -/
theorem ManufacturedFlipReflector.reusable_add_second_first_writers_le_pred
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (hactionUnused : ∀ k,
      k ∈ rawFirstWriterTimes w N (e, B.baseState) B.exploration.length →
      rawWriterAt w (e, B.baseState) k ≠ R.actionSwitch) :
    (ManufacturedReflector.flip R).reusableSwitches.length +
      (rawFirstWriterTimes w N (e, B.baseState)
        B.exploration.length).length + 1 ≤ N := by
  classical
  let A : ManufacturedReflector w g e := .flip R
  let times := rawFirstWriterTimes w N (e, B.baseState)
    B.exploration.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact nplus4_nodup_filter_nat _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply nplus4_nodup_map_nat_of_injective_on
    · intro i hi j hj hEq
      have hiData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hi)
      have hjData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hj)
      exact rawFirstWriterAt_injective hiData.2 hjData.2 hEq
    · exact htimesNodup
  have hdisjoint : ∀ oldSwitch ∈ A.reusableSwitches,
      ∀ freshSwitch ∈ writers, oldSwitch ≠ freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside := A.second_exploration_productive_writer_not_reusable
      hN B hbaseGrooves hpreGrooves hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  have hactionNotReusable : R.actionSwitch ∉ A.reusableSwitches := by
    intro hm
    obtain ⟨path, hpath, passage, hp, hswitch⟩ :=
      A.mem_reusableSwitches hm
    have hforeign := R.support_foreign path hpath passage hp
    exact hforeign hswitch
  have hactionNotWriters : R.actionSwitch ∉ writers := by
    intro hm
    obtain ⟨k, hk, hwriter⟩ := List.mem_map.mp hm
    have hk' : k ∈ times := hk
    have hne := hactionUnused k (by simpa [times] using hk')
    exact hne hwriter
  have hunionNodup : (A.reusableSwitches ++ writers).Nodup := by
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  let switches := R.actionSwitch :: (A.reusableSwitches ++ writers)
  have hnd : switches.Nodup := by
    dsimp [switches]
    rw [List.nodup_cons]
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hold | hfresh
      · exact hactionNotReusable hold
      · exact hactionNotWriters hfresh
    · exact hunionNodup
  have hactionLt : R.actionSwitch < N := by
    have h := A.exploration_trace.switch_lt hN
      (R.mouth, R.firstArm)
      (by simp [A, ManufacturedReflector.exploration])
    simpa [passageSwitch, ManufacturedFlipReflector.actionSwitch] using h
  have hlt : ∀ C ∈ switches, C < N := by
    intro C hC
    dsimp [switches] at hC
    rcases List.mem_cons.mp hC with rfl | hrest
    · exact hactionLt
    · rcases List.mem_append.mp hrest with hOld | hFresh
      · exact A.reusableSwitch_lt hN hOld
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
        have hkData := mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using hk)
        exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hnd hlt
  have hlen : switches.length =
      1 + A.reusableSwitches.length + times.length := by
    simp [switches, writers]
  rw [hlen] at hbound
  have hchargeA : A.reusableSwitches.length + times.length + 1 ≤ N := by
    omega
  simpa [A, times] using hchargeA

/-- Consequently the flip-first preserved two-history core also has size
`N+2` unless the second exploration has a first-writer event at the old action
switch. -/
theorem ManufacturedFlipReflector.preservedTwoHistoryCore_length_le_N_add_two_of_action_unused
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = (ManufacturedReflector.flip R).activatedState)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (hactionUnused : ∀ k,
      k ∈ rawFirstWriterTimes w N (e, B.baseState) B.exploration.length →
      rawWriterAt w (e, B.baseState) k ≠ R.actionSwitch) :
    ((ManufacturedReflector.flip R).preservedTwoHistoryCore B N).length ≤
      N + 2 := by
  let A : ManufacturedReflector w g e := .flip R
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase, A]
  have hcharge := R.reusable_add_second_first_writers_le_pred
    hN B hbaseGrooves hpreGrooves hactionUnused
  have hchargeA : A.reusableSwitches.length +
      (rawFirstWriterTimes w N (e, B.baseState)
        B.exploration.length).length + 1 ≤ N := by
    simpa [A] using hcharge
  have hexploration : A.exploration.length = A.reusableSwitches.length + 1 := by
    simp [A, ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches, Nat.add_assoc]
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length, hexploration]
  omega

end GeneralN
