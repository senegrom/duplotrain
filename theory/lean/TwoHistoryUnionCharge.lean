import JourneyReachesActivated
import ProtectedRepairFour

/-!
# Charging two opposite construction histories once

The coefficient-two estimate appends the two canonical manufactured-reflector
histories and pays for every switch occurrence twice.  This file isolates the
real obstruction.  Away from an old reusable support, the second exploration
uses globally fresh switch coordinates; the only switch of the first
exploration omitted from that support is the facing action mouth.  Thus the
two raw histories, with their common boundary erased, have size at most
`N + 4`.  If this estimate cannot be applied, the raw second exploration
contains a concrete first old-support contact.  If that contact actually
breaks the old grooves, the existing causal theorem exposes the exact return
or outward state-changing event responsible for the second charge.

All statements are over `Wiring`, `PhysicalTrace`, and `stepN`, for arbitrary
`N`.  No overlap of the two histories is assumed.
-/

namespace GeneralN

private theorem nodup_subset_length_two_history
    {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs cover : List α},
      xs.Nodup →
      (∀ x ∈ xs, x ∈ cover) →
      xs.length ≤ cover.length := by
  intro xs
  induction xs with
  | nil =>
      intro cover _ _
      exact Nat.zero_le _
  | cons x rest ih =>
      intro cover hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ cover := hsub x List.mem_cons_self
      have hrest : ∀ y ∈ rest, y ∈ cover.erase x := by
        intro y hy
        have hyCover : y ∈ cover :=
          hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun heq => hnd.1 (heq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyCover
      have hle := ih hnd.2 hrest
      have herase : (cover.erase x).length = cover.length - 1 :=
        List.length_erase_of_mem hx
      have hpositive : 0 < cover.length := by
        cases cover with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

private theorem nodup_filter_nat_two_history (p : Nat → Bool) :
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
          exact ⟨fun hmem => hnd.1 ((List.mem_filter.mp hmem).1),
            ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem nodup_map_nat_of_injective_on_two_history
    {f : Nat → Nat} {xs : List Nat}
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs →
      f x = f y → x = y)
    (hnd : xs.Nodup) :
    (xs.map f).Nodup := by
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
          (fun a ha b hb => hinj a
            (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb))
          hnd.2

private theorem count_map_range_two_of_eq
    {α : Type} [BEq α] [LawfulBEq α]
    (f : Nat → α) :
    ∀ {n i j : Nat},
      i < j → j < n → f i = f j →
      2 ≤ ((List.range n).map f).count (f i) := by
  intro n
  induction n with
  | zero =>
      intro i j hij hj _
      omega
  | succ n ih =>
      intro i j hij hj hEq
      rw [List.range_succ, List.map_append, List.count_append]
      by_cases hjLast : j = n
      · subst j
        have hi : i < n := by omega
        have hmem : f i ∈ (List.range n).map f := by
          apply List.mem_map.mpr
          exact ⟨i, List.mem_range.mpr hi, rfl⟩
        have hone : 1 ≤ ((List.range n).map f).count (f i) :=
          List.one_le_count_iff.mpr hmem
        have hsingle : ([n].map f).count (f i) = 1 := by
          simp [← hEq]
        omega
      · have hjn : j < n := by omega
        have htwo := ih hij hjn hEq
        omega

private theorem mem_erase_of_count_two
    {α : Type} [BEq α] [LawfulBEq α]
    {x y : α} {xs : List α}
    (htwo : 2 ≤ xs.count x)
    (hy : y ∈ xs) :
    y ∈ xs.erase x := by
  by_cases hyx : y = x
  · subst y
    apply List.count_pos_iff.mp
    rw [List.count_erase_self]
    omega
  · exact (List.mem_erase_of_ne hyx).mpr hy
private theorem physicalTrace_head_step_two_history
    {w : Wiring} {p x : Nat} {u : Tongues}
    {rest : List Passage} {finish : Nat × Tongues}
    (h : PhysicalTrace w (p, u) ((p, x) :: rest) finish) :
    ∃ q v,
      arrive u p = (x, v) ∧
      stepN w 1 (p, u) = some (q, v) := by
  cases h with
  | @cons _ _ q _ v _ _ harrive hlink tail =>
      refine ⟨q, v, harrive, ?_⟩
      simp [stepN, step, harrive, hlink]

/-- In a switch-simple trace, a productive passage leaves a permanent
change at its switch.  Simplicity excludes that switch from both the strict
prefix and strict suffix, so neither side can hide or repair the write. -/
theorem PhysicalTrace.simple_changed_passage_survives
    {w : Wiring} {start finish : Nat × Tongues}
    {passages before after : List Passage}
    {p x : Nat} {u v : Tongues}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hsplit : passages = before ++ (p, x) :: after)
    (hprefix : PhysicalTrace w start before (p, u))
    (harrive : arrive u p = (x, v))
    (hchanged :
      v (passageSwitch (p, x)) ≠ u (passageSwitch (p, x))) :
    finish.2 (passageSwitch (p, x)) ≠
      start.2 (passageSwitch (p, x)) := by
  have htrace' := htrace
  have hsimple' := hsimple
  rw [hsplit] at htrace' hsimple'
  obtain ⟨middle, hbefore, hrest⟩ := htrace'.split_append
  have hmiddle : middle = (p, u) := by
    have hactual := hbefore.sound
    have hgiven := hprefix.sound
    rw [hgiven] at hactual
    exact (Option.some.inj hactual).symm
  subst middle
  cases hrest with
  | @cons _ _ q _ v' _ _ harrive' _hlink hafter =>
      have hv' : v' = v := by
        rw [harrive] at harrive'
        exact (Prod.mk.inj harrive').2.symm
      subst v'
      unfold SwitchSimple at hsimple'
      simp only [List.map_append, List.map_cons] at hsimple'
      have hparts := List.nodup_append.mp hsimple'
      have hprefixForeign :
          ∀ prior ∈ before,
            passageSwitch prior ≠ passageSwitch (p, x) := by
        intro prior hprior hEq
        have hne := hparts.2.2 (passageSwitch prior)
          (List.mem_map.mpr ⟨prior, hprior, rfl⟩)
          (passageSwitch (p, x)) (by simp)
        exact hne hEq
      have hsuffixForeign :
          ∀ later ∈ after,
            passageSwitch later ≠ passageSwitch (p, x) := by
        have hheadTail := hparts.2.1
        rw [List.nodup_cons] at hheadTail
        intro later hlater hEq
        apply hheadTail.1
        exact List.mem_map.mpr ⟨later, hlater, hEq⟩
      have hu := hprefix.preserves
        (passageSwitch (p, x)) hprefixForeign
      have hv := hafter.preserves
        (passageSwitch (p, x)) hsuffixForeign
      intro hfinish
      apply hchanged
      calc
        v (passageSwitch (p, x)) =
            finish.2 (passageSwitch (p, x)) := hv.symm
        _ = start.2 (passageSwitch (p, x)) := hfinish
        _ = u (passageSwitch (p, x)) := hu.symm

/-- Raw-time form of
`PhysicalTrace.simple_changed_passage_survives`: every productive event
inside a switch-simple physical trace leaves its writer changed at the
trace endpoint. -/
theorem PhysicalTrace.simple_raw_productive_writer_survives
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    {k : Nat} (hk : k < passages.length)
    (hprod : RawProductiveAt w N start k) :
    finish.2 (rawWriterAt w start k) ≠
      start.2 (rawWriterAt w start k) := by
  let old : Passage := passages[k]
  have hsplit :
      passages =
        passages.take k ++ old :: passages.drop (k + 1) := by
    calc
      passages = passages.take k ++ passages.drop k :=
        (List.take_append_drop k passages).symm
      _ = passages.take k ++ old :: passages.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hk]
  have htrace' := htrace
  rw [hsplit] at htrace'
  obtain ⟨atOld, hprefix, htail⟩ := htrace'.split_append
  obtain ⟨cur, next, hcur, _hnext, hstep, hchange⟩ :=
    rawProductiveAt_changes_writer hN hprod
  have hprefixSound := hprefix.sound
  rw [List.length_take_of_le (Nat.le_of_lt hk)] at hprefixSound
  have hatOld : atOld = cur := by
    rw [hcur] at hprefixSound
    exact (Option.some.inj hprefixSound).symm
  subst atOld
  have hhead := htail.head_arrive
  have hentry : cur.1 = old.1 := hhead.1
  obtain ⟨afterOld, harriveOld⟩ := hhead.2
  have harriveOld' :
      arrive cur.2 old.1 = (old.2, afterOld) := by
    simpa [old] using harriveOld
  have hnextTongue : next.2 = afterOld := by
    calc
      next.2 = (arrive cur.2 cur.1).2 :=
        (step_some_parts hstep).2
      _ = afterOld := by
        rw [hentry, harriveOld']
  have harriveProductive :
      arrive cur.2 old.1 = (old.2, next.2) := by
    rw [harriveOld', hnextTongue]
  have hprefix' :
      PhysicalTrace w start (passages.take k)
        (old.1, cur.2) := by
    simpa [← hentry] using hprefix
  have hchangedOld :
      next.2 (passageSwitch old) ≠
        cur.2 (passageSwitch old) := by
    simpa [passageSwitch, ← hentry] using hchange
  have hsurvives :=
    htrace.simple_changed_passage_survives hsimple hsplit
      hprefix' harriveProductive hchangedOld
  have hwriter :=
    htrace.rawWriterAt_eq_passageSwitch_getElem hk
  simpa [old, hwriter] using hsurvives

/-- A reflector's manufacturing exploration is exactly the selected outward
route in its base state.  This identifies the second construction with the
active-lead API after swapping the two opposite reflectors. -/
theorem ManufacturedReflector.orientedRoute_baseState_eq_exploration
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.orientedRoute A.baseState = A.exploration := by
  cases A with
  | stay R =>
      rfl
  | flip R =>
      have hmouthSelected :
          R.mouthState R.actionSwitch = bval R.firstArm := by
        obtain ⟨after, hhead⟩ := R.candyTrace.head_arrive.2
        have hm : R.mouth % 3 = 0 := R.mouth_is_stem
        unfold arrive at hhead
        rw [if_pos hm] at hhead
        have hbranch :
            branchPort R.actionSwitch
              (R.mouthState R.actionSwitch) = R.firstArm := by
          simpa [ManufacturedFlipReflector.actionSwitch] using
            congrArg Prod.fst hhead
        have hrecovered :
            branchPort R.actionSwitch (bval R.firstArm) =
              R.firstArm := by
          simpa [R.firstArm_switch] using
            (branchPort_bval R.firstArm_branch)
        have hsame :
            branchPort R.actionSwitch
                (R.mouthState R.actionSwitch) =
              branchPort R.actionSwitch (bval R.firstArm) :=
          hbranch.trans hrecovered.symm
        cases hs : R.mouthState R.actionSwitch <;>
          cases hf : bval R.firstArm <;>
          simp [branchPort, hs, hf] at hsame ⊢ <;> omega
      have hforeign :
          ∀ passage ∈ R.runway,
            passageSwitch passage ≠ R.actionSwitch := by
        have hsimple := R.simple
        unfold SwitchSimple at hsimple
        simp only [List.map_append, List.map_cons] at hsimple
        have hparts := List.nodup_append.mp hsimple
        intro passage hp hEq
        have hleft : passageSwitch passage ∈
            R.runway.map passageSwitch :=
          List.mem_map.mpr ⟨passage, hp, rfl⟩
        have hright : R.actionSwitch ∈
            (passageSwitch (R.mouth, R.firstArm) ::
              R.candy.map passageSwitch) := by
          simp [passageSwitch,
            ManufacturedFlipReflector.actionSwitch]
        exact hparts.2.2 _ hleft _ hright hEq
      have hpreserve :=
        R.runwayTrace.preserves R.actionSwitch hforeign
      have hbaseSelected :
          R.base R.actionSwitch = bval R.firstArm := by
        calc
          R.base R.actionSwitch = R.mouthState R.actionSwitch :=
            hpreserve.symm
          _ = bval R.firstArm := hmouthSelected
      change
        (if R.base R.actionSwitch = bval R.firstArm then
          R.runway ++ (R.mouth, R.firstArm) :: R.candy
        else
          R.runway ++ (R.mouth, R.secondArm) ::
            reversePassages R.candy) =
          R.runway ++ (R.mouth, R.firstArm) :: R.candy
      rw [if_pos hbaseSelected]


/-- Switch coordinates belonging to the reusable support of a manufactured
reflector.  For a flip reflector this deliberately omits the facing action
mouth; that passage cannot itself change a tongue. -/
def ManufacturedReflector.reusableSwitches
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : List Nat :=
  match A with
  | .stay R => (R.runway ++ [(R.mouth, R.arm)]).map passageSwitch
  | .flip R => (R.runway ++ R.candy).map passageSwitch

/-- The reusable support is switch-simple. -/
theorem ManufacturedReflector.reusableSwitches_nodup
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.reusableSwitches.Nodup := by
  cases A with
  | stay R =>
      simpa [ManufacturedReflector.reusableSwitches,
        ManufacturedReflector.exploration, SwitchSimple] using R.simple
  | flip R =>
      have hs := R.simple
      unfold SwitchSimple at hs
      simp only [List.map_append, List.map_cons] at hs
      have hparts := List.nodup_append.mp hs
      have hout : (R.runway.map passageSwitch ++
          R.candy.map passageSwitch).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hparts.1, (List.nodup_cons.mp hparts.2.1).2, ?_⟩
        intro a ha b hb hab
        exact hparts.2.2 a ha b (List.mem_cons_of_mem _ hb) hab
      simpa only [ManufacturedReflector.reusableSwitches,
        List.map_append] using hout

/-- Membership in `reusableSwitches` is exactly membership in one of the
two reusable support paths. -/
theorem ManufacturedReflector.mem_reusableSwitches
    {w : Wiring} {g e k : Nat}
    (A : ManufacturedReflector w g e)
    (hk : k ∈ A.reusableSwitches) :
    ∃ path ∈ A.toSupported.paths, ∃ passage ∈ path,
      passageSwitch passage = k := by
  cases A with
  | stay R =>
      change ∃ path ∈ [R.runway, [(R.mouth, R.arm)]],
        ∃ passage ∈ path, passageSwitch passage = k
      change k ∈ (R.runway ++ [(R.mouth, R.arm)]).map passageSwitch at hk
      obtain ⟨passage, hpassage, hswitch⟩ := List.mem_map.mp hk
      rcases List.mem_append.mp hpassage with hrunway | hcore
      · exact ⟨R.runway, by simp, passage, hrunway, hswitch⟩
      · have hp : passage = (R.mouth, R.arm) := by simpa using hcore
        subst passage
        exact ⟨[(R.mouth, R.arm)], by simp,
          (R.mouth, R.arm), by simp, hswitch⟩
  | flip R =>
      change ∃ path ∈ [R.runway, R.candy],
        ∃ passage ∈ path, passageSwitch passage = k
      change k ∈ (R.runway ++ R.candy).map passageSwitch at hk
      obtain ⟨passage, hpassage, hswitch⟩ := List.mem_map.mp hk
      rcases List.mem_append.mp hpassage with hrunway | hcandy
      · exact ⟨R.runway, by simp, passage, hrunway, hswitch⟩
      · exact ⟨R.candy, by simp, passage, hcandy, hswitch⟩

theorem ManufacturedReflector.second_exploration_productive_writer_not_reusable
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    {k : Nat} (hk : k < B.exploration.length)
    (hprod :
      RawProductiveAt w N (e, B.baseState) k) :
    rawWriterAt w (e, B.baseState) k ∉
      A.reusableSwitches := by
  intro hreusable
  have hsurvives :=
    B.exploration_trace.simple_raw_productive_writer_survives
      hN B.exploration_simple hk hprod
  obtain ⟨path, hpath, old, hold, hswitch⟩ :=
    A.mem_reusableSwitches hreusable
  have hbaseOld := hbaseGrooves path hpath old hold
  have hpreOld := hpreGrooves path hpath old hold
  have hagree :=
    grooved_states_agree_on_passage hbaseOld hpreOld
  have hexit :
      old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch B.baseState old.2
    rw [hbaseOld] at hs
    exact hs.symm
  apply hsurvives
  calc
    B.preReturn.2 (rawWriterAt w (e, B.baseState) k) =
        B.preReturn.2 (old.2 / 3) := by
          rw [hexit, hswitch]
    _ = B.baseState (old.2 / 3) := hagree.symm
    _ = B.baseState (rawWriterAt w (e, B.baseState) k) := by
          rw [hexit, hswitch]


/-- Removing the facing action mouth loses at most one exploration switch. -/
theorem ManufacturedReflector.exploration_length_le_reusable_add_one
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.exploration.length ≤ A.reusableSwitches.length + 1 := by
  cases A <;>
    simp [ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches] <;> omega

/-- If the second construction avoids the first reusable support, the two
coordinate lists share no element. -/
theorem ManufacturedReflector.reusable_append_exploration_nodup
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (havoid : A.SupportAvoidsExploration B) :
    (A.reusableSwitches ++
      B.exploration.map passageSwitch).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨A.reusableSwitches_nodup, B.exploration_simple, ?_⟩
  intro a ha b hb hab
  obtain ⟨path, hpath, passage, hpassage, hpassageSwitch⟩ :=
    A.mem_reusableSwitches ha
  have hnot := havoid path hpath passage hpassage
  apply hnot
  obtain ⟨fresh, hfresh, hfreshSwitch⟩ := List.mem_map.mp hb
  apply List.mem_map.mpr
  refine ⟨fresh, hfresh, ?_⟩
  exact hfreshSwitch.trans (hab ▸ hpassageSwitch.symm)

/-- Every reusable support coordinate is within the ambient switch bound. -/
theorem ManufacturedReflector.reusableSwitch_lt
    {w : Wiring} {N g e k : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (hk : k ∈ A.reusableSwitches) : k < N := by
  cases A with
  | stay R =>
      change k ∈ (R.runway ++ [(R.mouth, R.arm)]).map passageSwitch at hk
      obtain ⟨passage, hpassage, rfl⟩ := List.mem_map.mp hk
      apply (ManufacturedReflector.stay R).exploration_trace.switch_lt
        hN passage
      simpa [ManufacturedReflector.exploration] using hpassage
  | flip R =>
      change k ∈ (R.runway ++ R.candy).map passageSwitch at hk
      obtain ⟨passage, hpassage, rfl⟩ := List.mem_map.mp hk
      apply (ManufacturedReflector.flip R).exploration_trace.switch_lt
        hN passage
      rcases List.mem_append.mp hpassage with hrunway | hcandy
      · exact List.mem_append_left _ hrunway
      · exact List.mem_append_right R.runway
          (List.mem_cons_of_mem _ hcandy)

/-- Coefficient-one coordinate charge in the groove-preserved branch.
The first reflector's reusable switches and all productive first writers of
the second simple exploration are disjoint and together occupy at most the
`N` available switch coordinates. -/
theorem ManufacturedReflector.reusable_add_second_first_writers_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2) :
    A.reusableSwitches.length +
      (rawFirstWriterTimes w N (e, B.baseState)
        B.exploration.length).length ≤ N := by
  classical
  let times :=
    rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact nodup_filter_nat_two_history _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply nodup_map_nat_of_injective_on_two_history
    · intro i hi j hj hEq
      have hiData :=
        mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using hi)
      have hjData :=
        mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using hj)
      exact rawFirstWriterAt_injective
        hiData.2 hjData.2 hEq
    · exact htimesNodup
  have hdisjoint :
      ∀ oldSwitch ∈ A.reusableSwitches,
        ∀ freshSwitch ∈ writers,
          oldSwitch ≠ freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData :=
      mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hk)
    have houtside :=
      A.second_exploration_productive_writer_not_reusable
        hN B hbaseGrooves hpreGrooves
          hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let switches := A.reusableSwitches ++ writers
  have hnd : switches.Nodup := by
    dsimp [switches]
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  have hlt : ∀ C ∈ switches, C < N := by
    intro C hC
    rcases List.mem_append.mp hC with hOld | hFresh
    · exact A.reusableSwitch_lt hN hOld
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
      have hkData :=
        mem_rawFirstWriterTimes_iff.mp (by
          simpa [times] using hk)
      exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hnd hlt
  have hlength :
      A.reusableSwitches.length + times.length ≤ N := by
    simpa [switches, writers] using hbound
  simpa [times] using hlength
/-- The second construction compressed to its initial vector, the post-vector
of each productive first writer in the switch-simple exploration, and its
single activated endpoint.  Quiet old-support passages create no entry. -/
noncomputable def ManufacturedReflector.writerConstructionHistory
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w g e) (N : Nat) :
    List (List Bool) :=
  rawFirstWriterHistory w N (g, B.baseState)
      B.exploration.length ++
    [VectorCount.restrict N B.activatedState]

/-- The compressed writer history represents every vector of the ordinary
sharp construction history. -/
theorem ManufacturedReflector.mem_writerConstructionHistory_of_mem_sharp
    {w : Wiring} {N g e : Nat}
    (B : ManufacturedReflector w g e)
    {x : List Bool}
    (hx : x ∈ B.sharpConstructionHistory N) :
    x ∈ B.writerConstructionHistory N := by
  classical
  unfold ManufacturedReflector.sharpConstructionHistory at hx
  rcases List.mem_append.mp hx with hprefix | hactivated
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hprefix
    apply List.mem_append_left
    apply B.exploration_trace.restrictedTonguesAt_mem_rawFirstWriterHistory
      B.exploration_simple j
    have hjlt := List.mem_range.mp hj
    omega
  · apply List.mem_append_right
    simpa using hactivated

/-- Exact size of the compressed writer history. -/
theorem ManufacturedReflector.writerConstructionHistory_length
    {w : Wiring} {N g e : Nat}
    (B : ManufacturedReflector w g e) :
    (B.writerConstructionHistory N).length =
      (rawFirstWriterTimes w N (g, B.baseState)
        B.exploration.length).length + 2 := by
  simp [ManufacturedReflector.writerConstructionHistory,
    rawFirstWriterHistory]


/-- The disjoint reusable/fresh coordinate charge is global: together the
two lists consume at most the `N` available switches. -/
theorem ManufacturedReflector.reusable_add_second_exploration_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (havoid : A.SupportAvoidsExploration B) :
    A.reusableSwitches.length + B.exploration.length ≤ N := by
  let switches := A.reusableSwitches ++
    B.exploration.map passageSwitch
  have hnd : switches.Nodup := by
    simpa [switches] using A.reusable_append_exploration_nodup B havoid
  have hlt : ∀ k ∈ switches, k < N := by
    intro k hk
    rcases List.mem_append.mp hk with hA | hB
    · exact A.reusableSwitch_lt hN hA
    · obtain ⟨passage, hpassage, rfl⟩ := List.mem_map.mp hB
      exact B.exploration_trace.switch_lt hN passage hpassage
  have hbound := nodup_nat_lt_length hnd hlt
  simpa [switches] using hbound

/-- Consequently, the two complete simple explorations cost only `N+1`
passages: the sole extra slot is the first reflector's facing action mouth. -/
theorem ManufacturedReflector.two_explorations_length_le_N_add_one
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (havoid : A.SupportAvoidsExploration B) :
    A.exploration.length + B.exploration.length ≤ N + 1 := by
  have hsupport := A.reusable_add_second_exploration_le hN B havoid
  have hA := A.exploration_length_le_reusable_add_one
  omega

/-- **Two-history union charge, support-avoiding branch.**

The second history begins at the first activated vector, so that boundary is
erased once.  No deduplication beyond this guaranteed boundary is used.  The
raw concatenation itself therefore has size at most `N+4`; every genuinely
new second-history vertex is already covered by this list. -/
theorem ManufacturedReflector.two_sharp_histories_length_le_N_add_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (havoid : A.SupportAvoidsExploration B) :
    (A.sharpConstructionHistory N ++
      (B.sharpConstructionHistory N).erase
        (VectorCount.restrict N A.activatedState)).length ≤ N + 4 := by
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.sharpConstructionHistory N := by
    unfold ManufacturedReflector.sharpConstructionHistory
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
    simp [restrictedTonguesAt, tonguesAt, stepN, hbase]
  have herase := List.length_erase_of_mem hboundary
  have hpaths := A.two_explorations_length_le_N_add_one hN B havoid
  simp only [ManufacturedReflector.sharpConstructionHistory,
    List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil] at herase ⊢
  omega

/-! ## Removing the internal duplicate of each sharp history -/

/-- The facing mouth passage of a nondegenerate manufactured reflector does
not change a tongue.  Consequently the state at the end of the runway occurs
again one passage later in the sharp exploration prefix. -/
private theorem ManufacturedFlipReflector.runway_boundary_repeated
    {w : Wiring} {g e N : Nat}
    (R : ManufacturedFlipReflector w g e) :
    restrictedTonguesAt w N (g, R.base) R.runway.length =
      restrictedTonguesAt w N (g, R.base) (R.runway.length + 1) := by
  have hAtRunway :
      tonguesAt w (g, R.base) R.runway.length = R.mouthState := by
    simp [tonguesAt, R.runwayTrace.sound]
  have hstepOne :
      ∃ q, stepN w 1 (R.mouth, R.mouthState) =
        some (q, R.mouthState) := by
    have htrace := R.candyTrace
    cases htrace with
    | @cons p x q u v passages finish harrive hlink tail =>
        have hv : v = R.mouthState := by
          unfold arrive at harrive
          rw [if_pos R.mouth_is_stem] at harrive
          exact (Prod.mk.inj harrive).2.symm
        refine ⟨q, ?_⟩
        simp [stepN, step, harrive, hlink, hv]
  have hAtNext :
      tonguesAt w (g, R.base) (R.runway.length + 1) =
        R.mouthState := by
    have hlive :
        ∃ finish, stepN w 1 (R.mouth, R.mouthState) = some finish := by
      obtain ⟨q, hq⟩ := hstepOne
      exact ⟨(q, R.mouthState), hq⟩
    have hshift := tonguesAt_add_of_reaches
      (K := R.runway.length) (d := 1) R.runwayTrace.sound hlive
    obtain ⟨q, hq⟩ := hstepOne
    rw [hshift]
    simp [tonguesAt, hq]
  simp only [restrictedTonguesAt]
  rw [hAtRunway, hAtNext]

/-- A canonical value that occurs twice in every sharp construction history.
For a stay reflector it is the pre-return/activated value.  For a flip
reflector it is the unchanged value on the two sides of the facing mouth
passage. -/
def ManufacturedReflector.sharpHistoryDuplicate
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : List Bool :=
  match A with
  | .stay R => VectorCount.restrict N R.returnState
  | .flip R =>
      restrictedTonguesAt w N (g, R.base) R.runway.length

/-- Every sharp construction history has an internal repetition, independent
of any relation to a second history. -/
theorem ManufacturedReflector.sharpHistoryDuplicate_count
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e) :
    2 ≤ (A.sharpConstructionHistory N).count
      (A.sharpHistoryDuplicate N) := by
  cases A with
  | stay R =>
      let f := restrictedTonguesAt w N (g, R.base)
      let x := VectorCount.restrict N R.returnState
      have hxPrefix :
          x ∈ (List.range
            ((R.runway ++ [(R.mouth, R.arm)]).length + 1)).map f := by
        apply List.mem_map.mpr
        refine ⟨(R.runway ++ [(R.mouth, R.arm)]).length,
          List.mem_range.mpr (by omega), ?_⟩
        dsimp [f, x]
        have hs :
            stepN w (R.runway.length + 1) (g, R.base) =
              some (R.arm, R.returnState) := by
          simpa [
          ManufacturedReflector.exploration,
            ManufacturedReflector.baseState,
            ManufacturedReflector.preReturn] using
              (ManufacturedReflector.stay R).exploration_trace.sound
        simp [restrictedTonguesAt, tonguesAt, hs]
      change 2 ≤
        (((List.range
          ((R.runway ++ [(R.mouth, R.arm)]).length + 1)).map f) ++
            [x]).count x
      rw [List.count_append]
      have hone :
          1 ≤ ((List.range
            ((R.runway ++ [(R.mouth, R.arm)]).length + 1)).map f).count x :=
        List.one_le_count_iff.mpr hxPrefix
      have hsingle : [x].count x = 1 := by simp
      omega
  | flip R =>
      let f := restrictedTonguesAt w N (g, R.base)
      have hEq : f R.runway.length = f (R.runway.length + 1) := by
        exact R.runway_boundary_repeated
      have hnext :
          R.runway.length + 1 <
            (R.runway ++ (R.mouth, R.firstArm) :: R.candy).length + 1 := by
        simp only [List.length_append, List.length_cons]
        omega
      have hprefix := count_map_range_two_of_eq f
        (n :=
          (R.runway ++ (R.mouth, R.firstArm) :: R.candy).length + 1)
        (i := R.runway.length) (j := R.runway.length + 1)
        (by omega) hnext hEq
      change 2 ≤
        (((List.range
          ((R.runway ++ (R.mouth, R.firstArm) :: R.candy).length + 1)).map f) ++
            [VectorCount.restrict N R.afterReturn]).count
              (f R.runway.length)
      rw [List.count_append]
      omega

/-- The sharp history with one guaranteed internal repetition removed. -/
def ManufacturedReflector.sharpHistoryCore
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : List (List Bool) :=
  (A.sharpConstructionHistory N).erase (A.sharpHistoryDuplicate N)

/-- Erasing the canonical duplicate loses no represented tongue vector. -/
theorem ManufacturedReflector.mem_sharpHistoryCore_of_mem
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    {x : List Bool}
    (hx : x ∈ A.sharpConstructionHistory N) :
    x ∈ A.sharpHistoryCore N := by
  exact mem_erase_of_count_two A.sharpHistoryDuplicate_count hx

/-- The compressed sharp history costs exactly one more vector than the
simple exploration has passages. -/
theorem ManufacturedReflector.sharpHistoryCore_length
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e) :
    (A.sharpHistoryCore N).length = A.exploration.length + 1 := by
  have hmem :
      A.sharpHistoryDuplicate N ∈ A.sharpConstructionHistory N :=
    List.count_pos_iff.mp (by
      have htwo := A.sharpHistoryDuplicate_count (N := N)
      omega)
  unfold ManufacturedReflector.sharpHistoryCore
  rw [List.length_erase_of_mem hmem]
  simp [ManufacturedReflector.sharpConstructionHistory]

/-- The activated endpoint is retained by the compressed first history. -/
theorem ManufacturedReflector.activated_mem_sharpHistoryCore
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e) :
    VectorCount.restrict N A.activatedState ∈ A.sharpHistoryCore N := by
  apply A.mem_sharpHistoryCore_of_mem
  simp [ManufacturedReflector.sharpConstructionHistory]

/-- Time zero, hence the reflector's base state, is retained by the compressed
history. -/
theorem ManufacturedReflector.base_mem_sharpHistoryCore
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e) :
    VectorCount.restrict N A.baseState ∈ A.sharpHistoryCore N := by
  apply A.mem_sharpHistoryCore_of_mem
  unfold ManufacturedReflector.sharpConstructionHistory
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
  simp [restrictedTonguesAt, tonguesAt, stepN]

/-- Coefficient-one cover for the two completed constructions in the
endpoint-groove-preserved branch.  The common activation boundary is erased
from the compressed second history and retained by the first core. -/
noncomputable def ManufacturedReflector.preservedTwoHistoryCore
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (N : Nat) : List (List Bool) :=
  A.sharpHistoryCore N ++
    (B.writerConstructionHistory N).erase
      (VectorCount.restrict N A.activatedState)

/-- The coefficient-one two-construction cover has size at most `N+3`.
The additional three are the first reflector's possible facing mouth, the
initial shared vector, and the second reflector's activated endpoint. -/
theorem ManufacturedReflector.preservedTwoHistoryCore_length_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2) :
    (A.preservedTwoHistoryCore B N).length ≤ N + 3 := by
  have hboundary :
      VectorCount.restrict N A.activatedState ∈
        B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    A.reusable_add_second_first_writers_le
      hN B hbaseGrooves hpreGrooves
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

/-- No represented construction vector is lost by coefficient-one
compression or by erasing the common boundary. -/
theorem ManufacturedReflector.mem_preservedTwoHistoryCore
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    {x : List Bool}
    (hx : x ∈ A.sharpConstructionHistory N ∨
      x ∈ B.sharpConstructionHistory N) :
    x ∈ A.preservedTwoHistoryCore B N := by
  rcases hx with hA | hB
  · apply List.mem_append_left
    exact A.mem_sharpHistoryCore_of_mem hA
  · have hBcompressed :=
      B.mem_writerConstructionHistory_of_mem_sharp hB
    by_cases hboundary :
        x = VectorCount.restrict N A.activatedState
    · subst x
      apply List.mem_append_left
      exact A.activated_mem_sharpHistoryCore
    · apply List.mem_append_right
      exact (List.mem_erase_of_ne hboundary).mpr hBcompressed
/-- Two exact manufacturing journeys whose first support is still grooved
at the second pre-return, followed by a directly counted tail, expose only
`N + tailCap + 2` distinct vectors.  The coefficient-one construction
history costs `N+3`, and the tail shares its time-zero boundary. -/
theorem two_manufacturing_journeys_preserved_support_then_tail_distinct_le
    {w : Wiring} {N e tailCap : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (A : ManufacturedReflector w start.1 e)
    (B : ManufacturedReflector w e start.1)
    (stateA stateB : Tongues)
    (hbaseA : A.baseState = start.2)
    (hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hgroovesA :
      PathGrooves A.toSupported.paths stateA)
    (hbaseB : B.baseState = stateA)
    (hactivatedB : stateB = B.activatedState)
    (hreachB : stepN w
      (B.exploration.length + B.runway.length + 1)
        (e, stateA) = some (start.1, stateB))
    (hgroovesB :
      PathGrooves B.toSupported.paths stateB)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (htail : ∀ (tailTimes : List Nat),
      (∀ k ∈ tailTimes,
        (stepN w k (start.1, stateB)).isSome) →
      (tailTimes.map (restrictedTonguesAt w N
        (start.1, stateB))).Nodup →
      tailTimes.length ≤ tailCap)
    (htailPos : 0 < tailCap)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + tailCap + 2 := by
  let firstTravel :=
    A.exploration.length + A.runway.length + 1
  let secondTravel :=
    B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let history := A.preservedTwoHistoryCore B N
  have hgroovesAActivated :
      PathGrooves A.toSupported.paths A.activatedState := by
    rw [← hactivatedA]
    exact hgroovesA
  have hgroovesBActivated :
      PathGrooves B.toSupported.paths B.activatedState := by
    rw [← hactivatedB]
    exact hgroovesB
  have hbaseAB :
      B.baseState = A.activatedState :=
    hbaseB.trans hactivatedA
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbaseB]
    exact hgroovesA
  have hreachTotal :
      stepN w totalTravel start =
        some (start.1, stateB) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hprefixCover : ∀ d, d ≤ totalTravel →
      restrictedTonguesAt w N start d ∈ history := by
    intro d hd
    by_cases hfirst : d ≤ firstTravel
    · dsimp [history]
      apply A.mem_preservedTwoHistoryCore B
      left
      have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hgroovesAActivated (j := d)
          (by simpa [firstTravel] using hfirst)
      simpa [hbaseA] using hm
    · let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q ≤ secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hliveQ := stepN_prefix_some hqLe hreachB
      have hshift :=
        tonguesAt_add_of_reaches hreachA hliveQ
      have hm := B.manufacturing_journey_mem_sharpHistory
        (N := N) hgroovesBActivated (j := q)
          (by simpa [secondTravel] using hqLe)
      have hm' :
          restrictedTonguesAt w N (e, stateA) q ∈
            B.sharpConstructionHistory N := by
        simpa [hbaseB] using hm
      have heq :
          restrictedTonguesAt w N start d =
            restrictedTonguesAt w N (e, stateA) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      dsimp [history]
      exact A.mem_preservedTwoHistoryCore B (Or.inr hm')
  have hboundary :
      VectorCount.restrict N stateB ∈ history := by
    dsimp [history]
    apply A.mem_preservedTwoHistoryCore B
    right
    simp [ManufacturedReflector.sharpConstructionHistory,
      hactivatedB]
  have hcount :=
    boundary_history_then_direct_tail_distinct_le
      hreachTotal history hprefixCover hboundary
        htail htailPos times hlive hnd
  have hhistory :
      history.length ≤ N + 3 := by
    dsimp [history]
    exact A.preservedTwoHistoryCore_length_le_N_add_three
      hN B hbaseAB hbaseGrooves hpreGrooves
  omega

/-- The complete four-vector protected tail therefore gives the sharp
`N+6` count in the pre-return-groove-preserved branch. -/
theorem two_manufacturing_journeys_preserved_support_then_four_tail_le_N_add_six
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (A : ManufacturedReflector w start.1 e)
    (B : ManufacturedReflector w e start.1)
    (stateA stateB : Tongues)
    (hbaseA : A.baseState = start.2)
    (hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hgroovesA :
      PathGrooves A.toSupported.paths stateA)
    (hbaseB : B.baseState = stateA)
    (hactivatedB : stateB = B.activatedState)
    (hreachB : stepN w
      (B.exploration.length + B.runway.length + 1)
        (e, stateA) = some (start.1, stateB))
    (hgroovesB :
      PathGrooves B.toSupported.paths stateB)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (htail : ∀ (tailTimes : List Nat),
      (∀ k ∈ tailTimes,
        (stepN w k (start.1, stateB)).isSome) →
      (tailTimes.map (restrictedTonguesAt w N
        (start.1, stateB))).Nodup →
      tailTimes.length ≤ 4)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 6 := by
  have hcount :=
    two_manufacturing_journeys_preserved_support_then_tail_distinct_le
      hN A B stateA stateB hbaseA hactivatedA hreachA
      hgroovesA hbaseB hactivatedB hreachB hgroovesB
      hpreGrooves htail (by omega) times hlive hnd
  omega

/-- A membership cover for the union of two sharp histories.  It erases one
internal duplicate from each history and then erases the shared activation
boundary from the second compressed history. -/
def ManufacturedReflector.twoSharpHistoryCore
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (N : Nat) : List (List Bool) :=
  A.sharpHistoryCore N ++
    (B.sharpHistoryCore N).erase
      (VectorCount.restrict N A.activatedState)

/-- The second compressed history really contains the shared A-to-B boundary,
so the final erasure removes one element. -/
theorem ManufacturedReflector.twoSharpHistoryCore_length
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState) :
    (A.twoSharpHistoryCore B N).length =
      A.exploration.length + B.exploration.length + 1 := by
  have hboundary :
      VectorCount.restrict N A.activatedState ∈ B.sharpHistoryCore N := by
    simpa [hbase] using B.base_mem_sharpHistoryCore (N := N)
  unfold ManufacturedReflector.twoSharpHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length, B.sharpHistoryCore_length]
  omega

/-- Every vector from either original sharp history remains in the compressed
two-history cover.  At the erased common boundary the first compressed
history supplies the representative. -/
theorem ManufacturedReflector.mem_twoSharpHistoryCore
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    {x : List Bool}
    (hx : x ∈ A.sharpConstructionHistory N ∨
      x ∈ B.sharpConstructionHistory N) :
    x ∈ A.twoSharpHistoryCore B N := by
  rcases hx with hxA | hxB
  · apply List.mem_append_left
    exact A.mem_sharpHistoryCore_of_mem hxA
  · by_cases hboundary :
        x = VectorCount.restrict N A.activatedState
    · subst x
      apply List.mem_append_left
      exact A.activated_mem_sharpHistoryCore
    · apply List.mem_append_right
      exact (List.mem_erase_of_ne hboundary).mpr
        (B.mem_sharpHistoryCore_of_mem hxB)

/-- **NODUP two-history union charge, support-avoiding branch.**

After the two internal repetitions and the shared boundary are erased, every
vector represented by either construction history fits in N+2 slots.
Unlike the earlier N+4 theorem, this statement bounds an arbitrary
duplicate-free union rather than the length of a particular raw list. -/
theorem ManufacturedReflector.two_sharp_histories_nodup_union_le_N_add_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (havoid : A.SupportAvoidsExploration B)
    (pool : List (List Bool))
    (hpool : ∀ x ∈ pool,
      x ∈ A.sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N)
    (hnd : pool.Nodup) :
    pool.length ≤ N + 2 := by
  have hsubset :
      ∀ x ∈ pool, x ∈ A.twoSharpHistoryCore B N := by
    intro x hx
    exact A.mem_twoSharpHistoryCore B (hpool x hx)
  have hcover :=
    nodup_subset_length_two_history hnd hsubset
  have hpaths :=
    A.two_explorations_length_le_N_add_one hN B havoid
  have hcore := A.twoSharpHistoryCore_length (N := N) B hbase
  omega

/-- A concrete old-support contact, retaining the exact physical prefix and
suffix of the second exploration. -/
structure SecondHistoryContactData
    (w : Wiring) (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g) where
  approach : List Passage
  fresh : Passage
  suffix : List Passage
  contactState : Tongues
  split : B.exploration = approach ++ fresh :: suffix
  approach_trace :
    PhysicalTrace w (e, B.baseState) approach (fresh.1, contactState)
  suffix_trace :
    PhysicalTrace w (fresh.1, contactState) (fresh :: suffix) B.preReturn
  old_grooves : PathGrooves A.toSupported.paths contactState
  touches : A.TouchesSupport fresh

/-- A first old-support contact is contact data whose strict approach has no
earlier old-support passage.  The dynamic contact theorems below only need
the parent data; freshness is retained here for the original coordinate
charge and for callers that genuinely stop at the first contact. -/
structure SecondHistorySupportContact
    (w : Wiring) (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    extends SecondHistoryContactData w A B where
  approach_fresh : ∀ prior ∈ approach, ¬ A.TouchesSupport prior

instance {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g} :
    Coe (SecondHistorySupportContact w A B)
      (SecondHistoryContactData w A B) :=
  ⟨SecondHistorySupportContact.toSecondHistoryContactData⟩

/-! ## Charge a prefix ending at the first damaging support passage -/

/-- Every contact approach is a prefix of the second switch-simple
exploration. -/
theorem SecondHistoryContactData.approach_simple
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B) :
    SwitchSimple C.approach := by
  have hs := B.exploration_simple
  unfold SwitchSimple at hs ⊢
  rw [C.split] at hs
  simp only [List.map_append, List.map_cons] at hs
  exact (List.nodup_append.mp hs).1

/-- If both endpoints of a switch-simple contact approach groove the old
support, every productive prefix writer is outside that support.  The write
survives by simplicity, so an old-support writer would contradict endpoint
agreement on the corresponding old passage. -/
theorem SecondHistoryContactData.approach_productive_writer_not_reusable
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    {k : Nat} (hk : k < C.approach.length)
    (hprod : RawProductiveAt w N (e, B.baseState) k) :
    rawWriterAt w (e, B.baseState) k ∉ A.reusableSwitches := by
  intro hreusable
  have hsurvives :
      C.contactState (rawWriterAt w (e, B.baseState) k) ≠
        B.baseState (rawWriterAt w (e, B.baseState) k) :=
    C.approach_trace.simple_raw_productive_writer_survives
      hN C.approach_simple hk hprod
  obtain ⟨path, hpath, old, hold, hswitch⟩ :=
    A.mem_reusableSwitches hreusable
  have hbaseOld := hbaseGrooves path hpath old hold
  have hcontactOld := C.old_grooves path hpath old hold
  have hagree :=
    grooved_states_agree_on_passage hbaseOld hcontactOld
  have hexit : old.2 / 3 = passageSwitch old := by
    have hs := arrive_exit_switch B.baseState old.2
    rw [hbaseOld] at hs
    exact hs.symm
  apply hsurvives
  calc
    C.contactState (rawWriterAt w (e, B.baseState) k) =
        C.contactState (old.2 / 3) := by rw [hexit, hswitch]
    _ = B.baseState (old.2 / 3) := hagree.symm
    _ = B.baseState (rawWriterAt w (e, B.baseState) k) := by
      rw [hexit, hswitch]

/-- The old reusable support and all productive first writers before the
damaging contact occupy disjoint switch coordinates, hence cost at most N
altogether. -/
theorem SecondHistoryContactData.reusable_add_approach_first_writers_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState) :
    A.reusableSwitches.length +
      (rawFirstWriterTimes w N (e, B.baseState)
        C.approach.length).length ≤ N := by
  classical
  let times :=
    rawFirstWriterTimes w N (e, B.baseState) C.approach.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact nodup_filter_nat_two_history _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply nodup_map_nat_of_injective_on_two_history
    · intro i hi j hj hEq
      have hiData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hi)
      have hjData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hj)
      exact rawFirstWriterAt_injective
        hiData.2 hjData.2 hEq
    · exact htimesNodup
  have hdisjoint :
      ∀ oldSwitch ∈ A.reusableSwitches,
        ∀ freshSwitch ∈ writers, oldSwitch ≠ freshSwitch := by
    intro oldSwitch hOld freshSwitch hFresh hEq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
    have hkData := mem_rawFirstWriterTimes_iff.mp (by
      simpa [times] using hk)
    have houtside :=
      C.approach_productive_writer_not_reusable
        hN hbaseGrooves hkData.1 hkData.2.1
    apply houtside
    rw [← hEq]
    exact hOld
  let switches := A.reusableSwitches ++ writers
  have hnd : switches.Nodup := by
    dsimp [switches]
    exact List.nodup_append.mpr
      ⟨A.reusableSwitches_nodup, hwritersNodup, hdisjoint⟩
  have hlt : ∀ C₀ ∈ switches, C₀ < N := by
    intro C₀ hC
    rcases List.mem_append.mp hC with hOld | hFresh
    · exact A.reusableSwitch_lt hN hOld
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hFresh
      have hkData := mem_rawFirstWriterTimes_iff.mp (by
        simpa [times] using hk)
      exact rawProductiveAt_writer_lt hN hkData.2.1
  have hbound := nodup_nat_lt_length hnd hlt
  have hlength :
      A.reusableSwitches.length + times.length ≤ N := by
    simpa [switches, writers] using hbound
  simpa [times] using hlength

/-- The compressed second prefix consists of its canonical first-writer
history and the post-contact vector. -/
noncomputable def SecondHistoryContactData.damageWriterHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (N : Nat) (next : Tongues) : List (List Bool) :=
  rawFirstWriterHistory w N (e, B.baseState) C.approach.length ++
    [VectorCount.restrict N next]

/-- Coefficient-one history through a damaging support contact. -/
noncomputable def SecondHistoryContactData.damageContactHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (N : Nat) (next : Tongues) : List (List Bool) :=
  A.sharpHistoryCore N ++
    (C.damageWriterHistory N next).erase
      (VectorCount.restrict N A.activatedState)

/-- Every literal second-prefix vector through the contact occurs in the
compressed writer history. -/
theorem SecondHistoryContactData.prefix_mem_damageWriterHistory
    {w : Wiring} {N g e j : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    {next : Tongues}
    (harrive : arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hj : j ≤ C.approach.length + 1) :
    restrictedTonguesAt w N (e, B.baseState) j ∈
      C.damageWriterHistory N next := by
  unfold SecondHistoryContactData.damageWriterHistory
  by_cases hprefix : j ≤ C.approach.length
  · apply List.mem_append_left
    exact C.approach_trace.restrictedTonguesAt_mem_rawFirstWriterHistory
      C.approach_simple j hprefix
  · have hjEq : j = C.approach.length + 1 := by omega
    obtain ⟨q, post, hhead, hone⟩ :=
      physicalTrace_head_step_two_history C.suffix_trace
    have hpost : post = next := by
      rw [harrive] at hhead
      exact (Prod.mk.inj hhead).2.symm
    have hglobal :
        stepN w j (e, B.baseState) = some (q, next) := by
      rw [hjEq, stepN_add, C.approach_trace.sound]
      simpa [hpost] using hone
    apply List.mem_append_right
    simp [restrictedTonguesAt, tonguesAt, hglobal]

/-- The damaging-contact history has coefficient one and length at most
N+3. -/
theorem SecondHistoryContactData.damageContactHistory_length_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves : PathGrooves A.toSupported.paths B.baseState)
    (next : Tongues) :
    (C.damageContactHistory N next).length ≤ N + 3 := by
  have hboundary :
      VectorCount.restrict N A.activatedState ∈
        C.damageWriterHistory N next := by
    unfold SecondHistoryContactData.damageWriterHistory
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge :=
    C.reusable_add_approach_first_writers_le hN hbaseGrooves
  have houter := A.exploration_length_le_reusable_add_one
  unfold SecondHistoryContactData.damageContactHistory
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length]
  simp [SecondHistoryContactData.damageWriterHistory,
    rawFirstWriterHistory]
  omega

/-! ## Stop the second charge at its first old-support contact -/

/-- The old reusable coordinates and the second journey's strictly
pre-contact coordinates are disjoint and individually simple. -/
theorem SecondHistorySupportContact.reusable_append_approach_nodup
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B) :
    (A.reusableSwitches ++ C.approach.map passageSwitch).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨A.reusableSwitches_nodup, ?_, ?_⟩
  · have hsimple := B.exploration_simple
    unfold SwitchSimple at hsimple
    rw [C.split] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  · intro oldSwitch holdSwitch freshSwitch hfreshSwitch hEq
    obtain ⟨path, hpath, old, hold, holdEq⟩ :=
      A.mem_reusableSwitches holdSwitch
    obtain ⟨prior, hprior, hpriorEq⟩ :=
      List.mem_map.mp hfreshSwitch
    apply C.approach_fresh prior hprior
    refine ⟨path, hpath, old, hold, ?_⟩
    exact holdEq.trans (hEq.trans hpriorEq.symm)

/-- The old support and the fresh approach together consume at most N
switch coordinates. -/
theorem SecondHistorySupportContact.reusable_add_approach_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B) :
    A.reusableSwitches.length + C.approach.length ≤ N := by
  let switches :=
    A.reusableSwitches ++ C.approach.map passageSwitch
  have hnd : switches.Nodup := by
    simpa [switches] using C.reusable_append_approach_nodup
  have hlt : ∀ k ∈ switches, k < N := by
    intro k hk
    rcases List.mem_append.mp hk with hA | hB
    · exact A.reusableSwitch_lt hN hA
    · obtain ⟨passage, hpassage, rfl⟩ := List.mem_map.mp hB
      apply B.exploration_trace.switch_lt hN passage
      rw [C.split]
      exact List.mem_append_left _ hpassage
  have hbound := nodup_nat_lt_length hnd hlt
  simpa [switches] using hbound

/-- The full first exploration and the strictly pre-contact part of the
second exploration cost at most N+1 passages. -/
theorem SecondHistorySupportContact.first_exploration_add_approach_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B) :
    A.exploration.length + C.approach.length ≤ N + 1 := by
  have hsupport := C.reusable_add_approach_le hN
  have hA := A.exploration_length_le_reusable_add_one
  omega

/-- Restricted tongue vectors of the second journey from its shared initial
boundary through the post-vector of the first old-support contact. -/
def SecondHistoryContactData.prefixHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (N : Nat) : List (List Bool) :=
  (List.range (C.approach.length + 2)).map
    (restrictedTonguesAt w N (e, B.baseState))

/-- Every second-journey vector through the contact belongs to the literal
prefix history. -/
theorem SecondHistoryContactData.mem_prefixHistory
    {w : Wiring} {N g e j : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (hj : j ≤ C.approach.length + 1) :
    restrictedTonguesAt w N (e, B.baseState) j ∈
      C.prefixHistory N := by
  unfold SecondHistoryContactData.prefixHistory
  apply List.mem_map.mpr
  exact ⟨j, List.mem_range.mpr (by omega), rfl⟩

/-- The second prefix begins at the activated endpoint of the first
construction, so this shared boundary may be erased once. -/
theorem SecondHistoryContactData.boundary_mem_prefixHistory
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (hbase : B.baseState = A.activatedState) :
    VectorCount.restrict N A.activatedState ∈ C.prefixHistory N := by
  have hzero := C.mem_prefixHistory (N := N) (j := 0) (by omega)
  simpa [restrictedTonguesAt, tonguesAt, stepN, hbase] using hzero

/-- A coefficient-one cover: the compressed first sharp history, followed
only by the second prefix through first contact, with the shared boundary
removed from the latter. -/
def SecondHistoryContactData.contactHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (N : Nat) : List (List Bool) :=
  A.sharpHistoryCore N ++
    (C.prefixHistory N).erase
      (VectorCount.restrict N A.activatedState)

/-- Exact length of the first-contact cover. -/
theorem SecondHistoryContactData.contactHistory_length
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (hbase : B.baseState = A.activatedState) :
    (C.contactHistory N).length =
      A.exploration.length + C.approach.length + 2 := by
  have hboundary := C.boundary_mem_prefixHistory (N := N) hbase
  unfold SecondHistoryContactData.contactHistory
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length]
  simp [SecondHistoryContactData.prefixHistory]
  omega

/-- Compatibility view of the generalized prefix history for a literal
first-support contact. -/
abbrev SecondHistorySupportContact.prefixHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (N : Nat) : List (List Bool) :=
  C.toSecondHistoryContactData.prefixHistory N

/-- Compatibility view of the generalized contact history. -/
abbrev SecondHistorySupportContact.contactHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (N : Nat) : List (List Bool) :=
  C.toSecondHistoryContactData.contactHistory N

theorem SecondHistorySupportContact.contactHistory_length
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState) :
    (C.contactHistory N).length =
      A.exploration.length + C.approach.length + 2 :=
  C.toSecondHistoryContactData.contactHistory_length hbase

/-- The first-contact cover has coefficient one: at most N+3 vectors. -/
theorem SecondHistorySupportContact.contactHistory_length_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState) :
    (C.contactHistory N).length ≤ N + 3 := by
  have hlength := C.contactHistory_length (N := N) hbase
  have hcharge := C.first_exploration_add_approach_le hN
  omega

/-- Erasing the internal and shared-boundary repetitions loses no vector:
the cover contains every first sharp-history vector and every second vector
through the first contact. -/
theorem SecondHistoryContactData.mem_contactHistory
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    {x : List Bool}
    (hx : x ∈ A.sharpConstructionHistory N ∨
      x ∈ C.prefixHistory N) :
    x ∈ C.contactHistory N := by
  rcases hx with hxA | hxB
  · apply List.mem_append_left
    exact A.mem_sharpHistoryCore_of_mem hxA
  · by_cases hboundary :
        x = VectorCount.restrict N A.activatedState
    · subst x
      apply List.mem_append_left
      exact A.activated_mem_sharpHistoryCore
    · apply List.mem_append_right
      exact (List.mem_erase_of_ne hboundary).mpr hxB

/-- The vector immediately before the first old-support contact is already
present in the coefficient-one contact history. -/
theorem SecondHistoryContactData.contact_pre_mem
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B) :
    VectorCount.restrict N C.contactState ∈ C.contactHistory N := by
  apply C.mem_contactHistory
  right
  have hm := C.mem_prefixHistory
    (N := N) (j := C.approach.length) (by omega)
  simpa [restrictedTonguesAt, tonguesAt,
    C.approach_trace.sound] using hm

/-- The contact history also contains the post-vector installed by the
contact passage.  This is the second historical corner needed by the
forward-splice Gray square. -/
theorem SecondHistoryContactData.contact_post_mem
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B) :
    ∃ next,
      arrive C.contactState C.fresh.1 = (C.fresh.2, next) ∧
      VectorCount.restrict N next ∈ C.contactHistory N := by
  obtain ⟨q, next, harrive, hone⟩ :=
    physicalTrace_head_step_two_history C.suffix_trace
  refine ⟨next, harrive, ?_⟩
  apply C.mem_contactHistory
  right
  have hm := C.mem_prefixHistory
    (N := N) (j := C.approach.length + 1) (by omega)
  have hglobal :
      stepN w (C.approach.length + 1) (e, B.baseState) =
        some (q, next) := by
    rw [stepN_add, C.approach_trace.sound]
    exact hone
  simpa [restrictedTonguesAt, tonguesAt, hglobal] using hm

/-- The literal contact history used by the dynamic classification embeds
in the compressed coefficient-one history. -/
theorem SecondHistoryContactData.mem_damageContactHistory_of_mem_contactHistory
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    {next : Tongues}
    (harrive : arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    {x : List Bool} (hx : x ∈ C.contactHistory N) :
    x ∈ C.damageContactHistory N next := by
  unfold SecondHistoryContactData.contactHistory at hx
  unfold SecondHistoryContactData.damageContactHistory
  rcases List.mem_append.mp hx with hxA | hxPrefix
  · exact List.mem_append_left _ hxA
  · have hxPrefix' : x ∈ C.prefixHistory N :=
      List.mem_of_mem_erase hxPrefix
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hxPrefix'
    have hjLe : j ≤ C.approach.length + 1 := by
      have hjLt := List.mem_range.mp hj
      omega
    have hwriter := C.prefix_mem_damageWriterHistory
      (N := N) harrive hjLe
    by_cases hboundary :
        restrictedTonguesAt w N (e, B.baseState) j =
          VectorCount.restrict N A.activatedState
    · rw [hboundary]
      apply List.mem_append_left
      exact A.activated_mem_sharpHistoryCore
    · apply List.mem_append_right
      exact (List.mem_erase_of_ne hboundary).mpr hwriter

/- **Coefficient-one first-contact union charge.**

Any duplicate-free selection drawn from the first complete sharp history and
the second journey only through its first old-support contact has size at
most N+3.  No overlap between the two lists is assumed. -/

theorem first_forward_contact_active_lead_two_history
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    {approach : List Passage} {p x : Nat}
    {suffix : List Passage} {u v : Tongues}
    {oriented : Passage} {repaired : Tongues}
    (hsplit : B.exploration = approach ++ (p, x) :: suffix)
    (happroach :
      PhysicalTrace w (e, B.baseState) approach (p, u))
    (hpaths : PathGrooves A.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3))
    (horiented : oriented ∈ A.orientedRoute u)
    (horientedGroove :
      arrive u oriented.2 = (oriented.1, u))
    (horientedSwitch : passageSwitch oriented = p / 3)
    (hforward : x = oriented.2)
    (hrepair : arrive v oriented.1 = (oriented.2, repaired))
    (hrestored :
      arrive repaired oriented.2 = (oriented.1, repaired)) :
    ∃ (entry mouth returnPort outside : Nat)
        (oldPrefix oldTail candy : List Passage) (tailSteps : Nat),
      (entry, mouth) ∈ A.orientedRoute u ∧
      A.orientedRoute u =
        oldPrefix ++ (entry, mouth) :: oldTail ∧
      PhysicalTrace w (outside, u) oldTail
        (A.orientedFinish u, u) ∧
      PhysicalTrace w (e, u) approach (returnPort, u) ∧
      SwitchSimple approach ∧
      PassagesGrooved u approach ∧
      (∀ passage ∈ approach,
        passageSwitch passage ≠ mouth / 3) ∧
      candy = reversePassages oldPrefix ++ approach ∧
      entry % 3 ≠ 0 ∧ mouth % 3 = 0 ∧
      w.link mouth = some outside ∧
      entry ≠ returnPort ∧
      PassagesGrooved u ((mouth, entry) :: candy) ∧
      PhysicalTrace w (mouth, u) ((mouth, entry) :: candy)
        (returnPort, u) ∧
      arrive u returnPort =
        (mouth, flipAt u (mouth / 3)) ∧
      PathGrooves A.toSupported.paths u ∧
      PassagesGrooved u candy ∧
      (∀ passage ∈ candy,
        passageSwitch passage ≠ mouth / 3) ∧
      IsReflector w mouth outside (candy.length + 2)
        (fun state => PassagesGrooved state candy)
        (fun state => flipAt state (mouth / 3)) ∧
      stepN w (approach.length + 1) (e, B.baseState) =
        some (outside, flipAt u (mouth / 3)) ∧
      stepN w tailSteps (outside, u) =
        some (e, A.toSupported.action.apply u) := by
  rcases oriented with ⟨a, s⟩
  simp only at horiented horientedGroove hforward hrepair hrestored
  subst x
  obtain ⟨hpBranch, hsEq, _hv, _hback⟩ :=
    changed_arrival_is_trailing harrive hchanged
  have hsStem : s % 3 = 0 := by
    rw [hsEq]
    omega
  have hsp : s / 3 = p / 3 := by
    rw [hsEq]
    omega
  have hsa : s / 3 = a / 3 := by
    have hswitch := arrive_exit_switch u s
    rw [horientedGroove] at hswitch
    exact hswitch.symm
  have haBranch : a % 3 ≠ 0 := by
    have haEq : branchPort (s / 3) (u (s / 3)) = a := by
      unfold arrive at horientedGroove
      rw [if_pos hsStem] at horientedGroove
      exact congrArg Prod.fst horientedGroove
    intro haStem
    cases hu : u (s / 3) <;>
      simp [branchPort, hu] at haEq <;> omega
  have hap : a ≠ p := by
    intro hEq
    subst p
    have holdForward := groove_forward horientedGroove
    rw [harrive] at holdForward
    have huv : v = u := congrArg Prod.snd holdForward
    apply hchanged
    rw [huv]
  obtain ⟨oldPrefix, oldTail, hrouteSplit⟩ :=
    List.append_of_mem horiented
  have hroute := A.orientedRoute_trace u hpaths
  have hrouteSimple := A.orientedRoute_simple u
  have hrouteGrooved :=
    hroute.grooved_of_switchSimple hrouteSimple
  have hOldPrefixData :=
    simple_grooved_trace_prefix_to_occurrence
      hroute hrouteSplit hrouteGrooved hrouteSimple
  have hOldPrefixGrooved : PassagesGrooved u oldPrefix := by
    intro passage hp
    exact hrouteGrooved passage (by
      rw [hrouteSplit]
      exact List.mem_append_left _ hp)
  have hApproachSimple : SwitchSimple approach := by
    have hsimple := B.exploration_simple
    unfold SwitchSimple at hsimple ⊢
    rw [hsplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hApproachGrooved : PassagesGrooved u approach :=
    happroach.grooved_of_switchSimple hApproachSimple
  have hApproachForeign :
      ∀ passage ∈ approach, passageSwitch passage ≠ p / 3 := by
    have hsimple := B.exploration_simple
    unfold SwitchSimple at hsimple
    rw [hsplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have hparts := List.nodup_append.mp hsimple
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch (p, s)) (by simp)
    exact hne (by simpa [passageSwitch] using hEq)
  let candy := reversePassages oldPrefix ++ approach
  have hCandyGrooved : PassagesGrooved u candy := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · exact reversePassages_grooved
        hOldPrefixGrooved passage hold
    · exact hApproachGrooved passage hnew
  have hCandyForeign :
      ∀ passage ∈ candy, passageSwitch passage ≠ s / 3 := by
    intro passage hp
    rcases List.mem_append.mp hp with hold | hnew
    · have hmapped : passageSwitch passage ∈
          (reversePassages oldPrefix).map passageSwitch :=
        List.mem_map.mpr ⟨passage, hold, rfl⟩
      have hmap :=
        map_passageSwitch_reversePassages hOldPrefixData.1
      rw [hmap] at hmapped
      have horiginal : passageSwitch passage ∈
          oldPrefix.map passageSwitch :=
        List.mem_reverse.mp hmapped
      obtain ⟨old, holdMem, holdEq⟩ :=
        List.mem_map.mp horiginal
      intro hmouth
      apply hOldPrefixData.2 old holdMem
      exact holdEq.trans (hmouth.trans hsa)
    · intro hmouth
      apply hApproachForeign passage hnew
      exact hmouth.trans hsp
  have hback := physicalTrace_contact_retraces_prefix
    hOldPrefixData.1 hOldPrefixGrooved A.entryEdge
      horientedGroove
  have hforwardTrace :=
    happroach.replay_grooved u hApproachGrooved
  have hsplice :
      PhysicalTrace w (s, u) ((s, a) :: candy) (p, u) := by
    simpa [candy, List.append_assoc] using
      hback.append hforwardTrace
  have hSpliceGrooved :
      PassagesGrooved u ((s, a) :: candy) := by
    intro passage hpassage
    rcases List.mem_cons.mp hpassage with hhead | htail
    · simpa [hhead] using groove_forward horientedGroove
    · exact hCandyGrooved passage htail
  have hroute' := hroute
  rw [hrouteSplit] at hroute'
  obtain ⟨middle, hOldBefore, hOldAfter⟩ :=
    hroute'.split_append
  have hMiddle : middle = (a, u) := by
    have h₁ := hOldBefore.sound
    have h₂ := hOldPrefixData.1.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hOldAfter with
  | @cons _ _ outside _ oldAfter _ _ hOldArrive hmouth hOldRest =>
      have hOldAfterState : oldAfter = u := by
        have hforwardOld := groove_forward horientedGroove
        rw [hOldArrive] at hforwardOld
        exact congrArg Prod.snd hforwardOld
      subst oldAfter
      have hcontactTrace :
          PhysicalTrace w (a, u) [(a, s)] (outside, u) :=
        PhysicalTrace.cons (groove_forward horientedGroove)
          hmouth (PhysicalTrace.nil _)
      have hlead := hOldPrefixData.1.append hcontactTrace
      have hleadSplit : A.orientedRoute u =
          (oldPrefix ++ [(a, s)]) ++ oldTail := by
        rw [hrouteSplit]
        simp [List.append_assoc]
      obtain ⟨tailSteps, _hlen, hcomplete⟩ :=
        A.complete_after_oriented_prefix
          u hpaths hleadSplit hlead
      have hflip : v = flipAt u (s / 3) := by
        have hv := changed_arrival_eq_flipAt harrive hchanged
        simpa [hsp] using hv
      have hone :
          stepN w 1 (p, u) = some (outside, v) := by
        simp [stepN, step, harrive, hmouth]
      have hreach :
          stepN w (approach.length + 1) (e, B.baseState) =
            some (outside, flipAt u (s / 3)) := by
        rw [stepN_add, happroach.sound]
        simp only [Option.bind_some]
        rw [hone, hflip]
      have hcrossed :
          arrive u p = (s, flipAt u (s / 3)) := by
        rw [harrive, hflip]
      refine ⟨a, s, p, outside, oldPrefix, oldTail,
        candy, tailSteps, horiented, hrouteSplit, hOldRest,
        hforwardTrace, hApproachSimple, hApproachGrooved,
        (by
          intro passage hpassage
          simpa [hsp] using
            hApproachForeign passage hpassage),
        rfl, haBranch, hsStem, hmouth, hap, hSpliceGrooved,
        hsplice, hcrossed, hpaths, hCandyGrooved,
        hCandyForeign, ?_, hreach, hcomplete⟩
      exact stem_lobe_isReflector_foreign w candy
        hsStem haBranch hpBranch hsa hsp hap hCandyForeign
        hsplice.linked hsplice.last_link hmouth

/- The first-contact prefix union itself needs no overlap assumption. -/
/-- A first changing forward contact into a flip reflector contributes only
the two action-image corners beyond the coefficient-one contact history.
Both the contact state and the state immediately after the contact are
already present in that history. -/
theorem SecondHistoryContactData.changed_forward_flip_two_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedFlipReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w (.flip R) B)
    {next : Tongues}
    (harrive :
      arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged :
      next (C.fresh.1 / 3) ≠
        C.contactState (C.fresh.1 / 3))
    {oriented : Passage} {repaired : Tongues}
    (horiented :
      oriented ∈
        (ManufacturedReflector.flip R).orientedRoute C.contactState)
    (horientedGroove :
      arrive C.contactState oriented.2 =
        (oriented.1, C.contactState))
    (horientedSwitch :
      passageSwitch oriented = C.fresh.1 / 3)
    (hforward : C.fresh.2 = oriented.2)
    (hrepair :
      arrive next oriented.1 = (oriented.2, repaired))
    (hrestored :
      arrive repaired oriented.2 = (oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
      times (C.contactHistory N) 2 := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, _hCandy, hCandyForeignNew, hLobe, hreach,
      _hcomplete⟩ :=
    first_forward_contact_active_lead_two_history
      (A := ManufacturedReflector.flip R) C.split C.approach_trace
      C.old_grooves harrive hchanged horiented horientedGroove
      horientedSwitch hforward hrepair hrestored
  let K := C.approach.length + 1
  let state := C.contactState
  let alternate := flipAt state (mouth / 3)
  have hreach' :
      stepN w K (e, B.baseState) =
        some (outside, alternate) := by
    simpa [K, state, alternate] using hreach
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.contactHistory N := by
    apply C.mem_contactHistory
    right
    have hm := C.mem_prefixHistory
      (N := N) (j := K) (by simp [K])
    simpa [restrictedTonguesAt, tonguesAt, hreach'] using hm
  have hstateHistorical :
      VectorCount.restrict N state ∈ C.contactHistory N := by
    simpa [state] using C.contact_pre_mem (N := N)
  have hleadHistorical : ∀ j ∈ times, j < K →
      restrictedTonguesAt w N (e, B.baseState) j ∈
        C.contactHistory N := by
    intro j _hj hjK
    apply C.mem_contactHistory
    right
    exact C.mem_prefixHistory (N := N) (j := j) (by
      dsimp [K] at hjK
      omega)
  by_cases hrunway : (entry, mouth) ∈ R.runway
  · obtain ⟨before, after, hrunwaySplit⟩ :=
      List.append_of_mem hrunway
    obtain ⟨D, _hDAction, hEntryOldNe, hDpaths,
        hNewAvoidsDRaw, _htravel⟩ :=
      R.suffix_after_runway_passage_with_travel state hRpaths
        hrunwaySplit hmouthLink
    have hentrySwitch : entry / 3 = mouth / 3 := by
      have hheadGroove :
          arrive state entry = (mouth, state) :=
        hfullGrooved (mouth, entry) List.mem_cons_self
      have hswitch := arrive_exit_switch state entry
      rw [hheadGroove] at hswitch
      exact hswitch.symm
    have hActionsNe : mouth / 3 ≠ D.actionSwitch := by
      rw [← hentrySwitch]
      exact hEntryOldNe
    have hNewAvoidsD :
        (LocalAction.flip (mouth / 3)).Avoids
          D.toSupported.paths := by
      simpa [hentrySwitch] using hNewAvoidsDRaw
    by_cases hcontact : ∃ passage ∈ candy,
        passageSwitch passage = D.actionSwitch
    · apply manufactured_flip_arbitrary_lobe_absolute_two_novelty
        D state hDpaths hNewAvoidsD hentryBranch hentrySwitch
        hfullGrooved hfullTrace hcrossed hCandyForeignNew hLobe
        hmouthLink hcontact hreach' times (C.contactHistory N)
        hentryHistorical hstateHistorical
      exact hleadHistorical
    · have hCandyForeignOld : ∀ passage ∈ candy,
          passageSwitch passage ≠ D.actionSwitch := by
        intro passage hp hEq
        exact hcontact ⟨passage, hp, hEq⟩
      apply manufactured_suffix_explicit_lobe_absolute_two_novelty
        D state hDpaths hNewAvoidsD hActionsNe hentryBranch
        hentrySwitch hfullGrooved hfullTrace hcrossed
        hCandyForeignNew hCandyForeignOld hLobe hmouthLink
        hreach' times (C.contactHistory N) hentryHistorical
        hstateHistorical
      exact hleadHistorical
  · obtain ⟨old, hold, horientation⟩ :=
      R.nonrunway_oriented_branch_entry_is_candy state
        hentryOld hrunway hentryBranch
    have hentryGrooved :
        arrive state entry = (mouth, state) :=
      hfullGrooved (mouth, entry) List.mem_cons_self
    have hone := manufactured_flip_candy_splice_absolute_one_novelty
      R state hRpaths hrouteSplit hOldTail hrunway hentryBranch
      hold horientation hentryGrooved hApproachReplay
      hApproachGrooved hApproachForeign hcrossed hmouthLink harms
      hreach' N (C.contactHistory N) hentryHistorical times
      hleadHistorical
    obtain ⟨fresh, hfresh, hmem⟩ := hone
    exact ⟨fresh, by omega, hmem⟩
private theorem twoHistory_twoPhase_concat
    {w : Wiring} {start middle : Nat × Tongues}
    {left right : Nat} {u v : Tongues}
    (hleft : stepN w left start = some middle)
    (hleftPhase : ∀ d, d ≤ left → ∃ port phase,
      stepN w d start = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (hrightPhase : ∀ d, d ≤ right → ∃ port phase,
      stepN w d middle = some (port, phase) ∧
        (phase = u ∨ phase = v))
    (d : Nat) (hd : d ≤ left + right) :
    ∃ port phase, stepN w d start = some (port, phase) ∧
      (phase = u ∨ phase = v) := by
  by_cases hdl : d ≤ left
  · exact hleftPhase d hdl
  · let r := d - left
    have hr : r ≤ right := by
      dsimp [r]
      omega
    have hdecomp : d = left + r := by
      dsimp [r]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hrightPhase r hr
    refine ⟨port, phase, ?_, hphase⟩
    rw [hdecomp, stepN_add, hleft]
    simpa using hrun

/-- Exact all-time two-phase tail for a first changing forward contact into a
stay reflector.  The entry time is the literal post-contact time of
prefixHistory, not an existentially reconstructed lead. -/
theorem SecondHistoryContactData.changed_forward_stay_two_phase_tail
    {w : Wiring} {g e : Nat}
    {R : ManufacturedStayReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w (.stay R) B)
    {next : Tongues}
    (harrive :
      arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged :
      next (C.fresh.1 / 3) ≠
        C.contactState (C.fresh.1 / 3))
    {oriented : Passage} {repaired : Tongues}
    (horiented :
      oriented ∈
        (ManufacturedReflector.stay R).orientedRoute C.contactState)
    (horientedGroove :
      arrive C.contactState oriented.2 =
        (oriented.1, C.contactState))
    (horientedSwitch :
      passageSwitch oriented = C.fresh.1 / 3)
    (hforward : C.fresh.2 = oriented.2)
    (hrepair :
      arrive next oriented.1 = (oriented.2, repaired))
    (hrestored :
      arrive repaired oriented.2 = (oriented.1, repaired)) :
    ∃ outside mouth,
      stepN w (C.approach.length + 1) (e, B.baseState) =
        some (outside, flipAt C.contactState (mouth / 3)) ∧
      ∀ d, ∃ port phase,
        stepN w d
          (outside, flipAt C.contactState (mouth / 3)) =
            some (port, phase) ∧
        (phase = flipAt C.contactState (mouth / 3) ∨
          phase = C.contactState) := by
  obtain ⟨entry, mouth, returnPort, outside, oldPrefix, oldTail,
      candy, tailSteps, hentryOld, hrouteSplit, hOldTail,
      hApproachReplay, hApproachSimple, hApproachGrooved,
      hApproachForeign, _hCandyEq, hentryBranch, _hmouthStem,
      hmouthLink, harms, hfullGrooved, hfullTrace, hcrossed,
      hRpaths, hCandy, hCandyForeign, hLobe, hreach,
      _hcomplete⟩ :=
    first_forward_contact_active_lead_two_history
      (A := ManufacturedReflector.stay R) C.split C.approach_trace
      C.old_grooves harrive hchanged horiented horientedGroove
      horientedSwitch hforward hrepair hrestored
  let k := mouth / 3
  let alternate := flipAt C.contactState k
  have hCandyFlip : PassagesGrooved alternate candy := by
    dsimp [alternate, k]
    exact grooved_after_flip_other hCandy hCandyForeign
  have hOldRoute :=
    (ManufacturedReflector.stay R).orientedRoute_trace
      C.contactState hRpaths
  have hOldSimple :=
    (ManufacturedReflector.stay R).orientedRoute_simple C.contactState
  have hOldGrooved :=
    hOldRoute.grooved_of_switchSimple hOldSimple
  have hOldForward :
      arrive C.contactState entry = (mouth, C.contactState) :=
    groove_forward (hOldGrooved (entry, mouth) hentryOld)
  have hentryMouthSwitch : entry / 3 = mouth / 3 := by
    have hswitch := arrive_exit_switch C.contactState entry
    rw [hOldForward] at hswitch
    exact hswitch.symm
  have hallAfter : ∀ d, ∃ port phase,
      stepN w d (outside, alternate) = some (port, phase) ∧
        (phase = alternate ∨ phase = C.contactState) := by
    change (entry, mouth) ∈ R.runway ++ [(R.mouth, R.arm)] at hentryOld
    rcases List.mem_append.mp hentryOld with hrunway | hcore
    · obtain ⟨before, after, hsplit⟩ := List.append_of_mem hrunway
      obtain ⟨D, hDpaths, hAvoid⟩ :=
        R.suffix_after_runway_passage C.contactState hRpaths
          hsplit hmouthLink
      have hAvoid' :
          (LocalAction.flip k).Avoids D.toSupported.paths := by
        dsimp [k]
        simpa [hentryMouthSwitch] using hAvoid
      have hDalt : PathGrooves D.toSupported.paths alternate := by
        dsimp [alternate]
        exact hDpaths.after_avoiding_action hAvoid'
      let dTravel := D.toSupported.travel
      let lTravel := candy.length + 2
      have hDaltEnd :
          stepN w dTravel (outside, alternate) =
            some (mouth, alternate) := by
        dsimp [dTravel]
        exact (D.toSupported.run alternate hDalt).1
      have hDstateEnd :
          stepN w dTravel (outside, C.contactState) =
            some (mouth, C.contactState) := by
        dsimp [dTravel]
        exact (D.toSupported.run C.contactState hDpaths).1
      have hDaltPhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          D.travel_state_stepN alternate hDalt (by
            simpa [dTravel, ManufacturedReflector.toSupported,
              ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, alternate, hrun, Or.inl rfl⟩
      have hDstatePhase : ∀ d, d ≤ dTravel → ∃ port phase,
          stepN w d (outside, C.contactState) =
            some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, hrun⟩ :=
          D.travel_state_stepN C.contactState hDpaths (by
            simpa [dTravel, ManufacturedReflector.toSupported,
              ManufacturedStayReflector.toSupported] using hd)
        exact ⟨port, C.contactState, hrun, Or.inr rfl⟩
      have hReverseEnd :
          stepN w lTravel (mouth, alternate) =
            some (outside, C.contactState) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (mouth, alternate) =
          some (outside, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd :
          stepN w lTravel (mouth, C.contactState) =
            some (outside, alternate) := by
        have h := (hLobe C.contactState hCandy).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (mouth, C.contactState) =
            some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase hfullGrooved hfullTrace
            hcrossed hmouthLink (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let half := dTravel + lTravel
      have hHalfAlt :
          stepN w half (outside, alternate) =
            some (outside, C.contactState) := by
        dsimp [half]
        rw [stepN_add, hDaltEnd]
        exact hReverseEnd
      have hHalfState :
          stepN w half (outside, C.contactState) =
            some (outside, alternate) := by
        dsimp [half]
        rw [stepN_add, hDstateEnd]
        exact hForwardEnd
      have hHalfAltPhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact twoHistory_twoPhase_concat hDaltEnd hDaltPhase
          hReversePhase d (by simpa [half] using hd)
      have hHalfStatePhase : ∀ d, d ≤ half → ∃ port phase,
          stepN w d (outside, C.contactState) =
            some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact twoHistory_twoPhase_concat hDstateEnd hDstatePhase
          hForwardPhase d (by simpa [half] using hd)
      let period := half + half
      have hperiod :
          stepN w period (outside, alternate) =
            some (outside, alternate) := by
        dsimp [period]
        rw [stepN_add, hHalfAlt]
        exact hHalfState
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (outside, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact twoHistory_twoPhase_concat hHalfAlt hHalfAltPhase
          hHalfStatePhase d (by simpa [period] using hd)
      have hpositive : 0 < period := by
        have hdpos := (ManufacturedReflector.stay D).travel_pos
        dsimp [period, half, dTravel, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow
    · simp only [List.mem_singleton] at hcore
      have hentryEq : entry = R.mouth := congrArg Prod.fst hcore
      have hmouthEq : mouth = R.arm := congrArg Prod.snd hcore
      subst entry
      subst mouth
      have houtsideEq : outside = R.arm := by
        rw [R.selfLink] at hmouthLink
        exact (Option.some.inj hmouthLink).symm
      subst outside
      let lTravel := candy.length + 2
      have hReverseEnd :
          stepN w lTravel (R.arm, alternate) =
            some (R.arm, C.contactState) := by
        have h := (hLobe alternate hCandyFlip).1
        change stepN w lTravel (R.arm, alternate) =
          some (R.arm, flipAt alternate k) at h
        dsimp [alternate] at h
        simpa [flipAt_flipAt] using h
      have hForwardEnd :
          stepN w lTravel (R.arm, C.contactState) =
            some (R.arm, alternate) := by
        have h := (hLobe C.contactState hCandy).1
        simpa [lTravel, alternate, k] using h
      have hReversePhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        dsimp [alternate, k]
        exact explicit_lobe_reverse_travel_two_phase
          hentryBranch hentryMouthSwitch hfullGrooved hfullTrace
          hcrossed hCandyForeign hmouthLink
          (by simpa [lTravel] using hd)
      have hForwardPhase : ∀ d, d ≤ lTravel → ∃ port phase,
          stepN w d (R.arm, C.contactState) =
            some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        obtain ⟨port, phase, hrun, hphase⟩ :=
          explicit_lobe_travel_two_phase hfullGrooved hfullTrace
            hcrossed hmouthLink (by simpa [lTravel] using hd)
        refine ⟨port, phase, hrun, ?_⟩
        dsimp [alternate, k]
        rcases hphase with h | h
        · exact Or.inr h
        · exact Or.inl h
      let period := lTravel + lTravel
      have hperiod :
          stepN w period (R.arm, alternate) =
            some (R.arm, alternate) := by
        dsimp [period]
        rw [stepN_add, hReverseEnd]
        exact hForwardEnd
      have hwindow : ∀ d, d ≤ period → ∃ port phase,
          stepN w d (R.arm, alternate) = some (port, phase) ∧
            (phase = alternate ∨ phase = C.contactState) := by
        intro d hd
        exact twoHistory_twoPhase_concat hReverseEnd hReversePhase
          hForwardPhase d (by simpa [period] using hd)
      have hpositive : 0 < period := by
        dsimp [period, lTravel]
        omega
      exact periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow
  refine ⟨outside, mouth, ?_, ?_⟩
  · simpa [alternate, k] using hreach
  · simpa [alternate] using hallAfter

/-- The stay-reflector forward branch uses only the two already historical
contact corners, hence it satisfies the requested budget two with an empty
fresh list. -/
theorem SecondHistoryContactData.changed_forward_stay_two_novelty
    {w : Wiring} {N g e : Nat}
    {R : ManufacturedStayReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w (.stay R) B)
    {next : Tongues}
    (harrive :
      arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged :
      next (C.fresh.1 / 3) ≠
        C.contactState (C.fresh.1 / 3))
    {oriented : Passage} {repaired : Tongues}
    (horiented :
      oriented ∈
        (ManufacturedReflector.stay R).orientedRoute C.contactState)
    (horientedGroove :
      arrive C.contactState oriented.2 =
        (oriented.1, C.contactState))
    (horientedSwitch :
      passageSwitch oriented = C.fresh.1 / 3)
    (hforward : C.fresh.2 = oriented.2)
    (hrepair :
      arrive next oriented.1 = (oriented.2, repaired))
    (hrestored :
      arrive repaired oriented.2 = (oriented.1, repaired))
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
      times (C.contactHistory N) 2 := by
  obtain ⟨outside, mouth, hreach, hall⟩ :=
    C.changed_forward_stay_two_phase_tail harrive hchanged
      horiented horientedGroove horientedSwitch hforward
      hrepair hrestored
  let K := C.approach.length + 1
  let alternate := flipAt C.contactState (mouth / 3)
  have hreach' :
      stepN w K (e, B.baseState) = some (outside, alternate) := by
    simpa [K, alternate] using hreach
  have hentryHistorical :
      VectorCount.restrict N alternate ∈ C.contactHistory N := by
    apply C.mem_contactHistory
    right
    have hm := C.mem_prefixHistory
      (N := N) (j := K) (by simp [K])
    simpa [restrictedTonguesAt, tonguesAt, hreach'] using hm
  have hstateHistorical :
      VectorCount.restrict N C.contactState ∈ C.contactHistory N :=
    C.contact_pre_mem
  refine ⟨[], by simp, ?_⟩
  intro j _hj
  simp only [List.append_nil]
  by_cases hjK : j < K
  · apply C.mem_contactHistory
    right
    exact C.mem_prefixHistory (N := N) (j := j) (by
      dsimp [K] at hjK
      omega)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hall d
    have hglobal :
        stepN w j (e, B.baseState) = some (port, phase) := by
      rw [hjEq, stepN_add, hreach']
      exact hrun
    have hvector :
        restrictedTonguesAt w N (e, B.baseState) j =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [alternate, h] using hentryHistorical
    · simpa [h] using hstateHistorical
private theorem arrive_state_eq_of_bit_eq
    {u v : Tongues} {p x : Nat}
    (harrive : arrive u p = (x, v))
    (hbit : v (p / 3) = u (p / 3)) :
    v = u := by
  unfold arrive at harrive
  by_cases hp : p % 3 = 0
  · rw [if_pos hp] at harrive
    exact (congrArg Prod.snd harrive).symm
  · rw [if_neg hp] at harrive
    have hv : v = pin u p :=
      (congrArg Prod.snd harrive).symm
    rw [hv] at hbit ⊢
    apply pin_of_agrees
    simpa [pin] using hbit.symm

/-- Exact all-time phase law for a backward old-support contact.  Time zero
has the incoming state; every positive time has the settled post-contact
state. -/
theorem backward_contact_all_time_two_phase_two_history
    {w : Wiring} {g e p oldEntry : Nat}
    {oldBase oldEnd u v : Tongues}
    {recorded approach : List Passage}
    (hrecorded :
      PhysicalTrace w (g, oldBase) recorded (oldEntry, oldEnd))
    (hrecordedGrooved : PassagesGrooved v recorded)
    (hentry : w.link e = some g)
    (hcontact : arrive u p = (oldEntry, v))
    (happroach : PhysicalTrace w (e, u) approach (p, u))
    (happroachGrooved : PassagesGrooved v approach) :
    ∀ m, ∃ port phase,
      stepN w m (p, u) = some (port, phase) ∧
        (phase = u ∨ phase = v) := by
  have hback := physicalTrace_contact_retraces_prefix
    hrecorded hrecordedGrooved hentry hcontact
  have hforward :=
    happroach.replay_grooved v happroachGrooved
  let cycle := (p, oldEntry) ::
    reversePassages recorded ++ approach
  have hcycle :
      PhysicalTrace w (p, u) cycle (p, v) := by
    dsimp [cycle]
    simpa [List.append_assoc] using hback.append hforward
  have hheadGrooved : arrive v oldEntry = (p, v) := by
    have hbackLocal := arrive_back u p
    rwa [hcontact] at hbackLocal
  have hallGrooved : PassagesGrooved v cycle := by
    intro passage hp
    dsimp [cycle] at hp
    rcases List.mem_cons.mp hp with hhead | htail
    · simpa [hhead] using hheadGrooved
    · rcases List.mem_append.mp htail with hold | hnew
      · exact reversePassages_grooved
          hrecordedGrooved passage hold
      · exact happroachGrooved passage hnew
  have hperiod :
      stepN w cycle.length (p, v) = some (p, v) := by
    dsimp [cycle]
    exact run_grooved_passages w v p oldEntry p
      (reversePassages recorded ++ approach)
      hcycle.linked hallGrooved hcycle.last_link
  have hcycleV : PhysicalTrace w (p, v) cycle (p, v) :=
    hcycle.replay_grooved v hallGrooved
  have hpositive : 0 < cycle.length := by
    dsimp [cycle]
    simp
  have hallV : ∀ m, ∃ port,
      stepN w m (p, v) = some (port, v) := by
    intro m
    have hwindow : ∀ d, d ≤ cycle.length → ∃ port phase,
        stepN w d (p, v) = some (port, phase) ∧
          (phase = v ∨ phase = v) := by
      intro d hd
      obtain ⟨port, hrun⟩ :=
        hcycleV.grooved_prefix_tongues v hallGrooved hd
      exact ⟨port, v, hrun, Or.inl rfl⟩
    obtain ⟨port, phase, hrun, hphase⟩ :=
      periodic_two_phase_prefix_tongues
        hpositive hperiod hwindow m
    rcases hphase with h | h
    · exact ⟨port, by rwa [h] at hrun⟩
    · exact ⟨port, by rwa [h] at hrun⟩
  have hfromU : ∀ m, 1 ≤ m → ∃ port,
      stepN w m (p, u) = some (port, v) := by
    intro m hm
    cases hback with
    | @cons _ _ q₀ _ v' _ _ harrive' hlink htailBack =>
        have hv' : v' = v := by
          have h := harrive'.symm.trans hcontact
          exact congrArg Prod.snd h
        rw [hv'] at harrive' htailBack
        have htail := htailBack.append hforward
        have hone :
            stepN w 1 (p, u) = some (q₀, v) := by
          simp [stepN, step, harrive', hlink]
        let m' := m - 1
        have hmEq : m = 1 + m' := by
          dsimp [m']
          omega
        have htailGrooved :
            PassagesGrooved v
              (reversePassages recorded ++ approach) := by
          intro passage hp
          exact hallGrooved passage
            (List.mem_cons_of_mem _ hp)
        by_cases hfirst :
            m' ≤ (reversePassages recorded ++ approach).length
        · obtain ⟨port, hrun⟩ :=
            htail.grooved_prefix_tongues
              v htailGrooved hfirst
          refine ⟨port, ?_⟩
          rw [hmEq, stepN_add, hone]
          simpa using hrun
        · let m'' := m' -
              (reversePassages recorded ++ approach).length
          have hm'Eq : m' =
              (reversePassages recorded ++ approach).length +
                m'' := by
            dsimp [m'']
            omega
          obtain ⟨port, hrun⟩ := hallV m''
          refine ⟨port, ?_⟩
          rw [hmEq, stepN_add, hone]
          simp only [Option.bind_some]
          rw [hm'Eq, stepN_add]
          have htailV :=
            htail.replay_grooved v htailGrooved
          rw [htailV.sound]
          simpa using hrun
  intro m
  cases m with
  | zero =>
      exact ⟨p, u, by simp [stepN], Or.inl rfl⟩
  | succ m =>
      obtain ⟨port, hrun⟩ := hfromU (m + 1) (by omega)
      exact ⟨port, v, hrun, Or.inr rfl⟩

/-- Any backward first support contact, changing or not, has no novelty after
the literal contact prefix: its two possible states are precisely the
pre-vector and post-vector already recorded by prefixHistory. -/
theorem SecondHistoryContactData.backward_contact_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    {next : Tongues}
    (harrive :
      arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    {oriented : Passage}
    (horiented :
      oriented ∈ A.orientedRoute C.contactState)
    (horientedGroove :
      arrive C.contactState oriented.2 =
        (oriented.1, C.contactState))
    (horientedSwitch :
      passageSwitch oriented = C.fresh.1 / 3)
    (hbackward : C.fresh.2 = oriented.1)
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
      times (C.contactHistory N) 2 := by
  obtain ⟨recorded, tail, hrouteSplit⟩ :=
    List.append_of_mem horiented
  have hroute :=
    A.orientedRoute_trace C.contactState C.old_grooves
  have hrouteSimple :=
    A.orientedRoute_simple C.contactState
  have hrouteGrooved :=
    hroute.grooved_of_switchSimple hrouteSimple
  have hprefixData :=
    simple_grooved_trace_prefix_to_occurrence
      hroute hrouteSplit hrouteGrooved hrouteSimple
  have hrecorded := hprefixData.1
  have hrecordedSimple : SwitchSimple recorded := by
    unfold SwitchSimple at hrouteSimple ⊢
    rw [hrouteSplit] at hrouteSimple
    simp only [List.map_append, List.map_cons] at hrouteSimple
    exact (List.nodup_append.mp hrouteSimple).1
  have hrecordedGrooved :
      PassagesGrooved C.contactState recorded :=
    hrecorded.grooved_of_switchSimple hrecordedSimple
  have hrecordedForeign : ∀ passage ∈ recorded,
      passageSwitch passage ≠ C.fresh.1 / 3 := by
    intro passage hp hEq
    apply hprefixData.2 passage hp
    exact hEq.trans horientedSwitch.symm
  have happroachSimple : SwitchSimple C.approach := by
    have hs := B.exploration_simple
    unfold SwitchSimple at hs ⊢
    rw [C.split] at hs
    simp only [List.map_append, List.map_cons] at hs
    exact (List.nodup_append.mp hs).1
  have happroachGrooved :
      PassagesGrooved C.contactState C.approach :=
    C.approach_trace.grooved_of_switchSimple happroachSimple
  have happroachForeign : ∀ passage ∈ C.approach,
      passageSwitch passage ≠ C.fresh.1 / 3 := by
    have hs := B.exploration_simple
    unfold SwitchSimple at hs
    rw [C.split] at hs
    simp only [List.map_append, List.map_cons] at hs
    have hparts := List.nodup_append.mp hs
    intro passage hp hEq
    have hne := hparts.2.2 (passageSwitch passage)
      (List.mem_map.mpr ⟨passage, hp, rfl⟩)
      (passageSwitch C.fresh) (by simp)
    exact hne (by
      simpa [passageSwitch] using hEq)
  have hnextForm :
      next = C.contactState ∨
        next =
          flipAt C.contactState (C.fresh.1 / 3) := by
    by_cases hchanged :
        next (C.fresh.1 / 3) ≠
          C.contactState (C.fresh.1 / 3)
    · exact Or.inr
        (changed_arrival_eq_flipAt harrive hchanged)
    · left
      apply arrive_state_eq_of_bit_eq harrive
      exact Classical.not_not.mp hchanged
  have hrecordedNext : PassagesGrooved next recorded := by
    rcases hnextForm with hsame | hflip
    · simpa [hsame] using hrecordedGrooved
    · rw [hflip]
      exact grooved_after_flip_other
        hrecordedGrooved hrecordedForeign
  have happroachNext :
      PassagesGrooved next C.approach := by
    rcases hnextForm with hsame | hflip
    · simpa [hsame] using happroachGrooved
    · rw [hflip]
      exact grooved_after_flip_other
        happroachGrooved happroachForeign
  have happroachReplay :
      PhysicalTrace w (e, C.contactState) C.approach
        (C.fresh.1, C.contactState) :=
    C.approach_trace.replay_grooved
      C.contactState happroachGrooved
  have hcontact :
      arrive C.contactState C.fresh.1 =
        (oriented.1, next) := by
    simpa [hbackward] using harrive
  have hall :=
    backward_contact_all_time_two_phase_two_history
      hrecorded hrecordedNext A.entryEdge hcontact
      happroachReplay happroachNext
  have hpreHistorical :
      VectorCount.restrict N C.contactState ∈
        C.contactHistory N :=
    C.contact_pre_mem
  have hpostHistorical :
      VectorCount.restrict N next ∈ C.contactHistory N := by
    obtain ⟨post, hpost, hmem⟩ :=
      C.contact_post_mem (N := N)
    have hpostEq : post = next := by
      rw [harrive] at hpost
      exact (Prod.mk.inj hpost).2.symm
    simpa [hpostEq] using hmem
  let K := C.approach.length
  have hreach :
      stepN w K (e, B.baseState) =
        some (C.fresh.1, C.contactState) := by
    simpa [K] using C.approach_trace.sound
  refine ⟨[], by simp, ?_⟩
  intro j _hj
  simp only [List.append_nil]
  by_cases hjK : j < K
  · apply C.mem_contactHistory
    right
    exact C.mem_prefixHistory (N := N) (j := j) (by
      dsimp [K] at hjK
      omega)
  · let d := j - K
    have hjEq : j = K + d := by
      dsimp [d]
      omega
    obtain ⟨port, phase, hrun, hphase⟩ := hall d
    have hglobal :
        stepN w j (e, B.baseState) = some (port, phase) := by
      rw [hjEq, stepN_add, hreach]
      exact hrun
    have hvector :
        restrictedTonguesAt w N (e, B.baseState) j =
          VectorCount.restrict N phase := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    rcases hphase with h | h
    · simpa [h] using hpreHistorical
    · simpa [h] using hpostHistorical
/-- Every first old-support contact that actually changes its tongue has the
unconditional two-novelty cover: backward orientation is the historical
two-phase lasso, while forward orientation is the exact stay/flip splice
proved above. -/
theorem SecondHistoryContactData.changed_contact_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    {next : Tongues}
    (harrive :
      arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged :
      next (C.fresh.1 / 3) ≠
        C.contactState (C.fresh.1 / 3))
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
      times (C.contactHistory N) 2 := by
  obtain ⟨path, hpath, old, hold, hsameSwitch⟩ := C.touches
  have hswitch :
      passageSwitch old = C.fresh.1 / 3 := by
    simpa [passageSwitch] using hsameSwitch
  obtain ⟨oriented, horiented, horientedGroove,
      horientedSwitch, hdirection⟩ :=
    A.changed_contact_on_orientedRoute
      C.contactState next C.old_grooves hpath hold
      hswitch harrive hchanged
  rcases hdirection with hbackward | hforward
  · exact C.backward_contact_two_novelty
      harrive horiented horientedGroove horientedSwitch
      hbackward times
  · obtain ⟨hforwardExit, repaired, hrepair, hrestored⟩ :=
      hforward
    cases A with
    | stay R =>
        exact C.changed_forward_stay_two_novelty
          harrive hchanged horiented horientedGroove
          horientedSwitch hforwardExit hrepair hrestored times
    | flip R =>
        exact C.changed_forward_flip_two_novelty
          harrive hchanged horiented horientedGroove
          horientedSwitch hforwardExit hrepair hrestored times

/-- The already-proved two-novelty contact tail transfers unchanged from
the literal prefix history to the compressed coefficient-one history. -/
theorem SecondHistoryContactData.changed_contact_two_novelty_charged
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    {next : Tongues}
    (harrive : arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged : next (C.fresh.1 / 3) ≠
      C.contactState (C.fresh.1 / 3))
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState) times
      (C.damageContactHistory N next) 2 := by
  obtain ⟨fresh, hfresh, hmem⟩ :=
    C.changed_contact_two_novelty harrive hchanged times
  refine ⟨fresh, hfresh, ?_⟩
  intro k hk
  rcases List.mem_append.mp (hmem k hk) with hhistory | hfreshMem
  · apply List.mem_append_left
    exact C.mem_damageContactHistory_of_mem_contactHistory
      harrive hhistory
  · exact List.mem_append_right _ hfreshMem

private theorem grooved_same_switch_passages_eq_or_reverse_two_history
    {state : Tongues} {old fresh : Passage}
    (hold : arrive state old.2 = (old.1, state))
    (hfresh : arrive state fresh.1 = (fresh.2, state))
    (hswitch : passageSwitch old = passageSwitch fresh) :
    fresh = old ∨ fresh = (old.2, old.1) := by
  have hswitch' : old.1 / 3 = fresh.1 / 3 := by
    simpa [passageSwitch] using hswitch
  have hexit := grooved_contact_exits_on_old_passage
    hold hfresh hswitch'
  have hback := arrive_back state fresh.1
  rw [hfresh] at hback
  rcases hexit with hentrySide | hexitSide
  · have hforward := groove_forward hold
    have hback' := hback
    rw [hentrySide, hforward] at hback'
    have hfirst : fresh.1 = old.2 :=
      (congrArg Prod.fst hback').symm
    right
    apply Prod.ext
    · exact hfirst
    · exact hentrySide
  · rw [hexitSide, hold] at hback
    have hfirst : fresh.1 = old.1 :=
      (congrArg Prod.fst hback).symm
    left
    apply Prod.ext
    · exact hfirst
    · exact hexitSide

theorem ManufacturedReflector.two_history_nodup_union_bound_or_first_contact
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hgrooves : PathGrooves A.toSupported.paths A.activatedState)
    (pool : List (List Bool))
    (hpool : ∀ x ∈ pool,
      x ∈ A.sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N)
    (hnd : pool.Nodup) :
    pool.length ≤ N + 2 ∨
      Nonempty (SecondHistorySupportContact w A B) := by
  classical
  by_cases hAvoid : A.SupportAvoidsExploration B
  · exact Or.inl
      (A.two_sharp_histories_nodup_union_le_N_add_two
        hN B hbase hAvoid pool hpool hnd)
  · right
    have hgroovesBase :
        PathGrooves A.toSupported.paths B.baseState := by
      simpa [hbase] using hgrooves
    obtain ⟨approach, fresh, suffix, contactState, hsplit,
        hbefore, hafter, hcontactGrooves, hfresh, htouch⟩ :=
      A.first_support_contact_trace B A.activatedState hbase
        hgrooves hAvoid
    exact ⟨{
      approach := approach
      fresh := fresh
      suffix := suffix
      contactState := contactState
      split := hsplit
      approach_trace := by simpa [hbase] using hbefore
      suffix_trace := hafter
      old_grooves := hcontactGrooves
      approach_fresh := hfresh
      touches := htouch
    }⟩

/-- **Old-support contact rebase.**

These are exactly the dynamic fields returned by two successive
first-activation certificates.  If the first support is still grooved after
the second activation, the complete two-reflector theta theorem is periodic.
If it is broken, repeated-mouth and backward contacts are periodic and the
orientation theorem leaves only one forward, self-repairing contact.  Thus no
unclassified old-support contact remains. -/
theorem ManufacturedReflector.second_history_rebases_to_periodic_or_forward
    {w : Wiring} {g e travel : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (stateB : Tongues)
    (hbase : B.baseState = A.activatedState)
    (hactivated : stateB = B.activatedState)
    (hreach : stepN w travel (e, B.baseState) = some (g, stateB))
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths stateB) :
    EventuallyPeriodic w (e, B.baseState) ∨
      A.ForwardOrientedFault B := by
  by_cases hAafter : PathGrooves A.toSupported.paths stateB
  · exact Or.inl
      (activated_manufactured_pair_eventually_periodic
        A B B.baseState stateB hreach hAafter hB)
  · rcases damaged_support_periodic_or_outward_fault
      A B A.activatedState stateB hbase hactivated
        hA hB hAafter with hperiodic | houtward
    · exact Or.inl (EventuallyPeriodic.prepend hreach hperiodic)
    · have hbaseGrooves :
          PathGrooves A.toSupported.paths B.baseState := by
        simpa [hbase] using hA
      exact outward_fault_eventuallyPeriodic_or_forward
        A B houtward hbaseGrooves

/-- If the fresh suffix stops inside the old selected-route tail, every
remaining fresh passage is grooved in the post-contact state.  Hence the
second construction reaches its pre-return port without another tongue
change. -/
theorem ManufacturedReflector.ForwardOrientedFault.preReturn_state_eq_contact
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    {approach : List Passage} {p x : Nat}
    {suffix : List Passage} {u v : Tongues}
    {oriented : Passage} {oldPrefix oldTail extra : List Passage}
    (hsplit : B.exploration = approach ++ (p, x) :: suffix)
    (happroach :
      PhysicalTrace w (e, B.baseState) approach (p, u))
    (hrouteSplit :
      A.orientedRoute u = oldPrefix ++ oriented :: oldTail)
    (hgrooves : PathGrooves A.toSupported.paths u)
    (harrive : arrive u p = (x, v))
    (hchanged : v (p / 3) ≠ u (p / 3))
    (horientedSwitch : passageSwitch oriented = p / 3)
    (htail : oldTail = suffix ++ extra) :
    B.preReturn.2 = v := by
  have hroute := A.orientedRoute_trace u hgrooves
  have hrouteSimple := A.orientedRoute_simple u
  have hrouteGrooved :=
    hroute.grooved_of_switchSimple hrouteSimple
  have hOldTailGrooved : PassagesGrooved u oldTail := by
    intro passage hpassage
    apply hrouteGrooved passage
    rw [hrouteSplit]
    exact List.mem_append_right oldPrefix
      (List.mem_cons_of_mem oriented hpassage)
  have hOldTailForeign :
      ∀ passage ∈ oldTail, passageSwitch passage ≠ p / 3 := by
    have hsimple := hrouteSimple
    unfold SwitchSimple at hsimple
    rw [hrouteSplit] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    have htailSimple := (List.nodup_append.mp hsimple).2.1
    rw [List.nodup_cons] at htailSimple
    intro passage hpassage hEq
    apply htailSimple.1
    apply List.mem_map.mpr
    exact ⟨passage, hpassage,
      hEq.trans horientedSwitch.symm⟩
  have hflip : v = flipAt u (p / 3) :=
    changed_arrival_eq_flipAt harrive hchanged
  have hOldTailGroovedV : PassagesGrooved v oldTail := by
    rw [hflip]
    exact grooved_after_flip_other
      hOldTailGrooved hOldTailForeign
  have hSuffixGroovedV : PassagesGrooved v suffix := by
    intro passage hpassage
    apply hOldTailGroovedV passage
    rw [htail]
    exact List.mem_append_left extra hpassage
  have hnew := B.exploration_trace
  rw [hsplit] at hnew
  obtain ⟨middle, hbefore, hafter⟩ := hnew.split_append
  have hmiddle : middle = (p, u) := by
    have h₁ := hbefore.sound
    have h₂ := happroach.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hafter with
  | @cons _ _ q _ next _ _ hhead _ hrest =>
      have hnext : next = v := by
        rw [harrive] at hhead
        exact (Prod.mk.inj hhead).2.symm
      subst next
      have hreplay :=
        hrest.replay_grooved v hSuffixGroovedV
      have hactual := hrest.sound
      have hreplayed := hreplay.sound
      rw [hactual] at hreplayed
      exact congrArg Prod.snd (Option.some.inj hreplayed)

theorem ManufacturedReflector.changed_support_contact_all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (C : SecondHistoryContactData w A B)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {next : Tongues}
    (harrive : arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged : next (C.fresh.1 / 3) ≠
      C.contactState (C.fresh.1 / 3))
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  let firstTravel :=
    A.exploration.length + A.runway.length + 1
  let localTimes :=
    (times.filter (fun k => decide (firstTravel < k))).map
      (fun k => k - firstTravel)
  let history := C.damageContactHistory N next
  have hreachA :
      stepN w firstTravel (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hreachBoundary :
      stepN w firstTravel (g, A.baseState) =
        some (e, B.baseState) := by
    simpa [hbase] using hreachA
  have hlocalCover :
      NoveltyCoverOn w N (e, B.baseState) localTimes history 2 := by
    dsimp [localTimes, history]
    exact C.changed_contact_two_novelty_charged
      harrive hchanged _
  obtain ⟨fresh, hfreshLength, hlocalMem⟩ := hlocalCover
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times history 2 := by
    refine ⟨fresh, hfreshLength, ?_⟩
    intro k hk
    by_cases hprefix : k ≤ firstTravel
    · have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hA (j := k) (by
          simpa [firstTravel] using hprefix)
      apply List.mem_append_left
      dsimp [history]
      unfold SecondHistoryContactData.damageContactHistory
      exact List.mem_append_left _
        (A.mem_sharpHistoryCore_of_mem hm)
    · have hafter : firstTravel < k := by omega
      let q := k - firstTravel
      have hkEq : k = firstTravel + q := by
        dsimp [q]
        omega
      have hkFiltered :
          k ∈ times.filter (fun t => decide (firstTravel < t)) := by
        apply List.mem_filter.mpr
        exact ⟨hk, by simp [hafter]⟩
      have hqMem : q ∈ localTimes := by
        dsimp [localTimes]
        apply List.mem_map.mpr
        exact ⟨k, hkFiltered, rfl⟩
      have hglobalLive := hlive k hk
      have hlocalLive :
          (stepN w q (e, B.baseState)).isSome := by
        rw [hkEq, stepN_add, hreachBoundary] at hglobalLive
        exact hglobalLive
      have hlocalReach :
          ∃ finish, stepN w q (e, B.baseState) = some finish :=
        Option.isSome_iff_exists.mp hlocalLive
      have hshift :=
        tonguesAt_add_of_reaches hreachBoundary hlocalReach
      have hvector :
          restrictedTonguesAt w N (g, A.baseState) k =
            restrictedTonguesAt w N (e, B.baseState) q := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [hvector]
      exact hlocalMem q hqMem
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have hhistory : history.length ≤ N + 3 := by
    dsimp [history]
    exact C.damageContactHistory_length_le_N_add_three
      hN hbase hbaseGrooves next
  omega

/-- Either the old support remains grooved at the second pre-return, or the
first damaging support passage supplies freshness-free contact data and an
actual tongue change.  Earlier harmless support passages are retained in
the approach; they are not recursively classified or charged. -/
theorem ManufacturedReflector.preReturn_grooved_or_changed_support_contact
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState) :
    PathGrooves A.toSupported.paths B.preReturn.2 ∨
      ∃ C : SecondHistoryContactData w A B, ∃ next : Tongues,
        arrive C.contactState C.fresh.1 = (C.fresh.2, next) ∧
        next (C.fresh.1 / 3) ≠ C.contactState (C.fresh.1 / 3) := by
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  by_cases hpre : PathGrooves A.toSupported.paths B.preReturn.2
  · exact Or.inl hpre
  · right
    obtain ⟨approach, p, x, suffix, u, v, path, old,
        hsplit, hprefix, hgrooves, harrive,
        hpath, hold, hswitch, hchanged, _hExit⟩ :=
      B.exploration_trace.first_changed_support_passage
        hbaseGrooves hpre
    have hfull := B.exploration_trace
    rw [hsplit] at hfull
    obtain ⟨middle, hbefore, hafter⟩ := hfull.split_append
    have hmiddle : middle = (p, u) := by
      have h₁ := hbefore.sound
      have h₂ := hprefix.sound
      rw [h₂] at h₁
      exact (Option.some.inj h₁).symm
    subst middle
    let C : SecondHistoryContactData w A B := {
      approach := approach
      fresh := (p, x)
      suffix := suffix
      contactState := u
      split := hsplit
      approach_trace := hprefix
      suffix_trace := hafter
      old_grooves := hgrooves
      touches := ⟨path, hpath, old, hold, by
        simpa [passageSwitch] using hswitch⟩
    }
    refine ⟨C, v, ?_, ?_⟩
    · simpa [C] using harrive
    · simpa [C] using hchanged

/-- **Two opposite manufactured reflectors, raw all-times coefficient-one
bound.**  If the old support survives to the second pre-return, the verified
four-vector protected repair gives N+6.  Otherwise the first damaging
support passage invokes the N+5 theorem above.  This is an unconditional
general-N theorem over the actual `stepN` trajectory. -/
theorem ManufacturedReflector.two_reflector_all_run_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 6 := by
  rcases A.preReturn_grooved_or_changed_support_contact
      B hbase hA with hpre | ⟨C, next, harrive, hchanged⟩
  · have hreachA : stepN w
        (A.exploration.length + A.runway.length + 1)
        (g, A.baseState) = some (e, A.activatedState) :=
      A.manufacturing_journey_reaches_activated hA
    have hreachB := B.manufacturing_journey_reaches_activated hB
    have hreachB' : stepN w
        (B.exploration.length + B.runway.length + 1)
        (e, A.activatedState) = some (g, B.activatedState) := by
      rw [← hbase]
      exact hreachB
    have hAatBase :
        PathGrooves A.toSupported.paths B.baseState := by
      rw [hbase]
      exact hA
    have htail : ∀ tailTimes : List Nat,
        (∀ k ∈ tailTimes,
          (stepN w k (g, B.activatedState)).isSome) →
        (tailTimes.map
          (restrictedTonguesAt w N
            (g, B.activatedState))).Nodup →
        tailTimes.length ≤ 4 := by
      intro tailTimes htailLive htailNodup
      exact manufactured_pair_protected_repair_distinct_le_four
        A B hAatBase hB tailTimes htailLive htailNodup
    exact
      two_manufacturing_journeys_preserved_support_then_four_tail_le_N_add_six
        hN A B A.activatedState B.activatedState
        rfl rfl hreachA hA hbase rfl hreachB' hB hpre htail
        times hlive hnd
  · have hc : times.length ≤ N + 5 :=
      A.changed_support_contact_all_run_distinct_le_N_add_five
        hN B C hbase hA harrive hchanged times hlive hnd
    omega

end GeneralN
