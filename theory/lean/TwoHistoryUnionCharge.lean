import RunwayHistoricalOne
import CompleteRepairFour

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


/-!
## The manufacturing journey reaches the activated state

The one raw `stepN` fact every downstream counting file needs from the
old Gray-corner module, extracted so the sharp proof does not depend on
the Mellit corridor.
-/

namespace GeneralN

/-- The complete canonical manufacturing journey really ends at the
reflector's activated state.  This packages only raw `stepN` facts and is
useful for identifying the first-turnaround contact vector with the initial
corner of the following reflector pair. -/
theorem ManufacturedReflector.manufacturing_journey_reaches_activated
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState) :
    stepN w (A.exploration.length + A.runway.length + 1)
      (g, A.baseState) = some (e, A.activatedState) := by
  have hback :
      stepN w (A.runway.length + 1) A.preReturn =
        some (e, A.activatedState) := by
    have htrace := physicalTrace_contact_retraces_prefix
      A.runway_trace (A.runway_grooved hpaths)
      A.entryEdge A.return_arrive_mouth
    simpa [reversePassages_length] using htrace.sound
  have hlen :
      A.exploration.length + A.runway.length + 1 =
        A.exploration.length + (A.runway.length + 1) := by
    omega
  rw [hlen, stepN_add, A.exploration_trace.sound]
  exact hback


theorem nodup_map_nat_of_injective_on_two_history
    {f : Nat → Nat} {xs : List Nat}
    (hinj : ∀ x, x ∈ xs → ∀ y, y ∈ xs → f x = f y → x = y)
    (hnd : xs.Nodup) : (xs.map f).Nodup :=
  map_nodup_of_injective_on_mem_self_pivot f hnd hinj

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
    rawProductiveAt_changes_writer hprod
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
      B.exploration_simple hk hprod
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
  let times :=
    rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact nodup_filter_nat _ List.nodup_range
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
      A.second_exploration_productive_writer_not_reusable B hbaseGrooves hpreGrooves
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
def ManufacturedReflector.writerConstructionHistory
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


theorem ManufacturedFlipReflector.runway_boundary_repeated
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

def ManufacturedReflector.preservedTwoHistoryCore
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
    rcases hphase with h | h <;>
      exact ⟨port, by rwa [h] at hrun⟩
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

end GeneralN
