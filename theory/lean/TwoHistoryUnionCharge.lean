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

The one raw `stepN` fact every downstream counting file needs about the
canonical manufacturing journey.
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
/-- A productive event in a switch-simple trace permanently changes its
writer. Otherwise both adjacent prefix values would equal the common endpoint
value, contradicting productivity. No passage reconstruction is needed. -/
theorem PhysicalTrace.simple_raw_productive_writer_survives
    {w : Wiring} {N : Nat}
    {start finish : Nat × Tongues} {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    {k : Nat} (hk : k < passages.length)
    (hprod : RawProductiveAt w N start k) :
    finish.2 (rawWriterAt w start k) ≠
      start.2 (rawWriterAt w start k) := by
  obtain ⟨cur, next, hcur, hnext, _hstep, hchange⟩ :=
    rawProductiveAt_changes_writer hprod
  have hwriter : rawWriterAt w start k = cur.1 / 3 := by
    simp [rawWriterAt, rawEntryAt, hcur]
  rw [hwriter]
  intro heq
  have hpre := htrace.prefix_coordinate_eq_endpoint hsimple (Nat.le_of_lt hk)
    hcur (cur.1 / 3)
  have hpost := htrace.prefix_coordinate_eq_endpoint hsimple (by omega)
    hnext (cur.1 / 3)
  rw [heq] at hpre hpost
  exact hchange ((hpost.elim id id).trans (hpre.elim id id).symm)

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

/-- Switch coordinates of the productive first writers in a manufactured
reflector's switch-simple construction. -/
def ManufacturedReflector.constructionFirstWriterSwitches
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w g e) (N : Nat) : List Nat :=
  (rawFirstWriterTimes w N (g, B.baseState)
      B.exploration.length).map
    (rawWriterAt w (g, B.baseState))

/-- The old reusable support and the second construction's productive
first writers form a single duplicate-free list of coordinates below `N`.
All ordinary and reserved-coordinate counts use this same certificate. -/
theorem ManufacturedReflector.sharedConstructionCoordinates
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2) :
    (A.reusableSwitches ++ B.constructionFirstWriterSwitches N).Nodup ∧
      (∀ j ∈ A.reusableSwitches ++ B.constructionFirstWriterSwitches N, j < N) := by
  let times :=
    rawFirstWriterTimes w N (e, B.baseState)
      B.exploration.length
  let writers := times.map (rawWriterAt w (e, B.baseState))
  have htimesNodup : times.Nodup := by
    dsimp [times, rawFirstWriterTimes]
    exact nodup_filter_nat _ List.nodup_range
  have hwritersNodup : writers.Nodup := by
    dsimp [writers]
    apply nodup_map_of_injective_on_mem
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
  exact ⟨hnd, hlt⟩

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
  obtain ⟨hnd, hlt⟩ := A.sharedConstructionCoordinates hN B hbaseGrooves hpreGrooves
  simpa [ManufacturedReflector.constructionFirstWriterSwitches] using
    nodup_nat_lt_length hnd hlt

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
    x ∈ A.preservedTwoHistoryCore B N := by grind [
      ManufacturedReflector.mem_sharpHistoryCore_of_mem,
      ManufacturedReflector.mem_writerConstructionHistory_of_mem_sharp,
      ManufacturedReflector.preservedTwoHistoryCore,
      ManufacturedReflector.sharpConstructionHistory]


/-- The facing action mouth of a flip reflector is not part of its reusable
support. -/
theorem ManufacturedFlipReflector.action_not_mem_reusable
    {w : Wiring} {g e : Nat}
    (R : ManufacturedFlipReflector w g e) :
    R.actionSwitch ∉
      (ManufacturedReflector.flip R).reusableSwitches := by
  intro hmem
  change R.actionSwitch ∈
    ((R.runway ++ R.candy).map passageSwitch) at hmem
  obtain ⟨passage, hpassage, hswitch⟩ := List.mem_map.mp hmem
  rcases List.mem_append.mp hpassage with hrunway | hcandy
  · exact (R.support_foreign R.runway (by simp)
      passage hrunway) hswitch
  · exact (R.support_foreign R.candy (by simp)
      passage hcandy) hswitch

/-- The omitted action mouth is one of the counted finite switches. -/
theorem ManufacturedFlipReflector.action_lt
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedFlipReflector w g e) :
    R.actionSwitch < N := by
  have hlt :=
    (ManufacturedReflector.flip R).exploration_trace.switch_lt
      hN (R.mouth, R.firstArm) (by
        simp [ManufacturedReflector.exploration])
  simpa [passageSwitch,
    ManufacturedFlipReflector.actionSwitch] using hlt

end GeneralN
