import StateLawTwoCandidate

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
structure SecondHistorySupportContact
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
  approach_fresh : ∀ prior ∈ approach, ¬ A.TouchesSupport prior
  touches : A.TouchesSupport fresh

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
def SecondHistorySupportContact.prefixHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (N : Nat) : List (List Bool) :=
  (List.range (C.approach.length + 2)).map
    (restrictedTonguesAt w N (e, B.baseState))

/-- Every second-journey vector through the contact belongs to the literal
prefix history. -/
theorem SecondHistorySupportContact.mem_prefixHistory
    {w : Wiring} {N g e j : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hj : j ≤ C.approach.length + 1) :
    restrictedTonguesAt w N (e, B.baseState) j ∈
      C.prefixHistory N := by
  unfold SecondHistorySupportContact.prefixHistory
  apply List.mem_map.mpr
  exact ⟨j, List.mem_range.mpr (by omega), rfl⟩

/-- The second prefix begins at the activated endpoint of the first
construction, so this shared boundary may be erased once. -/
theorem SecondHistorySupportContact.boundary_mem_prefixHistory
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState) :
    VectorCount.restrict N A.activatedState ∈ C.prefixHistory N := by
  have hzero := C.mem_prefixHistory (N := N) (j := 0) (by omega)
  simpa [restrictedTonguesAt, tonguesAt, stepN, hbase] using hzero

/-- A coefficient-one cover: the compressed first sharp history, followed
only by the second prefix through first contact, with the shared boundary
removed from the latter. -/
def SecondHistorySupportContact.contactHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (N : Nat) : List (List Bool) :=
  A.sharpHistoryCore N ++
    (C.prefixHistory N).erase
      (VectorCount.restrict N A.activatedState)

/-- Exact length of the first-contact cover. -/
theorem SecondHistorySupportContact.contactHistory_length
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState) :
    (C.contactHistory N).length =
      A.exploration.length + C.approach.length + 2 := by
  have hboundary := C.boundary_mem_prefixHistory (N := N) hbase
  unfold SecondHistorySupportContact.contactHistory
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length]
  simp [SecondHistorySupportContact.prefixHistory]
  omega

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
theorem SecondHistorySupportContact.mem_contactHistory
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
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

/-- **Coefficient-one first-contact union charge.**

Any duplicate-free selection drawn from the first complete sharp history and
the second journey only through its first old-support contact has size at
most N+3.  No overlap between the two lists is assumed. -/
theorem SecondHistorySupportContact.first_contact_prefix_nodup_union_le_N_add_three
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState)
    (pool : List (List Bool))
    (hpool : ∀ x ∈ pool,
      x ∈ A.sharpConstructionHistory N ∨
        x ∈ C.prefixHistory N)
    (hnd : pool.Nodup) :
    pool.length ≤ N + 3 := by
  have hsubset : ∀ x ∈ pool, x ∈ C.contactHistory N := by
    intro x hx
    exact C.mem_contactHistory (hpool x hx)
  have hcover := nodup_subset_length_two_history hnd hsubset
  have hlength := C.contactHistory_length_le_N_add_three hN hbase
  omega

/-- A three-vector post-contact novelty theorem is exactly sufficient for
the target N+6 count: the complete second construction is never paid for.
This is the generic assembly interface for the contact classification. -/
theorem SecondHistorySupportContact.prefix_then_three_novelty_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState)
    (times : List Nat)
    (hcover : NoveltyCoverOn w N (e, B.baseState)
      times (C.contactHistory N) 3)
    (hnd : (times.map
      (restrictedTonguesAt w N (e, B.baseState))).Nodup) :
    times.length ≤ N + 6 := by
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength := C.contactHistory_length_le_N_add_three hN hbase
  omega

/-- **Unconditional two-history reduction.**  Exact first-activation data
give either the `N+4` union charge or the first physical old-support contact;
the theorem does not assume that the histories overlap. -/
theorem ManufacturedReflector.two_history_bound_or_first_support_contact
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hgrooves : PathGrooves A.toSupported.paths A.activatedState) :
    (A.sharpConstructionHistory N ++
      (B.sharpConstructionHistory N).erase
        (VectorCount.restrict N A.activatedState)).length ≤ N + 4 ∨
      Nonempty (SecondHistorySupportContact w A B) := by
  classical
  by_cases hAvoid : A.SupportAvoidsExploration B
  · exact Or.inl
      (A.two_sharp_histories_length_le_N_add_four
        hN B hbase hAvoid)
  · right
    have hgroovesBase : PathGrooves A.toSupported.paths B.baseState := by
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

/-- **Unconditional NODUP two-history reduction.**

For the exact pair of opposite manufacturing journeys, every duplicate-free
selection from their two sharp histories has size at most N+2 unless the
second physical exploration has a concrete first contact with the reusable
support of the first.  No overlap premise is supplied by the caller. -/
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

/-- **Coefficient-one union reduction after contact normalization.**

For two exact opposite manufacturing journeys, a duplicate-free selection
from both sharp histories has at most N+2 states unless the constructed run
is already periodic or carries the single forward self-repair certificate.
The previous broad first-contact residue has disappeared. -/
theorem ManufacturedReflector.two_history_nodup_union_or_periodic_or_forward
    {w : Wiring} {N g e travel : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (stateB : Tongues)
    (hbase : B.baseState = A.activatedState)
    (hactivated : stateB = B.activatedState)
    (hreach : stepN w travel (e, B.baseState) = some (g, stateB))
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths stateB)
    (pool : List (List Bool))
    (hpool : ∀ x ∈ pool,
      x ∈ A.sharpConstructionHistory N ∨
        x ∈ B.sharpConstructionHistory N)
    (hnd : pool.Nodup) :
    pool.length ≤ N + 2 ∨
      EventuallyPeriodic w (e, B.baseState) ∨
        A.ForwardOrientedFault B := by
  by_cases hAvoid : A.SupportAvoidsExploration B
  · exact Or.inl
      (A.two_sharp_histories_nodup_union_le_N_add_two
        hN B hbase hAvoid pool hpool hnd)
  · rcases A.second_history_rebases_to_periodic_or_forward
      B stateB hbase hactivated hreach hA hB with
        hperiodic | hforward
    · exact Or.inr (Or.inl hperiodic)
    · exact Or.inr (Or.inr hforward)

/-- If the second activation actually damages the first support, the exact
first-activation preservation certificate localizes the extra coefficient to
one concrete turning event: either the final repeated mouth, or the unique
state-changing outward passage through that old support switch. -/
theorem ManufacturedReflector.second_history_damage_is_turning_resource
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (stateA stateB : Tongues)
    (hbase : B.baseState = stateA)
    (hactivated : stateB = B.activatedState)
    (hgrooves : PathGrooves A.toSupported.paths stateA)
    (hpreserves : ∀ j, j ∉ B.exploration.map passageSwitch →
      stateB j = stateA j)
    (hbroken : ¬ PathGrooves A.toSupported.paths stateB) :
    ∃ path ∈ A.toSupported.paths, ∃ old ∈ path,
      arrive stateB old.2 ≠ (old.1, stateB) ∧
      (passageSwitch old = B.preReturn.1 / 3 ∨
        ∃ approach p x suffix u v,
          B.exploration = approach ++ (p, x) :: suffix ∧
          passageSwitch (p, x) = passageSwitch old ∧
          PhysicalTrace w (e, B.baseState) approach (p, u) ∧
          arrive u p = (x, v) ∧
          u (passageSwitch old) = B.baseState (passageSwitch old) ∧
          B.preReturn.2 (passageSwitch old) = v (passageSwitch old) ∧
          v (passageSwitch old) ≠ u (passageSwitch old)) := by
  exact A.broken_support_change_location B stateA stateB
    hbase hactivated hgrooves hpreserves hbroken

end GeneralN
