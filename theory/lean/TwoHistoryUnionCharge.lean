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
