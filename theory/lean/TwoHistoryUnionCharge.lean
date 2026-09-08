import StateLawTwoCandidate
import PairActionCorners

/-!
# One coordinate budget for construction and continuation

A productive writer in a switch-simple trace cannot belong to a support
family grooved at both endpoints. Its first writers, the old reusable
switches, and any reserved coordinates therefore fit in one `N`-switch list.
Construction histories omit a known duplicate sample and share their common
boundary; the resulting covers cost `N+3`, or `N+2` with one reserve.
-/

namespace GeneralN

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
      simp only [SwitchSimple, List.map_append, List.map_cons] at hs
      simp only [ManufacturedReflector.reusableSwitches, List.map_append]
      grind

/-- Membership in `reusableSwitches` is exactly membership in one of the
two reusable support paths. -/
theorem ManufacturedReflector.mem_reusableSwitches
    {w : Wiring} {g e k : Nat}
    (A : ManufacturedReflector w g e)
    (hk : k ∈ A.reusableSwitches) :
    ∃ path ∈ A.toSupported.paths, ∃ passage ∈ path,
      passageSwitch passage = k := by
  cases A <;>
    simp only [ManufacturedReflector.reusableSwitches, ManufacturedReflector.toSupported,
      ManufacturedStayReflector.toSupported, ManufacturedFlipReflector.toSupported,
      List.mem_map, List.mem_append, List.mem_cons] at hk ⊢ <;> grind

/-- A productive passage in a switch-simple continuation cannot write an old
reusable coordinate when the old support is grooved at both endpoints. -/
theorem PhysicalTrace.productive_writer_not_old_reusable
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2)
    {k : Nat} (hk : k < passages.length)
    (hprod : RawProductiveAt w N start k) :
    rawWriterAt w start k ∉ A.reusableSwitches := by
  intro hreusable
  have hsurvives := htrace.simple_raw_productive_writer_survives hsimple hk hprod
  obtain ⟨path, hpath, old, hold, hswitch⟩ := A.mem_reusableSwitches hreusable
  exact hsurvives (by simpa [← hswitch] using
    (same_groove_same_tongue (hbase path hpath old hold) (hend path hpath old hold)).symm)

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
  have hmem : ∃ passage ∈ A.exploration, passageSwitch passage = k := by
    cases A <;> simp only [ManufacturedReflector.reusableSwitches,
      ManufacturedReflector.exploration, List.mem_map, List.mem_append, List.mem_cons] at hk ⊢ <;> grind
  obtain ⟨passage, hp, rfl⟩ := hmem
  exact A.exploration_trace.switch_lt hN passage hp

/-- Switch coordinates of the productive first writers in a manufactured
reflector's switch-simple construction. -/
def ManufacturedReflector.constructionFirstWriterSwitches
    {w : Wiring} {g e : Nat}
    (B : ManufacturedReflector w g e) (N : Nat) : List Nat :=
  (rawFirstWriterTimes w N (g, B.baseState)
      B.exploration.length).map
    (rawWriterAt w (g, B.baseState))

/-- The old reusable coordinates, the first productive writers of a
support-preserving simple continuation, and any duplicate-free list of extra
switches avoiding both share one ambient switch budget. -/
theorem ManufacturedReflector.reusable_add_continuation_first_writers_add_extras_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2)
    (extras : List Nat)
    (hextrasNodup : extras.Nodup)
    (hextrasLt : ∀ s ∈ extras, s < N)
    (hextrasReusable : ∀ s ∈ extras, s ∉ A.reusableSwitches)
    (hextrasWriters : ∀ s ∈ extras,
      s ∉ (rawFirstWriterTimes w N start passages.length).map (rawWriterAt w start)) :
    A.reusableSwitches.length +
      (rawFirstWriterTimes w N start passages.length).length + extras.length ≤ N := by
  let times := rawFirstWriterTimes w N start passages.length
  let writers := times.map (rawWriterAt w start)
  have hwritersNodup : writers.Nodup := by
    apply nodup_map_of_injective_on_mem
    · intro i hi j hj heq
      exact rawFirstWriterAt_injective (mem_rawFirstWriterTimes_iff.mp hi).2
        (mem_rawFirstWriterTimes_iff.mp hj).2 heq
    · exact List.Pairwise.filter _ List.nodup_range
  have hwriters : ∀ j ∈ writers, j < N ∧ j ∉ A.reusableSwitches := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    have hk := mem_rawFirstWriterTimes_iff.mp hk
    exact ⟨rawProductiveAt_writer_lt hN hk.2.1,
      htrace.productive_writer_not_old_reusable A hsimple hbase hend hk.1 hk.2.1⟩
  have hnd : (extras ++ (A.reusableSwitches ++ writers)).Nodup := by
    refine List.nodup_append.mpr ⟨hextrasNodup,
      List.nodup_append.mpr ⟨A.reusableSwitches_nodup, hwritersNodup, ?_⟩, ?_⟩ <;> grind
  have hbound := nodup_nat_lt_length (N := N) hnd (by
    have hlt : ∀ j ∈ A.reusableSwitches, j < N := fun _ hj => A.reusableSwitch_lt hN hj
    grind)
  simpa [writers, times, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbound

/-- The old reusable coordinates and the first productive writers of a
support-preserving simple continuation share one ambient switch budget. -/
theorem ManufacturedReflector.reusable_add_continuation_first_writers_le
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hbase : PathGrooves A.toSupported.paths start.2)
    (hend : PathGrooves A.toSupported.paths finish.2) :
    A.reusableSwitches.length +
      (rawFirstWriterTimes w N start passages.length).length ≤ N := by
  simpa using A.reusable_add_continuation_first_writers_add_extras_le hN htrace hsimple
    hbase hend [] List.nodup_nil (by simp) (by simp) (by simp)

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
  have htrace := R.candyTrace
  cases htrace with
  | @cons p x q u v passages finish harrive hlink tail =>
      have hv : v = R.mouthState := by
        unfold arrive at harrive
        rw [if_pos R.mouth_is_stem] at harrive
        exact (Prod.mk.inj harrive).2.symm
      have hnext : stepN w (R.runway.length + 1) (g, R.base) =
          some (q, R.mouthState) := by
        rw [stepN_add, R.runwayTrace.sound]
        simp [stepN, step, harrive, hlink, hv]
      simp [restrictedTonguesAt, tonguesAt, R.runwayTrace.sound, hnext]

/-- Omit a known duplicate sample: the stay activation, or the flip
reflector's pre-mouth sample, which equals the following sample. -/
def ManufacturedReflector.sharpHistoryCore
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) (N : Nat) : List (List Bool) :=
  match A with
  | .stay _ => (List.range (A.exploration.length + 1)).map
      (restrictedTonguesAt w N (g, A.baseState))
  | .flip R => ((List.range (A.exploration.length + 1)).erase R.runway.length).map
      (restrictedTonguesAt w N (g, A.baseState)) ++ [VectorCount.restrict N A.activatedState]

/-- Omitting the known duplicate loses no represented tongue vector. -/
theorem ManufacturedReflector.mem_sharpHistoryCore_of_mem
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e)
    {x : List Bool} (hx : x ∈ A.sharpConstructionHistory N) :
    x ∈ A.sharpHistoryCore N := by
  cases A with
  | stay R =>
      rcases List.mem_append.mp hx with hprefix | hactivated
      · exact hprefix
      · have hx : x = VectorCount.restrict N R.returnState := List.mem_singleton.mp hactivated
        rw [hx]
        apply List.mem_map.mpr
        exact ⟨(ManufacturedReflector.stay R).exploration.length,
          List.mem_range.mpr (by omega), by
            simp [restrictedTonguesAt, tonguesAt,
              (ManufacturedReflector.stay R).exploration_trace.sound,
              ManufacturedReflector.preReturn]⟩
  | flip R =>
      rcases List.mem_append.mp hx with hprefix | hactivated
      · apply List.mem_append_left
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hprefix
        by_cases heq : j = R.runway.length
        · subst j
          exact List.mem_map.mpr ⟨R.runway.length + 1,
            (List.mem_erase_of_ne (by omega)).mpr (List.mem_range.mpr (by
              simp only [ManufacturedReflector.exploration, List.length_append, List.length_cons]
              omega)),
            R.runway_boundary_repeated.symm⟩
        · exact List.mem_map.mpr ⟨j, (List.mem_erase_of_ne heq).mpr hj, rfl⟩
      · exact List.mem_append_right _ hactivated

/-- The compressed sharp history costs exactly one more vector than the
simple exploration has passages. -/
theorem ManufacturedReflector.sharpHistoryCore_length
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e) :
    (A.sharpHistoryCore N).length = A.exploration.length + 1 := by
  cases A with
  | stay R => simp [ManufacturedReflector.sharpHistoryCore]
  | flip R =>
      have hm : R.runway.length ∈ List.range
          ((ManufacturedReflector.flip R).exploration.length + 1) := by
        simp only [List.mem_range, ManufacturedReflector.exploration, List.length_append, List.length_cons]
        omega
      simp [ManufacturedReflector.sharpHistoryCore, List.length_erase_of_mem hm]

/-- The activated vector lies in the sharp history. -/
theorem ManufacturedReflector.activated_mem_sharpHistory
    {w : Wiring} {g e N : Nat} (A : ManufacturedReflector w g e) :
    VectorCount.restrict N A.activatedState ∈ A.sharpConstructionHistory N := by
  simp [ManufacturedReflector.sharpConstructionHistory]

/-- The pre-return vector lies in the sharp history. -/
theorem ManufacturedReflector.preReturn_mem_sharpHistory
    {w : Wiring} {g e N : Nat} (A : ManufacturedReflector w g e) :
    VectorCount.restrict N A.preReturn.2 ∈ A.sharpConstructionHistory N :=
  List.mem_append_left _ (List.mem_map.mpr ⟨A.exploration.length,
    List.mem_range.mpr (by omega),
    by simp [restrictedTonguesAt, tonguesAt, A.exploration_trace.sound]⟩)

/-- The activated endpoint is retained by the compressed first history. -/
theorem ManufacturedReflector.activated_mem_sharpHistoryCore
    {w : Wiring} {g e N : Nat}
    (A : ManufacturedReflector w g e) :
    VectorCount.restrict N A.activatedState ∈ A.sharpHistoryCore N :=
  A.mem_sharpHistoryCore_of_mem A.activated_mem_sharpHistory

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
    A.reusable_add_continuation_first_writers_le
      hN B.exploration_trace B.exploration_simple hbaseGrooves hpreGrooves
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

/-- One unused coordinate lowers the canonical two-construction history
from `N+3` to `N+2`, leaving room for two fresh repair-tail vectors. -/
theorem ManufacturedReflector.preservedTwoHistoryCore_length_le_N_add_two_of_reserved
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentA : Not (List.Mem k0 A.reusableSwitches))
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N))) :
    (A.preservedTwoHistoryCore B N).length <= N + 2 := by
  have hboundary :
      VectorCount.restrict N A.activatedState ∈
        B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge := A.reusable_add_continuation_first_writers_add_extras_le
    hN B.exploration_trace B.exploration_simple hbaseGrooves hpreGrooves [k0]
    (by simp) (by simpa using hk0)
    (by intro j hj; obtain rfl := List.mem_singleton.mp hj; exact habsentA)
    (by intro j hj; obtain rfl := List.mem_singleton.mp hj; exact habsentB)
  simp only [List.length_cons, List.length_nil] at hcharge
  have houter := A.exploration_length_le_reusable_add_one
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega


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
