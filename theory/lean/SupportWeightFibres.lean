import CanonicalProjectedEpochFrame
import BlockEpochAggregation

/-!
# Support-weight fibres

Occupied support decreases monotonically.  Consequently two times with the
same number of occupied coordinates have exactly the same support.  This lets
us partition any finite trajectory list by the integer weight

    trueCount (supportSnap slots k)

rather than by Boolean vectors.  There are only `slots.length + 1` possible
weights.

This file supplies the generic finite-fibre arithmetic, canonical minimum and
maximum times of a nonempty fibre, and the theorem turning equal endpoint
support into a fixed-support interval.
-/

namespace Echo

/-- Size of one integer-valued fibre. -/
def supportFibreSize {α : Type}
    (f : α → Nat) (q : Nat) (xs : List α) : Nat :=
  (xs.filter (fun x => f x = q)).length

/-- Sizes of all fibres with keys in `[0,K)`. -/
def supportFibreSizes {α : Type}
    (K : Nat) (f : α → Nat) (xs : List α) : List Nat :=
  (List.range K).map (fun q => supportFibreSize f q xs)

private theorem supportFibreSize_cons {α : Type}
    (f : α → Nat) (q : Nat) (x : α) (xs : List α) :
    supportFibreSize f q (x :: xs) =
      (if f x = q then 1 else 0) + supportFibreSize f q xs := by
  by_cases h : f x = q <;> simp [supportFibreSize, h]

private theorem range_indicator_zero : ∀ K n : Nat,
    K ≤ n →
    ((List.range K).map
      (fun q => if n = q then 1 else 0)).sum = 0 := by
  intro K
  induction K with
  | zero =>
      intro n _
      rfl
  | succ K ih =>
      intro n hKn
      have hprev := ih n (by omega)
      have hne : n ≠ K := by omega
      rw [List.range_succ, List.map_append, List.sum_append, hprev]
      simp [hne]

private theorem range_indicator_one : ∀ K n : Nat,
    n < K →
    ((List.range K).map
      (fun q => if n = q then 1 else 0)).sum = 1 := by
  intro K
  induction K with
  | zero =>
      intro n h
      omega
  | succ K ih =>
      intro n hn
      rw [List.range_succ, List.map_append, List.sum_append]
      by_cases hlt : n < K
      · have hprev := ih n hlt
        have hne : n ≠ K := by omega
        rw [hprev]
        simp [hne]
      · have heq : n = K := by omega
        subst n
        have hzero := range_indicator_zero K K (Nat.le_refl K)
        rw [hzero]
        simp

private theorem sum_map_add_nat {α : Type}
    (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      omega

/-- Integer fibres below `K` partition the list exactly. -/
theorem supportFibreSizes_sum {α : Type}
    (K : Nat) (f : α → Nat) :
    ∀ xs : List α,
      (∀ x ∈ xs, f x < K) →
      (supportFibreSizes K f xs).sum = xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp [supportFibreSizes]
  | cons x rest ih =>
      intro hbound
      have hx : f x < K := hbound x List.mem_cons_self
      have hrest : ∀ y ∈ rest, f y < K := by
        intro y hy
        exact hbound y (List.mem_cons_of_mem _ hy)
      have hpoint :
          supportFibreSizes K f (x :: rest) =
            (List.range K).map (fun q =>
              (if f x = q then 1 else 0) +
                supportFibreSize f q rest) := by
        unfold supportFibreSizes
        apply List.map_congr_left
        intro q _
        exact supportFibreSize_cons f q x rest
      rw [hpoint, sum_map_add_nat]
      rw [range_indicator_one K (f x) hx, ih hrest]
      simp

/-- A canonical minimum of one distinguished element and a tail. -/
def fibreMinFrom : Nat → List Nat → Nat
  | x, [] => x
  | x, y :: ys => Nat.min x (fibreMinFrom y ys)

/-- A canonical maximum of one distinguished element and a tail. -/
def fibreMaxFrom : Nat → List Nat → Nat
  | x, [] => x
  | x, y :: ys => Nat.max x (fibreMaxFrom y ys)

theorem fibreMinFrom_mem : ∀ x xs,
    fibreMinFrom x xs ∈ x :: xs := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      simp [fibreMinFrom]
  | cons y ys ih =>
      unfold fibreMinFrom
      by_cases h : x ≤ fibreMinFrom y ys
      · rw [Nat.min_eq_left h]
        exact List.mem_cons_self
      · have hle : fibreMinFrom y ys ≤ x := by omega
        rw [Nat.min_eq_right hle]
        exact List.mem_cons_of_mem _ (ih y)

theorem fibreMaxFrom_mem : ∀ x xs,
    fibreMaxFrom x xs ∈ x :: xs := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      simp [fibreMaxFrom]
  | cons y ys ih =>
      unfold fibreMaxFrom
      by_cases h : x ≤ fibreMaxFrom y ys
      · rw [Nat.max_eq_right h]
        exact List.mem_cons_of_mem _ (ih y)
      · have hle : fibreMaxFrom y ys ≤ x := by omega
        rw [Nat.max_eq_left hle]
        exact List.mem_cons_self

theorem fibreMinFrom_le_mem : ∀ x xs y,
    y ∈ x :: xs → fibreMinFrom x xs ≤ y := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_refl _
      · cases hy
  | cons z zs ih =>
      intro y hy
      unfold fibreMinFrom
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (ih z y hy)

theorem mem_le_fibreMaxFrom : ∀ x xs y,
    y ∈ x :: xs → y ≤ fibreMaxFrom x xs := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_refl _
      · cases hy
  | cons z zs ih =>
      intro y hy
      unfold fibreMaxFrom
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih z y hy) (Nat.le_max_right _ _)

theorem fibreMinFrom_le_fibreMaxFrom (x : Nat) (xs : List Nat) :
    fibreMinFrom x xs ≤ fibreMaxFrom x xs := by
  have hmin := fibreMinFrom_le_mem x xs x List.mem_cons_self
  have hmax := mem_le_fibreMaxFrom x xs x List.mem_cons_self
  exact Nat.le_trans hmin hmax

/-- Filtering a time list preserves duplicate-freeness of any mapped state
list. -/
theorem map_filter_nodup {α β : Type}
    (f : α → β) (p : α → Prop) [DecidablePred p] :
    ∀ {xs : List α},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs hnd
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hx : p x
      · simp only [List.filter_cons_of_pos hx, List.map_cons,
          List.nodup_cons]
        constructor
        · intro hm
          obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
          apply hnd.1
          exact List.mem_map.mpr
            ⟨y, (List.mem_filter.mp hy).1, hfy⟩
        · exact ih hnd.2
      · simpa [List.filter_cons_of_neg hx] using ih hnd.2

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Number of occupied coordinates in a finite slot frame. -/
noncomputable def supportWeight (slots : List Nat) (k : Nat) : Nat :=
  trueCount (supportSnap m e r0 slots k)

theorem supportWeight_lt (slots : List Nat) (k : Nat) :
    supportWeight m e r0 slots k < slots.length + 1 := by
  unfold supportWeight
  have h := trueCount_le_length
    (supportSnap m e r0 slots k)
  rw [supportSnap_length m e r0 slots k] at h
  omega

/-- Equal support weights force equal support vectors along one monotone run. -/
theorem supportSnap_eq_of_weight_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (slots : List Nat) {i j : Nat}
    (hweight : supportWeight m e r0 slots i =
      supportWeight m e r0 slots j) :
    supportSnap m e r0 slots i = supportSnap m e r0 slots j := by
  unfold supportWeight at hweight
  by_cases hij : i ≤ j
  · have hb := support_later_below m e r0 hrun hr0 slots hij
    have heq := eq_of_below_trueCount_eq hb hweight.symm
    exact heq.symm
  · have hji : j ≤ i := by omega
    have hb := support_later_below m e r0 hrun hr0 slots hji
    exact eq_of_below_trueCount_eq hb hweight

private theorem support_map_eq_at_mem {α β : Type}
    {xs : List α} {p q : α → β}
    (h : xs.map p = xs.map q) {x : α} (hx : x ∈ xs) :
    p x = q x := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hh := congrArg List.head? h
        simpa using hh
      · have ht := congrArg List.tail h
        simp only [List.map_cons, List.tail_cons] at ht
        exact ih ht hx

/-- Equal finite support snapshots give occupancy equivalence on every listed
slot. -/
theorem occupied_iff_of_supportSnap_eq_on_slots
    (slots : List Nat) {i j : Nat}
    (hsnap : supportSnap m e r0 slots i =
      supportSnap m e r0 slots j) :
    ∀ s ∈ slots,
      Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  intro s hs
  unfold supportSnap at hsnap
  have hb : decide (Occupied m e r0 i s) =
      decide (Occupied m e r0 j s) :=
    support_map_eq_at_mem hsnap hs
  constructor
  · intro hi
    have hit : decide (Occupied m e r0 i s) = true :=
      decide_eq_true hi
    have hjt : decide (Occupied m e r0 j s) = true := by
      rw [← hb]
      exact hit
    exact of_decide_eq_true hjt
  · intro hj
    have hjt : decide (Occupied m e r0 j s) = true :=
      decide_eq_true hj
    have hit : decide (Occupied m e r0 i s) = true := by
      rw [hb]
      exact hjt
    exact of_decide_eq_true hit

/-- In a complete finite frame, equality of finite support snapshots is equality
of the entire occupied support. -/
theorem completeFrame_global_support_eq
    {globalLo globalHi i j : Nat}
    {cells slots : List Nat}
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hiLo : globalLo ≤ i) (hiHi : i ≤ globalHi)
    (hjLo : globalLo ≤ j) (hjHi : j ≤ globalHi)
    (hsnap : supportSnap m e r0 slots i =
      supportSnap m e r0 slots j) :
    ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s := by
  have hslots := occupied_iff_of_supportSnap_eq_on_slots
    m e r0 slots hsnap
  intro s
  constructor
  · intro hocc
    rcases hocc with hs | hb
    · have hmem := completeFrame_confirmed_slot m e r0 frame
        hiLo hiHi hs
      exact (hslots s hmem).mp (Or.inl hs)
    · have hmem := completeFrame_confirmed_slot m e r0 frame
        hiLo hiHi hb
      have hbar := (hslots (m.bar s) hmem).mp (Or.inl hb)
      exact (occupied_bar m e r0 j s).mp hbar
  · intro hocc
    rcases hocc with hs | hb
    · have hmem := completeFrame_confirmed_slot m e r0 frame
        hjLo hjHi hs
      exact (hslots s hmem).mpr (Or.inl hs)
    · have hmem := completeFrame_confirmed_slot m e r0 frame
        hjLo hjHi hb
      have hbar := (hslots (m.bar s) hmem).mpr (Or.inl hb)
      exact (occupied_bar m e r0 i s).mp hbar

/-- Equal endpoint support makes every step of the interval support-preserving. -/
theorem pairedSupportFixed_of_endpoint_eq
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat} (hlohi : lo ≤ hi)
    (hend : ∀ s,
      Occupied m e r0 lo s ↔ Occupied m e r0 hi s) :
    PairedSupportFixed m e r0 lo hi := by
  intro k hkLo hkLt s
  constructor
  · intro hk
    have hlo : Occupied m e r0 lo s :=
      occupied_later_earlier m e r0 hrun hr0 hkLo hk
    have hhi : Occupied m e r0 hi s := (hend s).mp hlo
    exact occupied_later_earlier m e r0 hrun hr0
      (by omega) hhi
  · intro hk1
    exact occupied_later_earlier m e r0 hrun hr0
      (Nat.le_succ k) hk1

/-- Restrict a complete finite frame to a subinterval. -/
def restrictCompleteFiniteEpochFrame
    {globalLo globalHi lo hi : Nat}
    {cells slots : List Nat}
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hLo : globalLo ≤ lo) (hHi : hi ≤ globalHi) :
    CompleteFiniteEpochFrame m e r0 lo hi cells slots where
  cells_nodup := frame.cells_nodup
  slots_nodup := frame.slots_nodup
  star_closed := frame.star_closed
  bar_closed := frame.bar_closed
  bar_ne := frame.bar_ne
  slot_cell := frame.slot_cell
  selected := fun k hkLo hkHi c hc =>
    frame.selected k (Nat.le_trans hLo hkLo)
      (Nat.le_trans hkHi hHi) c hc
  confirmed_cell := fun k hkLo hkHi x hx =>
    frame.confirmed_cell k (Nat.le_trans hLo hkLo)
      (Nat.le_trans hkHi hHi) x hx

/-- Restrict absence of a four-slot tail to a subinterval. -/
theorem noFourTail_restrict
    {globalLo globalHi lo hi : Nat}
    (hno : StandaloneNoFourTailIn m e r0 globalLo globalHi)
    (hLo : globalLo ≤ lo) (hHi : hi ≤ globalHi) :
    StandaloneNoFourTailIn m e r0 lo hi := by
  intro k hkLo hkHi htail
  exact hno k (Nat.le_trans hLo hkLo)
    (Nat.le_trans hkHi hHi) htail

end Echo
