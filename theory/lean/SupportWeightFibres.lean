import PairedNoFullReachFreeze
import SupportMove
import BlockSparseBoundCore
import PersistentLobeSeparationStandalone

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
  by_cases h : f x = q <;>
    simp [supportFibreSize, h, Nat.add_comm]

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

private theorem sum_map_zero_nat {α : Type}
    (xs : List α) :
    (xs.map (fun _ => 0)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons _ rest ih => simp [ih]

def fibreMinFrom : Nat → List Nat → Nat
  | x, [] => x
  | x, y :: ys => Nat.min x (fibreMinFrom y ys)

/-- A canonical maximum of one distinguished element and a tail. -/
def fibreMaxFrom : Nat → List Nat → Nat
  | x, [] => x
  | x, y :: ys => Nat.max x (fibreMaxFrom y ys)

theorem fibreMinFrom_le_mem : ∀ x xs y,
    y ∈ x :: xs → fibreMinFrom x xs ≤ y := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · cases hy
  | cons z zs ih =>
      intro y hy
      change x.min (fibreMinFrom z zs) ≤ y
      rcases List.mem_cons.mp hy with hxy | hyTail
      · subst y
        exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _)
          (ih z y hyTail)

theorem mem_le_fibreMaxFrom : ∀ x xs y,
    y ∈ x :: xs → y ≤ fibreMaxFrom x xs := by
  intro x xs
  induction xs generalizing x with
  | nil =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · cases hy
  | cons z zs ih =>
      intro y hy
      change y ≤ x.max (fibreMaxFrom z zs)
      rcases List.mem_cons.mp hy with hxy | hyTail
      · subst y
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih z y hyTail)
          (Nat.le_max_right _ _)
theorem map_filter_nodup {α β : Type}
    (f : α → β) (p : α → Prop) [DecidablePred p] :
    ∀ {xs : List α},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs hnd
  induction xs with
  | nil => simp
  | cons x rest ih =>
      have hnd' := List.nodup_cons.mp hnd
      by_cases hx : p x
      · have hfilter :
            (x :: rest).filter p = x :: rest.filter p := by
          simp [hx]
        rw [hfilter, List.map_cons, List.nodup_cons]
        constructor
        · intro hm
          obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
          apply hnd'.1
          exact List.mem_map.mpr
            ⟨y, (List.mem_filter.mp hy).1, hfy⟩
        · exact ih hnd'.2
      · have hfilter :
            (x :: rest).filter p = rest.filter p := by
          simp [hx]
        rw [hfilter]
        exact ih hnd'.2

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Number of occupied coordinates in a finite slot frame. -/
noncomputable def supportWeight (slots : List Nat) (k : Nat) : Nat :=
  trueCount (supportSnap m e r0 slots k)

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

end Echo
