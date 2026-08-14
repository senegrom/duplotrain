import ReversalFacts

/-!
# Counting monotone support epochs

`SupportBound.lean` proves pointwise that an occupied jump edge can disappear
but can never return.  Here that set-valued monovariant is turned into a
quantitative theorem: along increasing times, a duplicate-free list of support
vectors has length at most `#edges + 1`.

This cleanly separates the global counting problem into

1. at most linearly many support epochs; and
2. the number of register states possible inside one fixed support.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- `lo` is obtained from `hi` only by changing some `true` entries to
`false`; no coordinate can turn on. -/
def BoolBelow : List Bool → List Bool → Prop
  | [], [] => True
  | a :: as, b :: bs => (a = true → b = true) ∧ BoolBelow as bs
  | _, _ => False

/-- Number of occupied coordinates. -/
def trueCount : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + trueCount bs

theorem trueCount_le_of_below {lo hi : List Bool}
    (h : BoolBelow lo hi) : trueCount lo ≤ trueCount hi := by
  induction lo generalizing hi with
  | nil =>
      cases hi with
      | nil => exact Nat.le_refl _
      | cons _ _ => cases h
  | cons a as ih =>
      cases hi with
      | nil => cases h
      | cons b bs =>
          have hab : a = true → b = true := (show
            (a = true → b = true) ∧ BoolBelow as bs from h).1
          have htail : BoolBelow as bs := (show
            (a = true → b = true) ∧ BoolBelow as bs from h).2
          have ht := ih htail
          cases a <;> cases b
          · simpa [trueCount] using ht
          · simp [trueCount] at ⊢
            omega
          · have hf : (false : Bool) = true := hab rfl
            cases hf
          · simpa [trueCount] using Nat.add_le_add_left ht 1

theorem eq_of_below_trueCount_eq {lo hi : List Bool}
    (h : BoolBelow lo hi)
    (hc : trueCount lo = trueCount hi) : lo = hi := by
  induction lo generalizing hi with
  | nil =>
      cases hi with
      | nil => rfl
      | cons _ _ => cases h
  | cons a as ih =>
      cases hi with
      | nil => cases h
      | cons b bs =>
          have hab : a = true → b = true := (show
            (a = true → b = true) ∧ BoolBelow as bs from h).1
          have htail : BoolBelow as bs := (show
            (a = true → b = true) ∧ BoolBelow as bs from h).2
          cases a <;> cases b
          · have htc : trueCount as = trueCount bs := by
              simpa [trueCount] using hc
            have he := ih htail htc
            simp [he]
          · have hle := trueCount_le_of_below htail
            simp [trueCount] at hc
            omega
          · have hf : (false : Bool) = true := hab rfl
            cases hf
          · have htc : trueCount as = trueCount bs := by
              simpa [trueCount] using hc
            have he := ih htail htc
            simp [he]

theorem trueCount_lt_of_below_ne {lo hi : List Bool}
    (h : BoolBelow lo hi) (hne : lo ≠ hi) :
    trueCount lo < trueCount hi := by
  have hle := trueCount_le_of_below h
  have hneq : trueCount lo ≠ trueCount hi := by
    intro heq
    exact hne (eq_of_below_trueCount_eq h heq)
  omega

theorem trueCount_le_length : ∀ xs : List Bool,
    trueCount xs ≤ xs.length := by
  intro xs
  induction xs with
  | nil => exact Nat.le_refl _
  | cons b bs ih =>
      cases b <;> simp [trueCount] <;> omega

/-- Consecutive vectors form a descending support chain. -/
def Descending : List (List Bool) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => BoolBelow y x ∧ Descending (y :: rest)

private theorem descending_length_le_head :
    ∀ (x : List Bool) (rest : List (List Bool)),
      (x :: rest).Nodup → Descending (x :: rest) →
      (x :: rest).length ≤ trueCount x + 1 := by
  intro x rest
  induction rest generalizing x with
  | nil =>
      intro _ _
      simp
  | cons y ys ih =>
      intro hnd hdesc
      have hndx := List.nodup_cons.mp hnd
      have hd : BoolBelow y x ∧ Descending (y :: ys) := by
        simpa only [Descending] using hdesc
      have hyx : y ≠ x := by
        intro h
        apply hndx.1
        rw [← h]
        exact List.mem_cons_self
      have hlt := trueCount_lt_of_below_ne hd.1 hyx
      have htail := ih y hndx.2 hd.2
      simp only [List.length_cons] at htail ⊢
      omega

noncomputable def supportSnap (edges : List Nat) (k : Nat) : List Bool :=
  edges.map (fun s => decide (Occupied m e r0 k s))

theorem supportSnap_length (edges : List Nat) (k : Nat) :
    (supportSnap m e r0 edges k).length = edges.length := by
  simp [supportSnap]

private theorem below_map {α : Type} (xs : List α)
    (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    BoolBelow (xs.map p) (xs.map q) := by
  induction xs with
  | nil => exact True.intro
  | cons x rest ih =>
      simp only [List.map_cons, BoolBelow]
      exact ⟨h x List.mem_cons_self,
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

/-- Occupancy at a later time implies occupancy at every earlier time. -/
theorem occupied_later_earlier
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j s : Nat} (hij : i ≤ j) :
    Occupied m e r0 j s → Occupied m e r0 i s := by
  intro hj
  by_cases hi : Occupied m e r0 i s
  · exact hi
  · exact absurd hj (empty_forever m e r0 hrun hr0 hij hi)

/-- Support vectors decrease along time. -/
theorem support_later_below
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (edges : List Nat) {i j : Nat} (hij : i ≤ j) :
    BoolBelow (supportSnap m e r0 edges j)
      (supportSnap m e r0 edges i) := by
  unfold supportSnap
  apply below_map
  intro s _ hs
  have hj : Occupied m e r0 j s := of_decide_eq_true hs
  exact decide_eq_true (occupied_later_earlier m e r0 hrun hr0 hij hj)

/-- Strictly increasing list of times. -/
def Increasing : List Nat → Prop
  | [] => True
  | [_] => True
  | i :: j :: rest => i < j ∧ Increasing (j :: rest)
end Echo
