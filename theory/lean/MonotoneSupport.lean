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

theorem boolBelow_length {lo hi : List Bool}
    (h : BoolBelow lo hi) : lo.length = hi.length := by
  induction lo generalizing hi with
  | nil =>
      cases hi with
      | nil => rfl
      | cons b bs => cases h
  | cons a as ih =>
      cases hi with
      | nil => cases h
      | cons b bs =>
          simp only [BoolBelow] at h
          simp only [List.length_cons]
          exact congrArg Nat.succ (ih h.2)

theorem trueCount_le_of_below {lo hi : List Bool}
    (h : BoolBelow lo hi) : trueCount lo ≤ trueCount hi := by
  induction lo generalizing hi with
  | nil =>
      cases hi with
      | nil => exact Nat.le_refl _
      | cons b bs => cases h
  | cons a as ih =>
      cases hi with
      | nil => cases h
      | cons b bs =>
          simp only [BoolBelow] at h
          cases a <;> cases b <;>
            simp only [trueCount, Bool.false_eq_true, Bool.true_eq_true,
              if_false, if_true] at h ⊢
          · exact ih h.2
          · exact Nat.le_trans (ih h.2) (Nat.le_add_left _ _)
          · exact absurd rfl (h.1)
          · exact Nat.add_le_add_left (ih h.2) 1

theorem eq_of_below_trueCount_eq {lo hi : List Bool}
    (h : BoolBelow lo hi)
    (hc : trueCount lo = trueCount hi) : lo = hi := by
  induction lo generalizing hi with
  | nil =>
      cases hi with
      | nil => rfl
      | cons b bs => cases h
  | cons a as ih =>
      cases hi with
      | nil => cases h
      | cons b bs =>
          simp only [BoolBelow] at h
          cases a <;> cases b
          · simp only [trueCount, if_false, Nat.zero_add] at hc
            rw [ih h.2 hc]
          · have hle := trueCount_le_of_below h.2
            simp only [trueCount, if_false, if_true, Nat.zero_add] at hc
            omega
          · exact absurd rfl h.1
          · simp only [trueCount, if_true, Nat.add_left_cancel_iff] at hc
            rw [ih h.2 hc]

theorem trueCount_lt_of_below_ne {lo hi : List Bool}
    (h : BoolBelow lo hi) (hne : lo ≠ hi) :
    trueCount lo < trueCount hi := by
  have hle := trueCount_le_of_below h
  have hneq : trueCount lo ≠ trueCount hi := by
    intro heq
    exact hne (eq_of_below_trueCount_eq h heq)
  omega

/-- Consecutive vectors form a descending support chain. -/
def Descending : List (List Bool) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => BoolBelow y x ∧ Descending (y :: rest)

private theorem descending_length_le_head :
    ∀ {vs : List (List Bool)}, vs.Nodup → Descending vs →
      ∀ {x rest}, vs = x :: rest → vs.length ≤ trueCount x + 1 := by
  intro vs hnd hdesc x rest heq
  subst vs
  induction rest generalizing x with
  | nil => simp
  | cons y ys ih =>
      simp only [List.nodup_cons] at hnd
      simp only [Descending] at hdesc
      have hxy : x ≠ y := by
        intro h
        exact hnd.1 (h ▸ List.mem_cons_self)
      have hlt := trueCount_lt_of_below_ne hdesc.1 (fun h => hxy h.symm)
      have htail := ih hnd.2 hdesc.2
      simp only [List.length_cons]
      omega

/-- A duplicate-free descending chain of length-`N` Boolean vectors has at
most `N+1` members. -/
theorem descending_chain_bound (N : Nat) (vs : List (List Bool))
    (hlen : ∀ v ∈ vs, v.length = N)
    (hnd : vs.Nodup) (hdesc : Descending vs) :
    vs.length ≤ N + 1 := by
  cases vs with
  | nil => exact Nat.zero_le _
  | cons x rest =>
      have hhead := descending_length_le_head hnd hdesc rfl
      have hcount : trueCount x ≤ x.length := by
        induction x with
        | nil => exact Nat.le_refl _
        | cons b bs ih =>
            cases b <;> simp [trueCount] <;> omega
      have hxlen := hlen x List.mem_cons_self
      omega

/-- Support vector on a chosen list of jump-edge representatives.  It is safe
if the list contains both endpoints too; that only duplicates coordinates and
weakens the numerical bound. -/
def supportSnap (edges : List Nat) (k : Nat) : List Bool :=
  edges.map (fun s => decide (Occupied m e r0 k s))

theorem supportSnap_length (edges : List Nat) (k : Nat) :
    (supportSnap m e r0 edges k).length = edges.length := by
  simp [supportSnap]

private theorem below_map {α : Type} (xs : List α)
    (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = true → q x = true) :
    BoolBelow (xs.map p) (xs.map q) := by
  induction xs with
  | nil => trivial
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

private theorem support_descending
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (edges : List Nat) :
    ∀ ks, Increasing ks →
      Descending (ks.map (supportSnap m e r0 edges)) := by
  intro ks hinc
  cases ks with
  | nil => trivial
  | cons i rest =>
      cases rest with
      | nil => trivial
      | cons j tail =>
          simp only [Increasing] at hinc
          simp only [List.map_cons, Descending]
          exact ⟨support_later_below m e r0 hrun hr0 edges
              (Nat.le_of_lt hinc.1),
            support_descending m e r0 hrun hr0 edges (j :: tail) hinc.2⟩

/-- **Linear number of support epochs.**  Along increasing times, if the
support vectors are pairwise distinct, there are at most `#edges + 1` of
them. -/
theorem support_epoch_bound
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (edges ks : List Nat)
    (hinc : Increasing ks)
    (hnd : (ks.map (supportSnap m e r0 edges)).Nodup) :
    ks.length ≤ edges.length + 1 := by
  have h := descending_chain_bound edges.length
    (ks.map (supportSnap m e r0 edges))
    (fun v hv => by
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hv
      exact supportSnap_length m e r0 edges k)
    hnd (support_descending m e r0 hrun hr0 edges ks hinc)
  simpa only [List.length_map] using h

end Echo
