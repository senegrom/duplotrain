import GrayTailCount

/-!
# Adding the four-state Gray tail to a strict-base prefix bound

The pre-absorption part of one fixed-support epoch has fourth-power size at
most `2^(3C)`.  The absorbed suffix contributes at most four further distinct
snapshots.  This file keeps the calculation integral and proves that the whole
epoch satisfies

    total^4 ≤ 625 * 2^(3C).

The constant `625 = 5^4` is deliberately crude; it has no effect on the
exponential base.
-/

namespace Echo

/-- Multiplication commutes with `fourth`. -/
theorem fourth_mul_eq_public (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  unfold fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Adding at most four elements costs only the universal fourth-power factor
`5^4 = 625`. -/
theorem add_four_fourth_bound
    (S T B : Nat)
    (hT : T ≤ S + 4)
    (hS : fourth S ≤ B)
    (hB : 1 ≤ B) :
    fourth T ≤ 625 * B := by
  cases S with
  | zero =>
      have h4 : fourth T ≤ fourth 4 := fourth_mono hT
      have h256 : fourth 4 = 256 := by decide
      rw [h256] at h4
      omega
  | succ s =>
      have hpos : 1 ≤ Nat.succ s := Nat.succ_le_succ (Nat.zero_le _)
      have hfive : Nat.succ s + 4 ≤ 5 * Nat.succ s := by omega
      have hTS : T ≤ 5 * Nat.succ s := Nat.le_trans hT hfive
      have hfourth := fourth_mono hTS
      rw [fourth_mul_eq_public] at hfourth
      have h625 : fourth 5 = 625 := by decide
      rw [h625] at hfourth
      exact Nat.le_trans hfourth (Nat.mul_le_mul_left 625 hS)

/-- Specialisation to the fixed-support three-quarter prefix estimate. -/
theorem add_gray_tail_to_three_quarter
    (C S T : Nat)
    (hT : T ≤ S + 4)
    (hS : fourth S ≤ 2^(3*C)) :
    fourth T ≤ 625 * 2^(3*C) := by
  exact add_four_fourth_bound S T (2^(3*C)) hT hS
    (Nat.one_le_pow (3*C) 2 (by decide))

/-- A Boolean time split preserves list length. -/
theorem time_filter_split (K : Nat) :
    ∀ ks : List Nat,
      (ks.filter (fun k => decide (k < K))).length +
      (ks.filter (fun k => !(decide (k < K)))).length = ks.length := by
  intro ks
  induction ks with
  | nil => rfl
  | cons k rest ih =>
      by_cases hk : k < K
      · simp [hk]
        omega
      · simp [hk]
        omega

private theorem nodup_map_filter_time {α : Type}
    {f : Nat → α} {p : Nat → Bool} :
    ∀ {ks : List Nat},
      (ks.map f).Nodup → ((ks.filter p).map f).Nodup := by
  intro ks
  induction ks with
  | nil => intro _; simp
  | cons k rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p k with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨j, hj, hfj⟩ := List.mem_map.mp hm
            exact hnd.1 (List.mem_map.mpr
              ⟨j, (List.mem_filter.mp hj).1, hfj⟩)
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp, if_false]
          exact ih hnd.2

/-- **Whole fixed-support epoch bound once a lobed Gray tail begins.**

The prefix count is supplied abstractly as `S`; the suffix count is discharged
by `absorbed_snapshot_count`.  A later module can instantiate `S` with the
component/lobe code count from `fixed_support_before_gray_bound`. -/
theorem prefix_plus_absorbed_tail_bound
    (m : Machine) (e r0 : Nat → Nat)
    (hrun : IsRun m e r0) {a b K : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hAB : m.star (m.cellOf a) = m.cellOf b)
    (hstart : e K = a)
    (hreg : reg m e r0 K (m.cellOf b) = b ∨
      reg m e r0 K (m.cellOf b) = m.bar b)
    (C S : Nat) (cells ks : List Nat)
    (hprefix : (ks.filter (fun k => decide (k < K))).length ≤ S)
    (hS : fourth S ≤ 2^(3*C))
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    fourth ks.length ≤ 625 * 2^(3*C) := by
  let tail := ks.filter (fun k => !(decide (k < K)))
  have htailTimes : ∀ k ∈ tail, K ≤ k := by
    intro k hk
    have hbool := (List.mem_filter.mp hk).2
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hbool
    omega
  have htailNodup : (tail.map (snap m e r0 cells)).Nodup :=
    nodup_map_filter_time hnd
  have htail : tail.length ≤ 4 :=
    absorbed_snapshot_count m e r0 hrun ha hb hAB hstart hreg
      cells tail htailTimes htailNodup
  have hsplit := time_filter_split K ks
  have htotal : ks.length ≤ S + 4 := by
    dsimp [tail] at htail
    omega
  exact add_gray_tail_to_three_quarter C S ks.length htotal hS

end Echo
