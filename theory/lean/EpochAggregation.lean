import LobeAbsorption

/-!
# Aggregating fixed-support bounds

Occupied support changes only linearly many times.  This file proves the
arithmetic needed to combine a fourth-power bound for each fixed-support epoch
without taking roots.

If there are at most `C+1` epochs and each epoch contains `b` states with

    b^4 ≤ B,

then the total number `T` satisfies

    T^4 ≤ (C+1)^4 * B.

Taking `B = 2^(3*C)` preserves a strict-base exponential bound up to the
polynomial prefactor.
-/

namespace Echo

/-- Total number of entries across a list of epochs. -/
def epochTotal {α : Type} : List (List α) → Nat
  | [] => 0
  | xs :: rest => xs.length + epochTotal rest

/-- Maximum epoch length. -/
def epochMax {α : Type} : List (List α) → Nat
  | [] => 0
  | xs :: rest => max xs.length (epochMax rest)

theorem epoch_length_le_max {α : Type} :
    ∀ {epochs : List (List α)} {xs : List α},
      xs ∈ epochs → xs.length ≤ epochMax epochs := by
  intro epochs
  induction epochs with
  | nil => intro xs h; cases h
  | cons y rest ih =>
      intro xs h
      simp only [List.mem_cons] at h
      unfold epochMax
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem epochTotal_le_count_mul_max {α : Type} :
    ∀ epochs : List (List α),
      epochTotal epochs ≤ epochs.length * epochMax epochs := by
  intro epochs
  induction epochs with
  | nil => simp [epochTotal, epochMax]
  | cons xs rest ih =>
      unfold epochTotal epochMax
      simp only [List.length_cons]
      have hx : xs.length ≤ max xs.length (epochMax rest) :=
        Nat.le_max_left _ _
      have hr : epochMax rest ≤ max xs.length (epochMax rest) :=
        Nat.le_max_right _ _
      calc
        xs.length + epochTotal rest
            ≤ xs.length + rest.length * epochMax rest :=
              Nat.add_le_add_left ih _
        _ ≤ max xs.length (epochMax rest) +
              rest.length * max xs.length (epochMax rest) := by
              exact Nat.add_le_add hx
                (Nat.mul_le_mul_left rest.length hr)
        _ = (rest.length + 1) *
              max xs.length (epochMax rest) := by
              rw [Nat.succ_mul]
              exact Nat.add_comm _ _

private theorem epochMax_is_zero_or_member {α : Type} :
    ∀ epochs : List (List α),
      epochMax epochs = 0 ∨
      ∃ xs ∈ epochs, xs.length = epochMax epochs := by
  intro epochs
  induction epochs with
  | nil => exact Or.inl rfl
  | cons xs rest ih =>
      unfold epochMax
      by_cases h : xs.length ≥ epochMax rest
      · have hm : max xs.length (epochMax rest) = xs.length :=
          Nat.max_eq_left h
        right
        exact ⟨xs, List.mem_cons_self, hm.symm⟩
      · have hlt : xs.length < epochMax rest := by omega
        have hm : max xs.length (epochMax rest) = epochMax rest :=
          Nat.max_eq_right (Nat.le_of_lt hlt)
        rcases ih with hz | ⟨ys, hys, hy⟩
        · rw [hz] at hlt
          omega
        · right
          exact ⟨ys, List.mem_cons_of_mem _ hys, hy.trans hm.symm⟩

/-- A common fourth-power bound for all epochs also bounds the maximum epoch. -/
theorem epochMax_fourth_le {α : Type}
    (epochs : List (List α)) (B : Nat)
    (hB : ∀ xs ∈ epochs, fourth xs.length ≤ B) :
    fourth (epochMax epochs) ≤ B := by
  rcases epochMax_is_zero_or_member epochs with hz | ⟨xs, hxs, hx⟩
  · rw [hz]
    exact Nat.zero_le _
  · rw [← hx]
    exact hB xs hxs

private theorem fourth_mul_eq (x y : Nat) :
    fourth (x*y) = fourth x * fourth y := by
  unfold fourth
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- **Epoch aggregation theorem.** -/
theorem aggregate_epoch_fourth_bound {α : Type}
    (C B : Nat) (epochs : List (List α))
    (hepochs : epochs.length ≤ C+1)
    (hB : ∀ xs ∈ epochs, fourth xs.length ≤ B) :
    fourth (epochTotal epochs) ≤ fourth (C+1) * B := by
  have htotal := epochTotal_le_count_mul_max epochs
  have hcount : epochs.length * epochMax epochs ≤
      (C+1) * epochMax epochs :=
    Nat.mul_le_mul_right _ hepochs
  have hlen : epochTotal epochs ≤ (C+1) * epochMax epochs :=
    Nat.le_trans htotal hcount
  have hfourth := fourth_mono hlen
  rw [fourth_mul_eq] at hfourth
  exact Nat.le_trans hfourth
    (Nat.mul_le_mul_left (fourth (C+1))
      (epochMax_fourth_le epochs B hB))

/-- Specialisation to the three-quarter per-epoch exponent. -/
theorem aggregate_three_quarter_epochs {α : Type}
    (C : Nat) (epochs : List (List α))
    (hepochs : epochs.length ≤ C+1)
    (hB : ∀ xs ∈ epochs, fourth xs.length ≤ 2^(3*C)) :
    fourth (epochTotal epochs) ≤ fourth (C+1) * 2^(3*C) := by
  exact aggregate_epoch_fourth_bound C (2^(3*C)) epochs hepochs hB

end Echo
