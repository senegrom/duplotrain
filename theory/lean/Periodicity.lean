import EchoMachine

/-!
# Every run is a rho

The echo machine is deterministic: the next entry is a function of the
current entry and the registers, and a step rewrites exactly one register.
The pair (current entry, registers of the listed cells) is therefore an
autonomously evolving state, and it ranges over a finite space: every
entry and every register value is one of the `slots`.

Pigeonhole: within the first `|slots|^(|cells|+1) + 1` steps two states
coincide, and determinism replays the stretch between them forever.
Every run is a **rho**: a pre-period and a cycle, with explicit bounds
(`run_eventually_periodic`).  On the cycle all registers recur, so by
`recurrence_emission` every productive step on the tail re-emits a token:
the cycle's token population is conserved, unconditionally (`run_rho`).

This is the assembly ground for the cycle-classification arguments
(`lone_write_no_mouth`, `divergence_names_steer`): they now have a
machine-checked eventual cycle to run on.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

private theorem map_congr_forall {f g : Nat → Nat} :
    ∀ l : List Nat, (∀ x ∈ l, f x = g x) → l.map f = l.map g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro h
      simp only [List.map_cons]
      rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem map_eq_forall {f g : Nat → Nat} :
    ∀ l : List Nat, l.map f = l.map g → ∀ x ∈ l, f x = g x := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons a t ih =>
      intro h x hx
      simp only [List.map_cons] at h
      injection h with h1 h2
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact h1
      · exact ih h2 x hxt

/-- The full machine state at time `k`: the current entry together with
the registers of the listed cells.  Determinism makes this evolve
autonomously; finiteness of the slot list makes it pigeonhole. -/
def stateCode (cells : List Nat) (k : Nat) : List Nat :=
  e k :: snap m e r0 cells k

/-- Equal states have equal entries. -/
theorem stateCode_entry_eq (cells : List Nat) {i j : Nat}
    (h : stateCode m e r0 cells i = stateCode m e r0 cells j) :
    e i = e j := by
  have h' : some (e i) = some (e j) := congrArg List.head? h
  exact Option.some.inj h'

/-- Equal states have equal registers on all listed cells. -/
theorem stateCode_reg_eq (cells : List Nat) {i j : Nat}
    (h : stateCode m e r0 cells i = stateCode m e r0 cells j) :
    ∀ C ∈ cells, reg m e r0 i C = reg m e r0 j C := by
  have h' : cells.map (reg m e r0 i) = cells.map (reg m e r0 j) :=
    congrArg List.tail h
  exact map_eq_forall cells h'

/-- **Determinism.**  Equal states step to equal states: the state code
evolves autonomously. -/
theorem state_step (hrun : IsRun m e r0) (cells : List Nat)
    (hcells : ∀ k, m.star (m.cellOf (e k)) ∈ cells) {i j : Nat}
    (h : stateCode m e r0 cells i = stateCode m e r0 cells j) :
    stateCode m e r0 cells (i+1) = stateCode m e r0 cells (j+1) := by
  have he : e i = e j := stateCode_entry_eq m e r0 cells h
  have hsnap := stateCode_reg_eq m e r0 cells h
  have hnext : e (i+1) = e (j+1) := by
    rw [hrun i, hrun j, he]
    exact congrArg m.bar (hsnap _ (hcells j))
  have hmap : cells.map (reg m e r0 (i+1)) = cells.map (reg m e r0 (j+1)) := by
    apply map_congr_forall
    intro C hC
    by_cases hc : m.cellOf (e (j+1)) = C
    · rw [reg_write m e r0 (by rw [hnext]; exact hc), reg_write m e r0 hc,
        hnext]
    · rw [reg_skip m e r0 (by rw [hnext]; exact hc), reg_skip m e r0 hc]
      exact hsnap C hC
  show e (i+1) :: cells.map (reg m e r0 (i+1))
      = e (j+1) :: cells.map (reg m e r0 (j+1))
  rw [hnext, hmap]

/-- A state coincidence replays forever: the whole future repeats. -/
theorem state_replay (hrun : IsRun m e r0) (cells : List Nat)
    (hcells : ∀ k, m.star (m.cellOf (e k)) ∈ cells) {i j : Nat}
    (h : stateCode m e r0 cells i = stateCode m e r0 cells j) :
    ∀ t, stateCode m e r0 cells (i+t) = stateCode m e r0 cells (j+t) := by
  intro t
  induction t with
  | zero => exact h
  | succ n ih => exact state_step m e r0 hrun cells hcells ih

/-- All lists of a given length over a fixed alphabet. -/
def listPow (S : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => S.flatMap (fun x => (listPow S n).map (fun l => x :: l))

private theorem flatMap_const_length (f : Nat → List (List Nat)) (n : Nat)
    (hf : ∀ x, (f x).length = n) :
    ∀ S : List Nat, (S.flatMap f).length = S.length * n := by
  intro S
  induction S with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, hf, ih, List.length_cons,
        Nat.succ_mul]
      omega

theorem listPow_length (S : List Nat) (n : Nat) :
    (listPow S n).length = S.length ^ n := by
  induction n with
  | zero => simp [listPow]
  | succ k ih =>
      have hf : ∀ x, ((listPow S k).map (fun l => x :: l)).length
          = S.length ^ k := by
        intro x
        rw [List.length_map, ih]
      show (S.flatMap (fun x => (listPow S k).map (fun l => x :: l))).length
          = S.length ^ (k+1)
      rw [flatMap_const_length _ _ hf S, Nat.pow_succ]
      exact Nat.mul_comm _ _

theorem mem_listPow (S : List Nat) :
    ∀ (n : Nat) (l : List Nat), l.length = n → (∀ x ∈ l, x ∈ S) →
      l ∈ listPow S n := by
  intro n
  induction n with
  | zero =>
      intro l hl _
      cases l with
      | nil => simp [listPow]
      | cons x t =>
          simp only [List.length_cons] at hl
          omega
  | succ k ih =>
      intro l hl hmem
      cases l with
      | nil =>
          simp only [List.length_nil] at hl
          omega
      | cons x t =>
          have ht : t.length = k := by
            simp only [List.length_cons] at hl
            omega
          show x :: t ∈ S.flatMap (fun y => (listPow S k).map (fun l => y :: l))
          apply List.mem_flatMap.mpr
          refine ⟨x, hmem x List.mem_cons_self, ?_⟩
          exact List.mem_map.mpr
            ⟨t, ih t ht (fun y hy => hmem y (List.mem_cons_of_mem _ hy)), rfl⟩

/-- Pigeonhole for trajectories: a sequence confined to a finite universe
repeats within `|universe| + 1` steps. -/
private theorem exists_repeat_aux :
    ∀ (n : Nat) (F : Nat → List Nat) (U : List (List Nat)),
      (∀ t, t ≤ n → F t ∈ U) → U.length < n →
      ∃ i j, i < j ∧ j ≤ n ∧ F i = F j := by
  intro n
  induction n with
  | zero =>
      intro F U _ hlen
      exact absurd hlen (Nat.not_lt_zero _)
  | succ n ih =>
      intro F U hmem hlen
      by_cases h : ∃ k, 1 ≤ k ∧ k ≤ n + 1 ∧ F k = F 0
      · obtain ⟨k, hk1, hkn, hkF⟩ := h
        exact ⟨0, k, hk1, hkn, hkF.symm⟩
      · have hne : ∀ k, 1 ≤ k → k ≤ n + 1 → F k ≠ F 0 :=
          fun k h1 h2 heq => h ⟨k, h1, h2, heq⟩
        have hmem0 : F 0 ∈ U := hmem 0 (Nat.zero_le _)
        have hmem' : ∀ t, t ≤ n → F (t+1) ∈ U.erase (F 0) := by
          intro t ht
          refine (List.mem_erase_of_ne ?_).mpr (hmem (t+1) (by omega))
          exact hne (t+1) (by omega) (by omega)
        have hpos : 0 < U.length := by
          cases U with
          | nil => cases hmem0
          | cons _ _ => simp
        have hlen' : (U.erase (F 0)).length < n := by
          rw [List.length_erase_of_mem hmem0]
          omega
        obtain ⟨i, k, hik, hkn, hF⟩ :=
          ih (fun t => F (t+1)) (U.erase (F 0)) hmem' hlen'
        exact ⟨i+1, k+1, by omega, by omega, hF⟩

/-- **The pigeonhole.**  Some state recurs within the first
`|slots|^(|cells|+1) + 1` steps.  No run hypothesis is needed: only that
all registers live in `slots`. -/
theorem state_repeat (cells slots : List Nat)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots) :
    ∃ i j, i < j ∧ j ≤ slots.length ^ (cells.length + 1) + 1 ∧
      stateCode m e r0 cells i = stateCode m e r0 cells j := by
  have hmem : ∀ t, stateCode m e r0 cells t
      ∈ listPow slots (cells.length + 1) := by
    intro t
    apply mem_listPow
    · show (e t :: cells.map (reg m e r0 t)).length = cells.length + 1
      rw [List.length_cons, List.length_map]
    · intro x hx
      have hx1 : x ∈ e t :: cells.map (reg m e r0 t) := hx
      rcases List.mem_cons.mp hx1 with rfl | hx'
      · have hw : reg m e r0 t (m.cellOf (e t)) = e t := reg_write m e r0 rfl
        rw [← hw]
        exact hregslots t _
      · obtain ⟨C, _, rfl⟩ := List.mem_map.mp hx'
        exact hregslots t C
  obtain ⟨i, j, hij, hjle, hF⟩ := exists_repeat_aux
    ((listPow slots (cells.length + 1)).length + 1)
    (fun t => stateCode m e r0 cells t)
    (listPow slots (cells.length + 1))
    (fun t _ => hmem t) (Nat.lt_succ_self _)
  refine ⟨i, j, hij, ?_, hF⟩
  rw [listPow_length] at hjle
  exact hjle

/-- A cell outside the write range keeps its initial register forever. -/
theorem reg_foreign (cells : List Nat) (hallcells : ∀ s, m.cellOf s ∈ cells)
    {c : Nat} (hc : c ∉ cells) : ∀ k, reg m e r0 k c = r0 c := by
  intro k
  induction k with
  | zero =>
      show (if m.cellOf (e 0) = c then e 0 else r0 c) = r0 c
      rw [if_neg (fun h : m.cellOf (e 0) = c => hc (h ▸ hallcells (e 0)))]
  | succ n ih =>
      rw [reg_skip m e r0
        (fun h : m.cellOf (e (n+1)) = c => hc (h ▸ hallcells (e (n+1))))]
      exact ih
end Echo
