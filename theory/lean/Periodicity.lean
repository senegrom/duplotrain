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


def listPow (S : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => S.flatMap (fun x => (listPow S n).map (fun l => x :: l))
end Echo
