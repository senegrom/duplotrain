import TrackLobe

/-!
# Supported reflector normal form

This file packages the first-revisit result with the exact path grooves on
which a manufactured reflector depends.  Two such reflectors compose
automatically whenever each local action avoids the other reflector's support.
The only remaining global case is therefore the classical theta intersection:
prove that non-avoidance settles on a simple cycle instead of manufacturing a
third independent component.
-/

namespace GeneralN

inductive LocalAction where
  | stay
  | flip (switch : Nat)

def LocalAction.apply : LocalAction → Tongues → Tongues
  | .stay, u => u
  | .flip k, u => flipAt u k

theorem LocalAction.involutive (action : LocalAction) :
    ∀ u, action.apply (action.apply u) = u := by
  intro u
  cases action with
  | stay => rfl
  | flip k => exact flipAt_flipAt u k

theorem LocalAction.commute (a b : LocalAction) :
    ∀ u, a.apply (b.apply u) = b.apply (a.apply u) := by
  intro u
  cases a with
  | stay => rfl
  | flip ka =>
      cases b with
      | stay => rfl
      | flip kb =>
          by_cases h : ka = kb
          · rw [h]
          · exact flipAt_comm (Ne.symm h)

/-- Every path in `paths` is currently grooved. -/
def PathGrooves (paths : List (List Passage)) (u : Tongues) : Prop :=
  ∀ path ∈ paths, PassagesGrooved u path

theorem pathGrooves_pair {a b : List Passage} {u : Tongues} :
    PathGrooves [a, b] u ↔
      PassagesGrooved u a ∧ PassagesGrooved u b := by
  constructor
  · intro h
    exact ⟨h a (by simp), h b (by simp)⟩
  · intro h path hp
    simp at hp
    rcases hp with rfl | rfl
    · exact h.1
    · exact h.2

theorem passagesGrooved_singleton {p x : Nat} {u : Tongues} :
    PassagesGrooved u [(p, x)] ↔ arrive u x = (p, u) := by
  constructor
  · intro h
    exact h (p, x) List.mem_cons_self
  · intro h passage hp
    simp only [List.mem_singleton] at hp
    simpa [hp] using h

/-- The local action does not touch any switch used by any support path. -/
def LocalAction.Avoids (action : LocalAction)
    (paths : List (List Passage)) : Prop :=
  match action with
  | .stay => True
  | .flip k =>
      ∀ path ∈ paths, ∀ passage ∈ path, passageSwitch passage ≠ k

theorem PathGrooves.after_avoiding_action
    {paths : List (List Passage)} {u : Tongues} {action : LocalAction}
    (hg : PathGrooves paths u) (ha : action.Avoids paths) :
    PathGrooves paths (action.apply u) := by
  cases action with
  | stay => exact hg
  | flip k =>
      intro path hp
      apply grooved_after_flip_other (hg path hp)
      exact ha path hp

/-- A reflector together with the finite list of paths whose grooves certify
its operation and its identity/one-switch action. -/
structure SupportedReflector (w : Wiring) (g e : Nat) where
  travel : Nat
  paths : List (List Passage)
  action : LocalAction
  run : IsReflector w g e travel (PathGrooves paths) action.apply

/-- Two opposite supported reflectors have a genuine period whenever their
actions avoid one another's groove supports. -/
theorem SupportedReflector.paired_period
    {w : Wiring} {gA gB : Nat}
    (A : SupportedReflector w gA gB)
    (B : SupportedReflector w gB gA)
    (hAB : A.action.Avoids B.paths)
    (hBA : B.action.Avoids A.paths)
    (u : Tongues) (hA : PathGrooves A.paths u)
    (hB : PathGrooves B.paths u) :
    stepN w (2 * (A.travel + B.travel)) (gA, u) = some (gA, u) := by
  exact paired_reflectors_period w A.run B.run
    (fun state hs => hs.after_avoiding_action hAB)
    (fun state hs => hs.after_avoiding_action hBA)
    (A.action.commute B.action)
    A.action.involutive B.action.involutive u hA hB

end GeneralN
