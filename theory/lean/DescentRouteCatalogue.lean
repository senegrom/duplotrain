import DescentSimplicity
import OverwriteDynamics

/-!
# Canonical concrete cascade routes

Trailing continuation depends only on the wiring.  Two finite `Descent`
witnesses beginning at the same branch port therefore have exactly the same
branch word and landing stem, even when their initial tongue vectors differ.

This permits a noncomputable but canonical catalogue:

* `entryAction w p` is the fixed branch-pin word of realised entry `p`;
* `entryRoot w p` is its root switch; and
* `entryLanding w p` is its landing stem.

All definitions are proof-independent by route uniqueness.
-/

namespace GeneralN

/-- Route and landing uniqueness for one concrete cascade entry. -/
theorem descent_route_unique
    {w : Wiring} {t₁ t₂ : Tongues} {p s₁ s₂ : Nat}
    {ps₁ ps₂ : List Nat} {t₁' t₂' : Tongues}
    (h₁ : Descent w t₁ p ps₁ s₁ t₁')
    (h₂ : Descent w t₂ p ps₂ s₂ t₂') :
    ps₁ = ps₂ ∧ s₁ = s₂ := by
  induction h₁ generalizing t₂ ps₂ s₂ t₂' with
  | @last t₁ p s₁ hp₁ hlink₁ hs₁ =>
      cases h₂ with
      | @last t₂ p s₂ hp₂ hlink₂ hs₂ =>
          rw [hlink₂] at hlink₁
          injection hlink₁ with hs
          exact ⟨rfl, hs.symm⟩
      | @cons t₂ p p₂' s₂ ps₂ t₂'
          hp₂ hlink₂ hp₂' hrest₂ =>
          rw [hlink₂] at hlink₁
          injection hlink₁ with heq
          have hmods := congrArg (fun x => x % 3) heq
          omega
  | @cons t₁ p p₁' s₁ ps₁ t₁'
      hp₁ hlink₁ hp₁' hrest₁ ih =>
      cases h₂ with
      | @last t₂ p s₂ hp₂ hlink₂ hs₂ =>
          rw [hlink₂] at hlink₁
          injection hlink₁ with heq
          have hmods := congrArg (fun x => x % 3) heq
          omega
      | @cons t₂ p p₂' s₂ ps₂ t₂'
          hp₂ hlink₂ hp₂' hrest₂ =>
          rw [hlink₂] at hlink₁
          injection hlink₁ with hnext
          subst p₂'
          obtain ⟨hps, hs⟩ := ih hrest₂
          exact ⟨congrArg (List.cons p₁') hps, hs⟩

/-- A packaged finite descent beginning at `p`. -/
structure DescentWitness (w : Wiring) (p : Nat) where
  initial : Tongues
  tail : List Nat
  landing : Nat
  final : Tongues
  descent : Descent w initial p tail landing final

/-- Realised entries have packaged descent witnesses. -/
theorem descentWitness_nonempty
    {w : Wiring} {p : Nat} (h : IsDescentEntry w p) :
    Nonempty (DescentWitness w p) := by
  rcases h with ⟨t, ps, s, t', hd⟩
  exact ⟨⟨t, ps, s, t', hd⟩⟩

/-- Choose one witness for a realised entry. -/
noncomputable def chosenDescentWitness
    (w : Wiring) (p : Nat) (h : IsDescentEntry w p) :
    DescentWitness w p :=
  Classical.choice (descentWitness_nonempty h)

open Classical in
/-- Canonical finite branch-pin word of a realised entry; unrealised ports
receive the empty word. -/
noncomputable def entryAction (w : Wiring) (p : Nat) : List Nat :=
  if h : IsDescentEntry w p then
    p :: (chosenDescentWitness w p h).tail
  else []

open Classical in
/-- Canonical root switch of a realised entry. -/
noncomputable def entryRoot (w : Wiring) (p : Nat) : Nat :=
  if h : IsDescentEntry w p then
    descentRoot p (chosenDescentWitness w p h).tail
  else 0

open Classical in
/-- Canonical landing stem of a realised entry. -/
noncomputable def entryLanding (w : Wiring) (p : Nat) : Nat :=
  if h : IsDescentEntry w p then
    (chosenDescentWitness w p h).landing
  else 0

/-- The chosen route equals every concrete descent route from the entry. -/
theorem entryAction_eq_of_descent
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    entryAction w p = p :: ps := by
  unfold entryAction
  split <;> rename_i hex
  · have hchosen := (chosenDescentWitness w p hex).descent
    have hroute := (descent_route_unique hchosen h).1
    rw [hroute]
  · exact False.elim (hex ⟨t, ps, s, t', h⟩)

/-- The chosen root equals the root of every concrete descent. -/
theorem entryRoot_eq_of_descent
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    entryRoot w p = descentRoot p ps := by
  unfold entryRoot
  split <;> rename_i hex
  · have hchosen := (chosenDescentWitness w p hex).descent
    have hroute := (descent_route_unique hchosen h).1
    rw [hroute]
  · exact False.elim (hex ⟨t, ps, s, t', h⟩)

/-- The chosen landing equals every concrete landing from the entry. -/
theorem entryLanding_eq_of_descent
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    entryLanding w p = s := by
  unfold entryLanding
  split <;> rename_i hex
  · have hchosen := (chosenDescentWitness w p hex).descent
    exact (descent_route_unique hchosen h).2
  · exact False.elim (hex ⟨t, ps, s, t', h⟩)

/-- The canonical root and landing are mouth-paired. -/
theorem entryRoot_mouthPaired
    {w : Wiring} {p : Nat} (h : IsDescentEntry w p) :
    MouthPaired w (entryRoot w p) (entryLanding w p / 3) := by
  rcases h with ⟨t, ps, s, t', hd⟩
  rw [entryRoot_eq_of_descent hd, entryLanding_eq_of_descent hd]
  exact descent_mouthPaired hd

/-- The canonical action word is exactly the tongue transformation of every
concrete descent. -/
theorem descent_result_eq_entryAction
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    t' = pinList (entryAction w p) t := by
  rw [entryAction_eq_of_descent h]
  exact descent_result_eq_pinList h

/-- Canonical actions of bounded realised entries have length at most `N`. -/
theorem entryAction_length_le
    {w : Wiring} {N p : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3*N ∧ b < 3*N)
    (hp : IsDescentEntry w p) :
    (entryAction w p).length ≤ N := by
  rcases hp with ⟨t, ps, s, t', hd⟩
  rw [entryAction_eq_of_descent hd]
  exact descent_path_length_le hN hd

end GeneralN
