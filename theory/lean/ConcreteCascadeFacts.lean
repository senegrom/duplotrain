import GeneralN

/-!
# Concrete cascade mouths and the wiring involution

This is the first constructive part of the wiring-to-echo bridge.  A concrete
`Descent` has a uniquely determined root switch and lands on a stem.  The
root stem and landing stem therefore form a symmetric mouth edge.  These
facts supply the fixed cell involution used by the echo machine.

The raw track pairing itself is totalised by fixing unlinked ports.  Symmetry
of `Wiring.link` makes this total map involutive without any additional
assumption.
-/

namespace GeneralN

/-- Totalise the partial track pairing by fixing an unlinked port. -/
def wireBar (w : Wiring) (p : Nat) : Nat :=
  (w.link p).getD p

theorem wireBar_of_link {w : Wiring} {p q : Nat}
    (h : w.link p = some q) : wireBar w p = q := by
  simp [wireBar, h]

theorem wireBar_of_unlinked {w : Wiring} {p : Nat}
    (h : w.link p = none) : wireBar w p = p := by
  simp [wireBar, h]

/-- The totalised concrete track pairing is an involution. -/
theorem wireBar_invol (w : Wiring) (p : Nat) :
    wireBar w (wireBar w p) = p := by
  cases h : w.link p with
  | none => simp [wireBar, h]
  | some q =>
      have hback : w.link q = some p := w.symm p q h
      simp [wireBar, h, hback]

/-- The switch at the root of a concrete trailing cascade. -/
def descentRoot (p : Nat) (ps : List Nat) : Nat :=
  lastOf p ps / 3

/-- Every concrete descent lands at a stem port. -/
theorem descent_landing_stem {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') : s % 3 = 0 := by
  induction h with
  | last hp hlink hs => exact hs
  | cons hp hlink hp' hrest ih => exact ih

/-- A stem port is exactly three times its switch index. -/
theorem stem_eq_three_mul_div {s : Nat} (hs : s % 3 = 0) :
    3 * (s / 3) = s := by
  omega

/-- Root switches `a` and `b` are mouth-paired when their stem ports are
linked. -/
def MouthPaired (w : Wiring) (a b : Nat) : Prop :=
  w.link (3 * a) = some (3 * b)

theorem mouthPaired_symm {w : Wiring} {a b : Nat}
    (h : MouthPaired w a b) : MouthPaired w b a := by
  unfold MouthPaired at h ⊢
  exact w.symm _ _ h

/-- A root stem has at most one mouth partner. -/
theorem mouthPaired_right_unique {w : Wiring} {a b c : Nat}
    (hab : MouthPaired w a b) (hac : MouthPaired w a c) : b = c := by
  unfold MouthPaired at hab hac
  rw [hab] at hac
  injection hac with h
  omega

/-- A descent's root is mouth-paired with its landing switch. -/
theorem descent_mouthPaired {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    MouthPaired w (descentRoot p ps) (s / 3) := by
  unfold MouthPaired descentRoot
  have hlink := descent_last_link h
  have hs := descent_landing_stem h
  have hstem : 3 * (s / 3) = s := stem_eq_three_mul_div hs
  rwa [hstem]

/-- The concrete mouth partner selected by a root stem.  Non-mouth roots are
fixed; genuine used mouth roots are handled by the conditional lemmas below. -/
def mouthPartner (w : Wiring) (c : Nat) : Nat :=
  match w.link (3 * c) with
  | some s => if s % 3 = 0 then s / 3 else c
  | none => c

theorem mouthPartner_eq_of_paired {w : Wiring} {a b : Nat}
    (h : MouthPaired w a b) : mouthPartner w a = b := by
  unfold MouthPaired at h
  simp [mouthPartner, h]

/-- On a genuine mouth edge, the concrete root-partner map is involutive. -/
theorem mouthPartner_invol_of_paired {w : Wiring} {a b : Nat}
    (h : MouthPaired w a b) :
    mouthPartner w (mouthPartner w a) = a := by
  rw [mouthPartner_eq_of_paired h]
  exact mouthPartner_eq_of_paired (mouthPaired_symm h)

/-- The root of a descent is sent to its landing switch. -/
theorem descent_mouthPartner {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    mouthPartner w (descentRoot p ps) = s / 3 :=
  mouthPartner_eq_of_paired (descent_mouthPaired h)

/-- Two descents with the same concrete root land at the same stem. -/
theorem descent_same_root_same_landing
    {w : Wiring} {t₁ t₂ : Tongues}
    {p₁ p₂ s₁ s₂ : Nat} {ps₁ ps₂ : List Nat}
    {t₁' t₂' : Tongues}
    (h₁ : Descent w t₁ p₁ ps₁ s₁ t₁')
    (h₂ : Descent w t₂ p₂ ps₂ s₂ t₂')
    (hroot : descentRoot p₁ ps₁ = descentRoot p₂ ps₂) :
    s₁ = s₂ := by
  have hlink₁ := descent_last_link h₁
  have hlink₂ := descent_last_link h₂
  have hstem : 3 * descentRoot p₁ ps₁ =
      3 * descentRoot p₂ ps₂ := congrArg (fun c => 3 * c) hroot
  unfold descentRoot at hstem
  rw [hstem, hlink₂] at hlink₁
  injection hlink₁

/-- Two descents landing at the same stem have the same concrete root. -/
theorem descent_same_landing_same_root
    {w : Wiring} {t₁ t₂ : Tongues}
    {p₁ p₂ s : Nat} {ps₁ ps₂ : List Nat}
    {t₁' t₂' : Tongues}
    (h₁ : Descent w t₁ p₁ ps₁ s t₁')
    (h₂ : Descent w t₂ p₂ ps₂ s t₂') :
    descentRoot p₁ ps₁ = descentRoot p₂ ps₂ := by
  have hlast := land_last_unique h₁ h₂
  unfold descentRoot
  omega

/-- If a second descent lands on the first descent's root stem, then its root
is exactly the first descent's landing switch.  This is the concrete
`star (star c) = c` calculation behind the echo compilation. -/
theorem descent_reverse_root
    {w : Wiring} {t₁ t₂ : Tongues}
    {p₁ p₂ s : Nat} {ps₁ ps₂ : List Nat}
    {t₁' t₂' : Tongues}
    (h₁ : Descent w t₁ p₁ ps₁ s t₁')
    (h₂ : Descent w t₂ p₂ ps₂
      (3 * descentRoot p₁ ps₁) t₂') :
    descentRoot p₂ ps₂ = s / 3 := by
  have hforward := descent_last_link h₁
  have hreverse := w.symm _ _ (descent_last_link h₂)
  have hs := descent_landing_stem h₁
  unfold descentRoot at hforward hreverse ⊢
  rw [hforward] at hreverse
  injection hreverse with heq
  omega

/-- Crossing the root stem follows the totalised concrete edge involution to
exactly the landing stem. -/
theorem wireBar_descent_root
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    wireBar w (3 * descentRoot p ps) = s := by
  apply wireBar_of_link
  simpa [descentRoot] using descent_last_link h

end GeneralN
