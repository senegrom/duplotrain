import DescentRouteCatalogue
import ConcreteMachine

/-!
# Coding concrete tree roots as paired echo cells

For a proper mouth edge between distinct roots `a` and `b`, encode the smaller
root by `2*min(a,b)` and the larger by the adjacent odd number.  The global
echo involution `mateNat` then agrees exactly with the physical mouth pairing.

The code is injective on proper mouth roots because distinct stem edges form a
matching.  All branch ports in one canonical cascade have the same root code.
-/

namespace GeneralN

/-- A root whose stem is paired with a distinct root stem. -/
def ProperMouthRoot (w : Wiring) (r : Nat) : Prop :=
  ∃ s, MouthPaired w r s ∧ r ≠ s

/-- Canonical paired-cell code of a concrete root. -/
def rootCode (w : Wiring) (r : Nat) : Nat :=
  let s := mouthPartner w r
  if r < s then 2 * r else 2 * s + 1

/-- `mateNat` swaps the even and odd members of every adjacent pair. -/
theorem mateNat_two_mul : ∀ n,
    mateNat (2 * n) = 2 * n + 1
  | 0 => rfl
  | n + 1 => by
      have ih := mateNat_two_mul n
      change mateNat (2 * n + 2) = 2 * n + 3
      simp [mateNat, ih]

theorem mateNat_two_mul_add_one : ∀ n,
    mateNat (2 * n + 1) = 2 * n
  | 0 => rfl
  | n + 1 => by
      have ih := mateNat_two_mul_add_one n
      change mateNat (2 * n + 3) = 2 * n + 2
      simp [mateNat, ih]

/-- Root code on the smaller endpoint of a proper mouth edge. -/
theorem rootCode_left_of_mouth
    {w : Wiring} {a b : Nat}
    (h : MouthPaired w a b) (hab : a < b) :
    rootCode w a = 2 * a := by
  unfold rootCode
  rw [mouthPartner_eq_of_paired h]
  simp [hab]

/-- Root code on the larger endpoint of a proper mouth edge. -/
theorem rootCode_right_of_mouth
    {w : Wiring} {a b : Nat}
    (h : MouthPaired w a b) (hba : b < a) :
    rootCode w a = 2 * b + 1 := by
  unfold rootCode
  rw [mouthPartner_eq_of_paired h]
  rw [if_neg (by omega : ¬ a < b)]

/-- The root code intertwines the physical mouth pairing and `mateNat`. -/
theorem rootCode_mouth_partner
    {w : Wiring} {a b : Nat}
    (h : MouthPaired w a b) (hne : a ≠ b) :
    mateNat (rootCode w a) = rootCode w b := by
  have hsymm := mouthPaired_symm h
  by_cases hab : a < b
  · have hba : ¬ b < a := by omega
    rw [rootCode_left_of_mouth h hab,
      rootCode_right_of_mouth hsymm hab,
      mateNat_two_mul]
  · have hba : b < a := by omega
    rw [rootCode_right_of_mouth h hba,
      rootCode_left_of_mouth hsymm hba,
      mateNat_two_mul_add_one]

theorem rootCode_injective_on_proper
    {w : Wiring} {a b : Nat}
    (ha : ProperMouthRoot w a)
    (hb : ProperMouthRoot w b)
    (hcode : rootCode w a = rootCode w b) : a = b := by
  obtain ⟨sa, hasa, hane⟩ := ha
  obtain ⟨sb, hasb, hbne⟩ := hb
  have hpa : mouthPartner w a = sa :=
    mouthPartner_eq_of_paired hasa
  have hpb : mouthPartner w b = sb :=
    mouthPartner_eq_of_paired hasb
  by_cases hal : a < sa
  · have hca : rootCode w a = 2 * a :=
      rootCode_left_of_mouth hasa hal
    by_cases hbl : b < sb
    · have hcb : rootCode w b = 2 * b :=
        rootCode_left_of_mouth hasb hbl
      rw [hca, hcb] at hcode
      omega
    · have hsbb : sb < b := by omega
      have hcb : rootCode w b = 2 * sb + 1 :=
        rootCode_right_of_mouth hasb hsbb
      rw [hca, hcb] at hcode
      omega
  · have hsaa : sa < a := by omega
    have hca : rootCode w a = 2 * sa + 1 :=
      rootCode_right_of_mouth hasa hsaa
    by_cases hbl : b < sb
    · have hcb : rootCode w b = 2 * b :=
        rootCode_left_of_mouth hasb hbl
      rw [hca, hcb] at hcode
      omega
    · have hsbb : sb < b := by omega
      have hcb : rootCode w b = 2 * sb + 1 :=
        rootCode_right_of_mouth hasb hsbb
      rw [hca, hcb] at hcode
      have hs : sa = sb := by omega
      have hsaBack : mouthPartner w sa = a := by
        have hi := mouthPartner_invol_of_paired hasa
        rw [hpa] at hi
        exact hi
      have hsbBack : mouthPartner w sb = b := by
        have hi := mouthPartner_invol_of_paired hasb
        rw [hpb] at hi
        exact hi
      rw [hs, hsbBack] at hsaBack
      exact hsaBack.symm

/-- Every branch in one realised cascade has the same canonical root. -/
theorem entryRoot_eq_of_mem_entryAction
    {w : Wiring} {p b : Nat}
    (hp : IsDescentEntry w p)
    (hb : b ∈ entryAction w p) :
    entryRoot w b = entryRoot w p := by
  rcases hp with ⟨t, ps, s, t', hd⟩
  have haction := entryAction_eq_of_descent hd
  rw [haction] at hb
  obtain ⟨u, qs, hsuffix, hlen⟩ := descent_suffix hd hb
  rw [entryRoot_eq_of_descent hsuffix,
    entryRoot_eq_of_descent hd]
  exact descent_same_landing_same_root hsuffix hd

theorem rootCode_eq_of_mem_entryAction
    {w : Wiring} {p b : Nat}
    (hp : IsDescentEntry w p)
    (hb : b ∈ entryAction w p) :
    rootCode w (entryRoot w b) = rootCode w (entryRoot w p) := by
  rw [entryRoot_eq_of_mem_entryAction hp hb]

end GeneralN
