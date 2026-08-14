import ConcreteFiniteBounds

/-!
# Landed cascades are simple paths

A switch has only one stem exit.  Consequently two finite descents beginning
at branches of the same switch must have the same remaining length: their
first stem exits coincide, and the claim follows recursively.  If one landed
descent revisited a switch, the suffix beginning at that revisit would be a
strictly shorter descent from the same switch to the same landing, a
contradiction.

Thus the switches on every landed cascade are duplicate-free.  In a bounded
`N`-switch wiring its branch word has length at most `N`.
-/

namespace GeneralN

/-- Two finite descents beginning in the same switch have equal branch-word
lengths. -/
theorem descent_path_length_eq_of_same_switch
    {w : Wiring} {t₁ : Tongues} {p₁ s₁ : Nat}
    {ps₁ : List Nat} {t₁' : Tongues}
    (h₁ : Descent w t₁ p₁ ps₁ s₁ t₁') :
    ∀ {t₂ : Tongues} {p₂ s₂ : Nat}
      {ps₂ : List Nat} {t₂' : Tongues},
      Descent w t₂ p₂ ps₂ s₂ t₂' →
      p₁ / 3 = p₂ / 3 →
      (p₁ :: ps₁).length = (p₂ :: ps₂).length := by
  induction h₁ with
  | @last t₁ p₁ s₁ hp₁ hlink₁ hs₁ =>
      intro t₂ p₂ s₂ ps₂ t₂' h₂ hswitch
      cases h₂ with
      | @last t₂ p₂ s₂ hp₂ hlink₂ hs₂ =>
          rfl
      | @cons t₂ p₂ p₂' s₂ ps₂ t₂' hp₂ hlink₂ hp₂' hrest₂ =>
          have hstem : 3 * (p₁ / 3) = 3 * (p₂ / 3) :=
            congrArg (fun c => 3 * c) hswitch
          rw [hstem, hlink₂] at hlink₁
          injection hlink₁ with heq
          have hmods := congrArg (fun x => x % 3) heq
          omega
  | @cons t₁ p₁ p₁' s₁ ps₁ t₁'
      hp₁ hlink₁ hp₁' hrest₁ ih =>
      intro t₂ p₂ s₂ ps₂ t₂' h₂ hswitch
      cases h₂ with
      | @last t₂ p₂ s₂ hp₂ hlink₂ hs₂ =>
          have hstem : 3 * (p₁ / 3) = 3 * (p₂ / 3) :=
            congrArg (fun c => 3 * c) hswitch
          rw [hstem, hlink₂] at hlink₁
          injection hlink₁ with heq
          have hmods := congrArg (fun x => x % 3) heq
          omega
      | @cons t₂ p₂ p₂' s₂ ps₂ t₂'
          hp₂ hlink₂ hp₂' hrest₂ =>
          have hstem : 3 * (p₁ / 3) = 3 * (p₂ / 3) :=
            congrArg (fun c => 3 * c) hswitch
          rw [hstem, hlink₂] at hlink₁
          injection hlink₁ with hnext
          subst p₂'
          have htail := ih hrest₂ rfl
          simp only [List.length_cons] at htail ⊢
          omega

/-- Every branch occurring in a descent begins a suffix descent to the same
landing. -/
theorem descent_suffix
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    ∀ {b : Nat}, b ∈ p :: ps →
      ∃ u : Tongues, ∃ qs : List Nat,
        Descent w u b qs s t' ∧
        (b :: qs).length ≤ (p :: ps).length := by
  induction h with
  | @last t p s hp hlink hs =>
      intro b hb
      rcases List.mem_cons.mp hb with hbp | hb
      · subst b
        exact ⟨t, [], Descent.last hp hlink hs, Nat.le_refl _⟩
      · cases hb
  | @cons t p p' s ps t' hp hlink hp' hrest ih =>
      intro b hb
      rcases List.mem_cons.mp hb with hbp | hb
      · subst b
        exact ⟨t, p' :: ps,
          Descent.cons hp hlink hp' hrest, Nat.le_refl _⟩
      · obtain ⟨u, qs, hsuffix, hlen⟩ := ih hb
        refine ⟨u, qs, hsuffix, ?_⟩
        simp only [List.length_cons] at hlen ⊢
        omega

/-- **Simplicity.**  The switch indices visited by a landed cascade are
pairwise distinct. -/
theorem descent_switch_path_nodup
    {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    ((p :: ps).map (fun b => b / 3)).Nodup := by
  induction h with
  | @last t p s hp hlink hs =>
      simp
  | @cons t p p' s ps t' hp hlink hp' hrest ih =>
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hmem
        have hmem' : p / 3 ∈ (p' :: ps).map (fun b => b / 3) := by
          rw [List.map_cons]
          exact hmem
        obtain ⟨b, hb, hswitch⟩ := List.mem_map.mp hmem'
        obtain ⟨u, qs, hsuffix, hsuffixLen⟩ :=
          descent_suffix hrest hb
        have hfull : Descent w t p (p' :: ps) s t' :=
          Descent.cons hp hlink hp' hrest
        have hsameLen := descent_path_length_eq_of_same_switch
          hfull hsuffix hswitch.symm
        simp only [List.length_cons] at hsameLen hsuffixLen
        omega
      · have ih' := ih
        simp only [List.map_cons, List.nodup_cons] at ih'
        exact ih'

end GeneralN
