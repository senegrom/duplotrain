import FutureEntryBound

/-!
# Bounded multiplicity of consecutive pairs

`FutureEntryBound` collapses every future entry to a fixed alphabet of at most
`2 * #cells + 1` elements.  This file removes the unnecessarily strong
pair-`Nodup` hypothesis from the quadratic counting step.

If every ordered consecutive entry pair occurs at most `r` times in a phase,
then the phase has length at most

    r * (2 * #cells + 1)^2.

Thus the experimentally observed multiplicity ceiling `r = 3` would already
give an unconditional quadratic echo-machine bound.  All counting below is
proved; the remaining dynamical statement is exactly the multiplicity bound.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Every consecutive entry pair occurs at most `r` times among `ks`. -/
def PairMultiplicity (ks : List Nat) (r : Nat) : Prop :=
  ∀ p, (ks.filter (fun k => decide (pairTag e k = p))).length ≤ r

private theorem filter_split_bool (p : Nat → Bool) :
    ∀ l : List Nat,
      (l.filter p).length + (l.filter (fun x => !(p x))).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
      cases hp : p x with
      | true => simp [hp]; omega
      | false => simp [hp]; omega

private theorem filter_filter_length_le (p q : Nat → Bool) :
    ∀ l : List Nat, ((l.filter p).filter q).length ≤ (l.filter q).length := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
      cases hp : p x <;> cases hq : q x <;> simp [hp, hq, ih]

/-- Generic finite-alphabet counting with bounded fibre multiplicity. -/
private theorem bounded_multiplicity_length (f : Nat → List Nat) (r : Nat) :
    ∀ (S ks : List (List Nat)),
      (∀ tag, (ks.filter (fun k => decide (f k = tag))).length ≤ r) →
      (∀ k ∈ ks, f k ∈ S) →
      ks.length ≤ r * S.length := by
  intro S
  induction S with
  | nil =>
      intro ks _ hmem
      cases ks with
      | nil => simp
      | cons k t =>
          have hk := hmem k List.mem_cons_self
          cases hk
  | cons a S ih =>
      intro ks hmult hmem
      let yes := ks.filter (fun k => decide (f k = a))
      let no := ks.filter (fun k => !(decide (f k = a)))
      have hyes : yes.length ≤ r := hmult a
      have hmultNo : ∀ tag,
          (no.filter (fun k => decide (f k = tag))).length ≤ r := by
        intro tag
        have hle := filter_filter_length_le
          (fun k => !(decide (f k = a)))
          (fun k => decide (f k = tag)) ks
        exact Nat.le_trans hle (hmult tag)
      have hmemNo : ∀ k ∈ no, f k ∈ S := by
        intro k hk
        have hkf := List.mem_filter.mp hk
        have hne : f k ≠ a := by
          have hb := hkf.2
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hb
          exact hb
        rcases List.mem_cons.mp (hmem k hkf.1) with ha | hS
        · exact absurd ha hne
        · exact hS
      have hno : no.length ≤ r * S.length := ih no hmultNo hmemNo
      have hsplit : yes.length + no.length = ks.length :=
        filter_split_bool (fun k => decide (f k = a)) ks
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

private theorem pairRect_length (xs ys : List Nat) :
    (xs.flatMap (fun a => ys.map (fun b => [a, b]))).length
      = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons _ t ih =>
      simp [ih, Nat.add_mul, Nat.add_comm]

private theorem pairUniverse_length_local (xs : List Nat) :
    (pairUniverse xs).length = xs.length * xs.length := by
  exact pairRect_length xs xs

/-- Bounded pair multiplicity gives a polynomial bound in the exact future
alphabet, without assuming pairwise distinct pairs. -/
theorem future_pair_multiplicity_bound
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    (K r : Nat) (ks : List Nat) (hks : ∀ k ∈ ks, K ≤ k)
    (hmult : PairMultiplicity e ks r) :
    ks.length ≤ r *
      ((futureEntryAlphabet m e r0 cells slots K).length *
       (futureEntryAlphabet m e r0 cells slots K).length) := by
  let A := futureEntryAlphabet m e r0 cells slots K
  have hsub : ∀ k ∈ ks, pairTag e k ∈ pairUniverse A := by
    intro k hk
    unfold pairTag pairUniverse
    apply List.mem_flatMap.mpr
    refine ⟨e k, future_entry_mem m e r0 hrun hr0 cells slots hcells
      hregslots (hks k hk), ?_⟩
    exact List.mem_map.mpr ⟨e (k+1),
      future_entry_mem m e r0 hrun hr0 cells slots hcells hregslots
        (by have := hks k hk; omega), rfl⟩
  unfold PairMultiplicity at hmult
  have hle := bounded_multiplicity_length (pairTag e) r
    (pairUniverse A) ks hmult hsub
  rw [pairUniverse_length_local] at hle
  exact hle

/-- With at most one token per cell, multiplicity `r` gives the explicit
polynomial bound `r * (2C+1)^2`. -/
theorem future_pair_multiplicity_le_cells_sq
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hslotsnd : slots.Nodup)
    (hallcells : ∀ s, m.cellOf s ∈ cells)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    (K r : Nat) (ks : List Nat) (hks : ∀ k ∈ ks, K ≤ k)
    (hmult : PairMultiplicity e ks r) :
    ks.length ≤ r * ((2 * cells.length + 1) * (2 * cells.length + 1)) := by
  have hp := future_pair_multiplicity_bound m e r0 hrun hr0 cells slots
    hcells hregslots K r ks hks hmult
  have htok := tokens_le_cells m e r0 slots hslotsnd cells hallcells K
  have hA : (futureEntryAlphabet m e r0 cells slots K).length
      ≤ 2 * cells.length + 1 := by
    rw [futureEntryAlphabet_length]
    omega
  have hsquare :
      (futureEntryAlphabet m e r0 cells slots K).length *
          (futureEntryAlphabet m e r0 cells slots K).length
        ≤ (2 * cells.length + 1) * (2 * cells.length + 1) :=
    Nat.mul_le_mul hA hA
  exact Nat.le_trans hp (Nat.mul_le_mul (Nat.le_refl r) hsquare)

/-- The observed three-occurrence ceiling would give a concrete quadratic
bound immediately. -/
theorem future_pair_three_bound
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells slots : List Nat)
    (hslotsnd : slots.Nodup)
    (hallcells : ∀ s, m.cellOf s ∈ cells)
    (hcells : ∀ j, m.star (m.cellOf (e j)) ∈ cells)
    (hregslots : ∀ j c, reg m e r0 j c ∈ slots)
    (K : Nat) (ks : List Nat) (hks : ∀ k ∈ ks, K ≤ k)
    (hmult : PairMultiplicity e ks 3) :
    ks.length ≤ 3 * ((2 * cells.length + 1) * (2 * cells.length + 1)) :=
  future_pair_multiplicity_le_cells_sq m e r0 hrun hr0 cells slots
    hslotsnd hallcells hcells hregslots K 3 ks hks hmult

end Echo
