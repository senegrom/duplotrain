import StarLobeDichotomy

/-!
# Fixed-support strict-base bound, reduced to the projected code

This file joins the dynamical lobe dichotomy to the finite coding theorem.
For a fixed support epoch, suppose the exact register snapshots inject into

* a projected pseudoforest code `p < P`, and
* one Boolean coordinate for every persistent active lobe cell.

If the projected capacity satisfies `P² ≤ 2^(C-A)`, then either the epoch code
has fourth power at most `2^(3C)`, or a star-paired lobe pair has already
forced the four-slot Gray tail.

Thus the only remaining structural work for the strict-base bound is the
construction of the projected pseudoforest code and its capacity estimate;
the lobe side is now unconditional.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Encoded fixed-epoch dichotomy.** -/
theorem persistent_epoch_encoded_or_absorb
    (hrun : IsRun m e r0)
    (lo hi : Nat) (active cells : List Nat) (P : Nat)
    (codes : List (Nat × List Bool))
    (hactive : active.Nodup)
    (hcells : cells.Nodup)
    (hcover : ∀ c ∈ active,
      c ∈ cells ∧ m.star c ∈ cells)
    (hwit : ∀ c ∈ active,
      PersistentLobeWitness m e r0 lo hi c)
    (hcodes : codes.Nodup)
    (hcodeP : ∀ z ∈ codes, z.1 < P)
    (hcodeA : ∀ z ∈ codes, z.2.length = active.length)
    (hcap : P * P ≤ 2 ^ (cells.length - active.length)) :
    fourth codes.length ≤ 2 ^ (3 * cells.length) ∨
    ∃ c k a b,
      c ∈ active ∧ m.star c ∈ active ∧
      lo ≤ k ∧ k ≤ hi ∧
      ∀ j, k ≤ j →
        e j = a ∨ e j = m.bar a ∨
        e j = b ∨ e j = m.bar b := by
  rcases persistent_lobes_separated_or_absorb m e r0 hrun
      lo hi active hactive hwit with hsep | habs
  · apply Or.inl
    exact encoded_starSeparated_bound m cells active P codes
      hsep hcells hcover hcodes hcodeP hcodeA hcap
  · exact Or.inr habs

/-- Quantitative variant using only the half-density conclusion.  This form is
convenient when the active lobe cells have already been counted separately. -/
theorem half_dense_epoch_code_bound
    (C A P : Nat)
    (codes : List (Nat × List Bool))
    (hcodes : codes.Nodup)
    (hcodeP : ∀ z ∈ codes, z.1 < P)
    (hcodeA : ∀ z ∈ codes, z.2.length = A)
    (hhalf : 2 * A ≤ C)
    (hcap : P * P ≤ 2 ^ (C - A)) :
    fourth codes.length ≤ 2 ^ (3 * C) := by
  exact encoded_half_active_bound C A P codes
    hcodes hcodeP hcodeA hhalf hcap

end Echo
