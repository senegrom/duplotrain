import ActiveLobes

/-!
# Integrated fixed-support bound before the Gray tail

This module joins the two independent halves of the strict-base argument:

* `active_lobes_half`: before absorption, genuinely variable occupied lobes
  use at most one endpoint of each mouth-partner pair; and
* `encoded_three_quarter_star_pair_bound`: a tree/pseudoforest code of
  square-capacity `P² ≤ 2^M`, together with `A` active lobe bits satisfying
  `2A ≤ C`, has fourth-power capacity at most `2^(3C)`.

The remaining structural work is now isolated in the hypotheses that produce
an injective code and a certified component capacity.  No separate injection
from active lobe cells into non-lobe cells is needed.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Fixed-support three-quarter bound before absorption.**

`cells` is a star-closed finite cell universe, `active` is the list of
variable occupied-lobe cells during `[i,j]`, and `codes` is any pairwise-
distinct encoding of the states by a projected component code below `P` plus
one Boolean coordinate for every active cell.

Once the cell budget splits as `C = L + M`, the active cells lie among the `L`
lobe cells, and the non-lobe/component code satisfies `P² ≤ 2^M`, Lean derives

    codes.length^4 ≤ 2^(3 * cells.length).
-/
theorem fixed_support_before_gray_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j : Nat} (hij : i ≤ j)
    (cells active : List Nat)
    (L M P : Nat)
    (codes : List (Nat × List Bool))
    (hactiveNodup : active.Nodup)
    (hactiveSub : ∀ c ∈ active, c ∈ cells)
    (hclosed : StarClosed m cells)
    (hvar : ∀ c ∈ active, VariesOnInterval m e r0 i j c)
    (hlobe : ∀ c ∈ active,
      ∃ s, m.cellOf s = c ∧ LobeSlot m s ∧
        ∀ k, i ≤ k → k ≤ j → Occupied m e r0 k s)
    (hnoGray : ∀ k, i < k → k ≤ j → ¬ GrayTail m e r0 k)
    (hcodeNodup : codes.Nodup)
    (hcodeP : ∀ z ∈ codes, z.1 < P)
    (hcodeA : ∀ z ∈ codes, z.2.length = active.length)
    (hC : cells.length = L + M)
    (hAL : active.length ≤ L)
    (hcap : P * P ≤ 2^M) :
    fourth codes.length ≤ 2^(3 * cells.length) := by
  have hhalf : 2 * active.length ≤ cells.length :=
    active_lobes_half m e r0 hrun hr0 hij cells active
      hactiveNodup hactiveSub hclosed hvar hlobe hnoGray
  exact encoded_three_quarter_star_pair_bound
    cells.length L M active.length P codes
    hcodeNodup hcodeP hcodeA hC hAL hhalf hcap

end Echo
