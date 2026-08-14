import SupportSize

/-!
# At most one active cell per mouth-partner pair

The mouth pairing `star` is a fixed-point-free involution.  Before a pair of
occupied lobe cells absorbs the run into its Gray square, the set of genuinely
variable lobe cells must be `star`-independent: it cannot contain both `c` and
`star c`.

This file proves the finite counting consequence independently of the dynamic
argument.  If `active` is a duplicate-free, `star`-independent subset of a
`star`-closed cell universe, then

    2 * active.length ≤ cells.length.

Combined with the lobe absorption theorem, this replaces the unnecessarily
strong requirement that active lobes inject specifically into non-lobe cells.
-/

namespace Echo

variable (m : Machine)

def StarIndependent (active : List Nat) : Prop :=
  ∀ c, c ∈ active → m.star c ∉ active


private theorem nodup_map_of_injective_on
    {f : Nat → Nat} {l : List Nat}
    (hinj : ∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y)
    (hnd : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      simp only [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
        have hxy := hinj x List.mem_cons_self y
          (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (hxy ▸ hy)
      · exact ih
          (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb)) hnd.2

private theorem nodup_subset_length_nat {l S : List Nat}
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) :
    l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

end Echo
