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

/-- A cell list contains the mouth partner of each of its members. -/
def StarClosed (cells : List Nat) : Prop :=
  ∀ c, c ∈ cells → m.star c ∈ cells

/-- No two listed cells are mouth partners. -/
def StarIndependent (active : List Nat) : Prop :=
  ∀ c, c ∈ active → m.star c ∉ active

/-- The mouth involution is injective. -/
theorem star_injective : Function.Injective m.star := by
  intro a b h
  have h' := congrArg m.star h
  simpa only [m.star_invol] using h'

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

private theorem nodup_append_of_disjoint
    {l r : List Nat}
    (hl : l.Nodup) (hr : r.Nodup)
    (hdis : ∀ x ∈ l, x ∉ r) :
    (l ++ r).Nodup := by
  induction l with
  | nil => simpa using hr
  | cons x rest ih =>
      simp only [List.nodup_cons] at hl
      simp only [List.cons_append, List.nodup_cons]
      constructor
      · intro hm
        simp only [List.mem_append] at hm
        rcases hm with hm | hm
        · exact hl.1 hm
        · exact hdis x List.mem_cons_self hm
      · exact ih hl.2
          (fun y hy => hdis y (List.mem_cons_of_mem _ hy))

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

/-- **Half-universe bound.**  A `star`-independent finite set occupies at most
one endpoint of each mouth-partner pair. -/
theorem star_independent_length
    (cells active : List Nat)
    (hnd : active.Nodup)
    (hsub : ∀ c ∈ active, c ∈ cells)
    (hclosed : StarClosed m cells)
    (hind : StarIndependent m active) :
    2 * active.length ≤ cells.length := by
  have hstarnd : (active.map m.star).Nodup :=
    nodup_map_of_injective_on
      (fun x _ y _ hxy => star_injective m hxy) hnd
  have hdis : ∀ c ∈ active, c ∉ active.map m.star := by
    intro c hc hmem
    obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hmem
    have h := congrArg m.star hdc
    rw [m.star_invol] at h
    apply hind c hc
    rw [← h]
    exact hd
  have hdoubled : (active ++ active.map m.star).Nodup :=
    nodup_append_of_disjoint hnd hstarnd hdis
  have hsubset : ∀ c ∈ active ++ active.map m.star, c ∈ cells := by
    intro c hc
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hsub c hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      exact hclosed d (hsub d hd)
  have hle := nodup_subset_length_nat hdoubled hsubset
  simpa only [List.length_append, List.length_map, Nat.two_mul] using hle

end Echo
