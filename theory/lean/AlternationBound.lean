import LinearBound

/-!
# Alternation structure for the echo machine

This file starts the structural part missing from the linear accounting bound.
The first theorem is unconditional: if two ascents of the same cell have
different successors, then the partner cell must have been ascended in the
interval between them. Thus steering variation cannot be generated locally;
it has to be fed by the mouth partner.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

theorem predecessor_cell
    (hrun : IsRun m e r0) (hr0 : ∀ c, m.cellOf (r0 c) = c) (k : Nat) :
    m.cellOf (e k) = m.star (m.cellOf (m.bar (e (k+1)))) := by
  have hw := (witness m e r0 hrun hr0 k).1
  have hs := congrArg m.star hw
  rw [m.star_invol] at hs
  exact hs.symm

def AlternationStep (k : Nat) : Prop :=
  ProductiveStep m e r0 k ∧ ¬ FirstStep m e k

private theorem nodup_map_of_injective_on
    {f : Nat → Nat} {l : List Nat}
    (hinj : ∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y)
    (hnd : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x t ih =>
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
    (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ S) : l.length ≤ S.length := by
  induction l generalizing S with
  | nil => exact Nat.zero_le _
  | cons x t ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ S := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ t, y ∈ S.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      have hlen : (S.erase x).length = S.length - 1 := List.length_erase_of_mem hx
      rw [hlen] at hle
      have hpos : 0 < S.length := by
        cases S with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

end Echo
