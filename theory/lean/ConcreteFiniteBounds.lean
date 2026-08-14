import ConcreteCascadeFacts

/-!
# Finite concrete slot and root bounds

An `N`-switch wiring has only `2*N` branch ports.  This file proves that
statement in the form required by the concrete echo compilation, without
assuming the finite slot list is a sublist of any preconstructed enumeration.

Every branch port is encoded injectively by

    2 * switch + branchBit,

where the branch bit is zero for residue 1 and one for residue 2.  Actual
cascade entries are branch ports on switches below `N`, so any duplicate-free
list of them has length at most `2*N`.  Likewise any duplicate-free list of
cascade roots has length at most `N`.
-/

namespace GeneralN


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

def IsDescentEntry (w : Wiring) (p : Nat) : Prop :=
  ∃ t ps s t', Descent w t p ps s t'

end GeneralN
