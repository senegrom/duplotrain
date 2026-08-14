import NestedRestorationElimination

/-!
# Quantitative charging for nested restoration families

`NestedRestorationElimination` proves that strictly nested first-restoration
frames have distinct restored slots.  This file turns that structural fact
into finite counting statements.

The distinction between slots and switches is kept explicit.  Slot
injectivity alone gives a bound by the finite slot universe, hence `2 * N`
for a physical `N`-switch compilation.  A coefficient-one `N` bound needs
the additional fact that the charged roots occupy different switch cells;
that premise is exposed rather than silently inferred.

The final two theorems are phrased for duplicate-free observations at frame
openings.  They can therefore count productive or repeated-writer novel
vectors once a caller identifies those events with a nested family.
-/

namespace Echo

variable (m : Machine) (e : Nat -> Nat) (r0 : Nat -> Nat)

/-- A finite prefix of a strictly nested family of first-restoration frames.
Indices increase inward: later openings occur later, while later closings
occur earlier. -/
structure FiniteStrictNestedRestorationFamily
    (depth : Nat) (opening closing : Nat -> Nat) : Prop where
  frame : forall i, i < depth ->
    FirstRestorationFrame m e r0 (opening i) (closing i)
  nested : forall {i j}, i < j -> j < depth ->
    opening i < opening j /\ closing j < closing i

/-- The restored-root map is injective on the finite family. -/
theorem FiniteStrictNestedRestorationFamily.root_injective
    {depth : Nat} {opening closing : Nat -> Nat}
    (A : FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing)
    {i j : Nat} (hi : i < depth) (hj : j < depth)
    (hroot : oldSlot m e r0 (opening i) =
      oldSlot m e r0 (opening j)) :
    i = j := by
  by_cases hij : i = j
  · exact hij
  by_cases hlt : i < j
  · have horder := A.nested hlt hj
    have hne := strict_nested_first_restoration_roots_ne
      m e r0 (A.frame i hi) (A.frame j hj) horder.1 horder.2
    exact (hne hroot.symm).elim
  · have hji : j < i := by omega
    have horder := A.nested hji hi
    have hne := strict_nested_first_restoration_roots_ne
      m e r0 (A.frame j hj) (A.frame i hi) horder.1 horder.2
    exact (hne hroot).elim

private theorem map_nodup_of_injective_on_charge
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) :
    forall {xs : List alpha}, xs.Nodup ->
      (forall a, a ∈ xs -> forall b, b ∈ xs -> f a = f b -> a = b) ->
      (xs.map f).Nodup := by
  intro xs hnd hinj
  induction xs with
  | nil => simp
  | cons a rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
        have hab := hinj a List.mem_cons_self b
          (List.mem_cons_of_mem _ hb) hfb.symm
        exact hnd.1 (hab ▸ hb)
      · exact ih hnd.2
          (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx)
            y (List.mem_cons_of_mem _ hy))

private theorem nodup_of_map_nodup_charge
    {alpha beta : Type} [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) :
    forall {xs : List alpha}, (xs.map f).Nodup -> xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons a rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro ha
        apply hnd.1
        exact List.mem_map.mpr ⟨a, ha, rfl⟩
      · exact ih hnd.2

private theorem nodup_subset_length_charge
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall {xs pool : List alpha},
      xs.Nodup ->
      (forall x, x ∈ xs -> x ∈ pool) ->
      xs.length <= pool.length := by
  intro xs
  induction xs with
  | nil => intro pool _ _; exact Nat.zero_le _
  | cons x rest ih =>
      intro pool hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : x ∈ pool := hsub x List.mem_cons_self
      have hrest : forall y, y ∈ rest -> y ∈ pool.erase x := by
        intro y hy
        have hyPool := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hEq => hnd.1 (hEq ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyPool
      have hle := ih hnd.2 hrest
      rw [List.length_erase_of_mem hx] at hle
      have hpositive : 0 < pool.length := by
        cases pool with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- The complete finite family has no repeated restoration root. -/
theorem FiniteStrictNestedRestorationFamily.roots_nodup
    {depth : Nat} {opening closing : Nat -> Nat}
    (A : FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing) :
    ((List.range depth).map
      (fun i => oldSlot m e r0 (opening i))).Nodup := by
  apply map_nodup_of_injective_on_charge
    (fun i => oldSlot m e r0 (opening i)) List.nodup_range
  intro i hi j hj hEq
  exact A.root_injective m e r0
    (List.mem_range.mp hi) (List.mem_range.mp hj) hEq

/-- **Finite nested-root charge.**  If every restored root belongs to a
finite slot universe, the depth of a strictly nested family is at most the
size of that universe. -/
theorem FiniteStrictNestedRestorationFamily.depth_le_slots
    {depth : Nat} {opening closing : Nat -> Nat}
    (A : FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing)
    (slots : List Nat)
    (hroot : forall i, i < depth ->
      oldSlot m e r0 (opening i) ∈ slots) :
    depth <= slots.length := by
  have hle := nodup_subset_length_charge
    (A.roots_nodup m e r0)
    (fun root hrootMap => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrootMap
      exact hroot i (List.mem_range.mp hi))
  simpa only [List.length_map, List.length_range] using hle

/-- Physical corollary: two available branch slots per switch give an
unconditional `2 * N` bound on the depth of this nested branch. -/
theorem FiniteStrictNestedRestorationFamily.depth_le_two_mul
    {depth N : Nat} {opening closing : Nat -> Nat}
    (A : FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing)
    (slots : List Nat)
    (hroot : forall i, i < depth ->
      oldSlot m e r0 (opening i) ∈ slots)
    (hslots : slots.length <= 2 * N) :
    depth <= 2 * N := by
  exact Nat.le_trans (A.depth_le_slots m e r0 slots hroot) hslots

end Echo
