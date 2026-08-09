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

/-- Any duplicate-free collection of observed post-opening states drawn
from a nested family is bounded by the same slot charge.  The observation
may be a complete register snapshot, a restricted raw tongue vector, or any
other state code. -/
theorem nested_opening_novelty_le_slots
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {depth : Nat} {opening closing : Nat -> Nat}
    (A : FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing)
    (slots : List Nat)
    (hroot : forall i, i < depth ->
      oldSlot m e r0 (opening i) ∈ slots)
    (observe : Nat -> alpha) (indices : List Nat)
    (hindices : forall i, i ∈ indices -> i < depth)
    (hnovel : (indices.map
      (fun i => observe (opening i + 1))).Nodup) :
    indices.length <= slots.length := by
  have hindicesNodup : indices.Nodup :=
    nodup_of_map_nodup_charge
      (fun i => observe (opening i + 1)) hnovel
  have hrootsNodup : (indices.map
      (fun i => oldSlot m e r0 (opening i))).Nodup := by
    apply map_nodup_of_injective_on_charge
      (fun i => oldSlot m e r0 (opening i)) hindicesNodup
    intro i hi j hj hEq
    exact A.root_injective m e r0
      (hindices i hi) (hindices j hj) hEq
  have hle := nodup_subset_length_charge hrootsNodup
    (fun root hrootMap => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrootMap
      exact hroot i (hindices i hi))
  simpa only [List.length_map] using hle

/-- **General-`N` novelty bound for the nested branch.**  Under the physical
two-slot-per-switch bound, arbitrarily deep nested restoration can account
for at most `2 * N` duplicate-free productive/repeated-writer post-vectors.
This is unconditional for the nested branch once its roots are covered by
the compiler's physical slot list. -/
theorem nested_opening_novelty_le_two_mul
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {depth N : Nat} {opening closing : Nat -> Nat}
    (A : FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing)
    (slots : List Nat)
    (hroot : forall i, i < depth ->
      oldSlot m e r0 (opening i) ∈ slots)
    (hslots : slots.length <= 2 * N)
    (observe : Nat -> alpha) (indices : List Nat)
    (hindices : forall i, i ∈ indices -> i < depth)
    (hnovel : (indices.map
      (fun i => observe (opening i + 1))).Nodup) :
    indices.length <= 2 * N := by
  exact Nat.le_trans
    (nested_opening_novelty_le_slots m e r0 A slots hroot
      observe indices hindices hnovel)
    hslots

/-- **Coefficient-one interface.**  If no two charged restoration roots
belong to the same switch cell, then nested novel openings charge switches,
not merely slots, and their number is at most `N`.

The `hone` premise is deliberately explicit: root-slot injectivity by itself
does not prove cell injectivity when a switch has two branch slots. -/
theorem nested_opening_novelty_le_switches
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {depth N : Nat} {opening closing : Nat -> Nat}
    (A : FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing)
    (observe : Nat -> alpha) (indices : List Nat)
    (hindices : forall i, i ∈ indices -> i < depth)
    (hnovel : (indices.map
      (fun i => observe (opening i + 1))).Nodup)
    (hbounded : forall i, i ∈ indices ->
      m.cellOf (oldSlot m e r0 (opening i)) < N)
    (hone : forall i, i ∈ indices -> forall j, j ∈ indices ->
      m.cellOf (oldSlot m e r0 (opening i)) =
        m.cellOf (oldSlot m e r0 (opening j)) ->
      oldSlot m e r0 (opening i) = oldSlot m e r0 (opening j)) :
    indices.length <= N := by
  have hindicesNodup : indices.Nodup :=
    nodup_of_map_nodup_charge
      (fun i => observe (opening i + 1)) hnovel
  have hcellsNodup : (indices.map
      (fun i => m.cellOf (oldSlot m e r0 (opening i)))).Nodup := by
    apply map_nodup_of_injective_on_charge
      (fun i => m.cellOf (oldSlot m e r0 (opening i))) hindicesNodup
    intro i hi j hj hcell
    exact A.root_injective m e r0
      (hindices i hi) (hindices j hj) (hone i hi j hj hcell)
  have hle := nodup_subset_length_charge hcellsNodup
    (fun C hC => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
      exact List.mem_range.mpr (hbounded i hi))
  simpa only [List.length_map, List.length_range] using hle

/-- A finite slot universe has binary switch capacity when no cell contains
three distinct listed roots.  This is the exact local capacity supplied by
the two branch slots of a physical lazy switch. -/
def AtMostTwoSlotsPerCell (slots : List Nat) : Prop :=
  forall a, a ∈ slots -> forall b, b ∈ slots -> forall c, c ∈ slots ->
    m.cellOf a = m.cellOf b ->
    m.cellOf a = m.cellOf c ->
    a = b \/ a = c \/ b = c

/-- **Coefficient-one repeated-writer charge.**

Suppose the selected nested openings are all repeated writers: each has an
earlier opening in the family that writes the same switch.  Because nested
roots are injective and a physical switch supplies at most two root slots,
two selected repeated openings cannot write the same switch.  Consequently
duplicate-free post-opening observations at those events number at most
`N`, one per switch.

Unlike `nested_opening_novelty_le_switches`, this theorem does not assume
root-cell injectivity.  It derives the needed injectivity for the repeated
subset from the binary per-switch slot capacity. -/
theorem nested_repeated_writer_novelty_le_switches
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (hr0 : forall c, m.cellOf (r0 c) = c)
    {depth N : Nat} {opening closing : Nat -> Nat}
    (A : FiniteStrictNestedRestorationFamily
      m e r0 depth opening closing)
    (slots : List Nat)
    (hroot : forall i, i < depth ->
      oldSlot m e r0 (opening i) ∈ slots)
    (hcapacity : AtMostTwoSlotsPerCell m slots)
    (hbounded : forall s, s ∈ slots -> m.cellOf s < N)
    (observe : Nat -> alpha) (indices : List Nat)
    (hindices : forall i, i ∈ indices -> i < depth)
    (hrepeated : forall i, i ∈ indices ->
      exists j, j < i /\
        writerAt m e (opening j) = writerAt m e (opening i))
    (hnovel : (indices.map
      (fun i => observe (opening i + 1))).Nodup) :
    indices.length <= N := by
  have hindicesNodup : indices.Nodup :=
    nodup_of_map_nodup_charge
      (fun i => observe (opening i + 1)) hnovel
  have hcellsNodup : (indices.map
      (fun i => m.cellOf (oldSlot m e r0 (opening i)))).Nodup := by
    apply map_nodup_of_injective_on_charge
      (fun i => m.cellOf (oldSlot m e r0 (opening i))) hindicesNodup
    intro i hi j hj hcell
    have hiDepth := hindices i hi
    have hjDepth := hindices j hj
    by_cases hij : i = j
    · exact hij
    by_cases hlt : i < j
    · obtain ⟨a, hai, hwriter⟩ := hrepeated i hi
      have haDepth : a < depth := by omega
      have hcellAI :
          m.cellOf (oldSlot m e r0 (opening a)) =
            m.cellOf (oldSlot m e r0 (opening i)) := by
        have haCell := old_new_cell m e r0 hr0 (opening a)
        have hiCell := old_new_cell m e r0 hr0 (opening i)
        have hw : m.cellOf (e (opening a + 1)) =
            m.cellOf (e (opening i + 1)) := by
          simpa [writerAt] using hwriter
        exact haCell.trans (hw.trans hiCell.symm)
      have hcases := hcapacity
        (oldSlot m e r0 (opening a)) (hroot a haDepth)
        (oldSlot m e r0 (opening i)) (hroot i hiDepth)
        (oldSlot m e r0 (opening j)) (hroot j hjDepth)
        hcellAI (hcellAI.trans hcell)
      rcases hcases with hEq | hEq | hEq
      · have := A.root_injective m e r0 haDepth hiDepth hEq
        omega
      · have := A.root_injective m e r0 haDepth hjDepth hEq
        omega
      · exact A.root_injective m e r0 hiDepth hjDepth hEq
    · have hji : j < i := by omega
      obtain ⟨a, haj, hwriter⟩ := hrepeated j hj
      have haDepth : a < depth := by omega
      have hcellAJ :
          m.cellOf (oldSlot m e r0 (opening a)) =
            m.cellOf (oldSlot m e r0 (opening j)) := by
        have haCell := old_new_cell m e r0 hr0 (opening a)
        have hjCell := old_new_cell m e r0 hr0 (opening j)
        have hw : m.cellOf (e (opening a + 1)) =
            m.cellOf (e (opening j + 1)) := by
          simpa [writerAt] using hwriter
        exact haCell.trans (hw.trans hjCell.symm)
      have hcases := hcapacity
        (oldSlot m e r0 (opening a)) (hroot a haDepth)
        (oldSlot m e r0 (opening j)) (hroot j hjDepth)
        (oldSlot m e r0 (opening i)) (hroot i hiDepth)
        hcellAJ (hcellAJ.trans hcell.symm)
      rcases hcases with hEq | hEq | hEq
      · have := A.root_injective m e r0 haDepth hjDepth hEq
        omega
      · have := A.root_injective m e r0 haDepth hiDepth hEq
        omega
      · exact (A.root_injective m e r0 hjDepth hiDepth hEq).symm
  have hle := nodup_subset_length_charge hcellsNodup
    (fun C hC => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hC
      exact List.mem_range.mpr
        (hbounded (oldSlot m e r0 (opening i))
          (hroot i (hindices i hi))))
  simpa only [List.length_map, List.length_range] using hle

end Echo
