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

/-- The first port of a descent is a branch port. -/
theorem descent_entry_branch {w : Wiring} {t : Tongues} {p s : Nat}
    {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') : p % 3 ≠ 0 := by
  cases h with
  | last hp _ _ => exact hp
  | cons hp _ _ _ => exact hp

/-- A bounded wiring keeps the entry switch of every concrete descent below
`N`, and therefore keeps the entry branch port below `3*N`. -/
theorem descent_entry_bounded
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {t : Tongues} {p s : Nat} {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') : p < 3 * N := by
  cases h with
  | @last t p s hp hlink hs =>
      have hstem := (hN _ _ hlink).1
      have hmod : p % 3 < 3 := Nat.mod_lt _ (by omega)
      have hdecomp := Nat.mod_add_div p 3
      omega
  | @cons t p p' s ps t' hp hlink hp' hrest =>
      have hstem := (hN _ _ hlink).1
      have hmod : p % 3 < 3 := Nat.mod_lt _ (by omega)
      have hdecomp := Nat.mod_add_div p 3
      omega

/-- Every branch visited by a bounded concrete descent belongs to one of the
first `N` switches. -/
theorem descent_route_bounded
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {t : Tongues} {p s : Nat} {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') :
    ∀ b ∈ p :: ps, b < 3 * N := by
  induction h with
  | @last t p s hp hlink hs =>
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact descent_entry_bounded hN
          (Descent.last hp hlink hs)
      · cases hb
  | @cons t p p' s ps t' hp hlink hp' hrest ih =>
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact descent_entry_bounded hN
          (Descent.cons hp hlink hp' hrest)
      · exact ih b hb

/-- The root switch of every bounded descent is below `N`. -/
theorem descent_root_bounded
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {t : Tongues} {p s : Nat} {ps : List Nat} {t' : Tongues}
    (h : Descent w t p ps s t') : descentRoot p ps < N := by
  have hlast := descent_last_link h
  have hstem := (hN _ _ hlast).1
  unfold descentRoot
  omega

/-- A compact code for a branch port. -/
def branchCode (p : Nat) : Nat :=
  2 * (p / 3) + (p % 3 - 1)

/-- A branch port below `3*N` has code below `2*N`. -/
theorem branchCode_lt_two_mul
    {p N : Nat} (hp : p < 3 * N) (hbranch : p % 3 ≠ 0) :
    branchCode p < 2 * N := by
  unfold branchCode
  have hmod : p % 3 < 3 := Nat.mod_lt _ (by omega)
  have hdecomp := Nat.mod_add_div p 3
  omega

/-- The branch code is injective on branch ports. -/
theorem branchCode_injective
    {p q : Nat} (hp : p % 3 ≠ 0) (hq : q % 3 ≠ 0)
    (hcode : branchCode p = branchCode q) : p = q := by
  unfold branchCode at hcode
  have hpmod : p % 3 < 3 := Nat.mod_lt _ (by omega)
  have hqmod : q % 3 < 3 := Nat.mod_lt _ (by omega)
  have hpdecomp := Nat.mod_add_div p 3
  have hqdecomp := Nat.mod_add_div q 3
  omega

private theorem map_nodup_of_injective_on
    {α β : Type} (f : α → β) :
    ∀ {xs : List α}, xs.Nodup →
      (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) →
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

/-- Any duplicate-free finite list of branch ports from the first `N`
switches has length at most `2*N`. -/
theorem branch_port_list_length_le_two_mul
    {N : Nat} {slots : List Nat}
    (hnd : slots.Nodup)
    (hbounded : ∀ p ∈ slots, p < 3 * N)
    (hbranch : ∀ p ∈ slots, p % 3 ≠ 0) :
    slots.length ≤ 2 * N := by
  have hcodeNodup : (slots.map branchCode).Nodup := by
    apply map_nodup_of_injective_on branchCode hnd
    intro p hp q hq hcode
    exact branchCode_injective
      (hbranch p hp) (hbranch q hq) hcode
  have hsub : ∀ x ∈ slots.map branchCode,
      x ∈ List.range (2 * N) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range.mpr
      (branchCode_lt_two_mul (hbounded p hp) (hbranch p hp))
  have hle := nodup_subset_length_nat hcodeNodup hsub
  simpa using hle

/-- A port is a realised concrete cascade entry. -/
def IsDescentEntry (w : Wiring) (p : Nat) : Prop :=
  ∃ t ps s t', Descent w t p ps s t'

/-- Realised cascade entries are branch ports. -/
theorem isDescentEntry_branch
    {w : Wiring} {p : Nat} (hp : IsDescentEntry w p) :
    p % 3 ≠ 0 := by
  rcases hp with ⟨t, ps, s, t', h⟩
  exact descent_entry_branch h

/-- Realised cascade entries in a bounded wiring are below `3*N`. -/
theorem isDescentEntry_bounded
    {w : Wiring} {N p : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (hp : IsDescentEntry w p) : p < 3 * N := by
  rcases hp with ⟨t, ps, s, t', h⟩
  exact descent_entry_bounded hN h

/-- **Concrete slot bound.**  A duplicate-free finite list of realised
cascade entries has at most two entries per switch. -/
theorem descent_entry_list_length_le_two_mul
    {w : Wiring} {N : Nat} {slots : List Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (hnd : slots.Nodup)
    (hentries : ∀ p ∈ slots, IsDescentEntry w p) :
    slots.length ≤ 2 * N := by
  apply branch_port_list_length_le_two_mul hnd
  · intro p hp
    exact isDescentEntry_bounded hN (hentries p hp)
  · intro p hp
    exact isDescentEntry_branch (hentries p hp)

/-- Any duplicate-free finite list of cell indices below `N` has length at
most `N`. -/
theorem bounded_cell_list_length_le
    {N : Nat} {cells : List Nat}
    (hnd : cells.Nodup)
    (hbounded : ∀ c ∈ cells, c < N) :
    cells.length ≤ N := by
  have hsub : ∀ c ∈ cells, c ∈ List.range N := by
    intro c hc
    exact List.mem_range.mpr (hbounded c hc)
  have hle := nodup_subset_length_nat hnd hsub
  simpa using hle

/-- A cell is realised as the root of some concrete descent. -/
def IsDescentRoot (w : Wiring) (c : Nat) : Prop :=
  ∃ t p ps s t', Descent w t p ps s t' ∧ descentRoot p ps = c

/-- Realised cascade roots in a bounded wiring are below `N`. -/
theorem isDescentRoot_bounded
    {w : Wiring} {N c : Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (hc : IsDescentRoot w c) : c < N := by
  rcases hc with ⟨t, p, ps, s, t', h, rfl⟩
  exact descent_root_bounded hN h

/-- **Concrete root-cell bound.**  A duplicate-free finite list of realised
cascade roots has at most one entry per switch. -/
theorem descent_root_list_length_le
    {w : Wiring} {N : Nat} {cells : List Nat}
    (hN : ∀ a b, w.link a = some b →
      a < 3 * N ∧ b < 3 * N)
    (hnd : cells.Nodup)
    (hroots : ∀ c ∈ cells, IsDescentRoot w c) :
    cells.length ≤ N := by
  apply bounded_cell_list_length_le hnd
  intro c hc
  exact isDescentRoot_bounded hN (hroots c hc)

end GeneralN
