import OneReserveFromNoTail

/-!
# Correct finite assembly of one reserve per component

The coordinates are parenthesised explicitly as

    (activeRoots ++ activePartners) ++ reserves.

This avoids the append-associativity ambiguity in the first draft.  All
cardinality lemmas are local, so the module has no dependency on private
helpers from another file.
-/

namespace Echo

variable (m : Machine)

/-- Recursive pairwise disjointness for component cell lists. -/
def ComponentListsDisjointV2 : List (List Nat) → Prop
  | [] => True
  | cells :: rest =>
      (∀ other ∈ rest, ∀ c ∈ cells, c ∉ other) ∧
      ComponentListsDisjointV2 rest

/-- A selected reserve belongs to its component and is not the mouth partner
of an active root. -/
def IsComponentReserveV2
    (roots cells : List Nat) (r : Nat) : Prop :=
  r ∈ cells ∧ m.star r ∉ roots

/-- Pointwise lifting of a relation to equal-length lists (local copy
of Mathlib's `PairForall`, absent from core). -/
inductive PairForall {α β : Type} (R : α → β → Prop) :
    List α → List β → Prop
  | nil : PairForall R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → PairForall R as bs → PairForall R (a :: as) (b :: bs)

/-- Select one reserve per component. -/
theorem exists_component_reserve_list_v2
    (roots : List Nat) :
    ∀ components : List (List Nat),
      (∀ cells ∈ components,
        ∃ r, IsComponentReserveV2 m roots cells r) →
      ∃ reserves,
        PairForall (IsComponentReserveV2 m roots)
          components reserves := by
  intro components
  induction components with
  | nil =>
      intro _
      exact ⟨[], PairForall.nil⟩
  | cons cells rest ih =>
      intro h
      obtain ⟨r, hr⟩ := h cells List.mem_cons_self
      obtain ⟨rs, hrs⟩ := ih (fun other ho =>
        h other (List.mem_cons_of_mem _ ho))
      exact ⟨r :: rs, PairForall.cons hr hrs⟩

private theorem reserve_v2_length
    {roots : List Nat} :
    ∀ {components : List (List Nat)} {reserves : List Nat},
      PairForall (IsComponentReserveV2 m roots)
        components reserves →
      reserves.length = components.length := by
  intro components reserves h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem reserve_v2_mem_component
    {roots : List Nat} :
    ∀ {components : List (List Nat)} {reserves : List Nat},
      PairForall (IsComponentReserveV2 m roots)
        components reserves →
      ∀ r ∈ reserves,
        ∃ cells, cells ∈ components ∧ r ∈ cells := by
  intro components reserves h
  induction h with
  | nil =>
      intro r hr
      cases hr
  | @cons cells r rest rs hr hrest ih =>
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨cells, List.mem_cons_self, hr.1⟩
      · rcases ih x hx with ⟨other, ho, hxo⟩
        exact ⟨other, List.mem_cons_of_mem _ ho, hxo⟩

/-- Reserves chosen from pairwise-disjoint components are duplicate-free. -/
theorem component_reserves_nodup_v2
    {roots : List Nat} :
    ∀ {components : List (List Nat)} {reserves : List Nat},
      ComponentListsDisjointV2 components →
      PairForall (IsComponentReserveV2 m roots)
        components reserves →
      reserves.Nodup := by
  intro components reserves hdis hrel
  induction hrel with
  | nil => simp
  | @cons cells r rest rs hr hrest ih =>
      unfold ComponentListsDisjointV2 at hdis
      simp only [List.nodup_cons]
      constructor
      · intro hmem
        rcases reserve_v2_mem_component m hrest r hmem with
          ⟨other, ho, hro⟩
        exact (hdis.1 other ho r hr.1) hro
      · exact ih hdis.2

private theorem nodup_map_star_v2
    {roots : List Nat} (hnd : roots.Nodup) :
    (roots.map m.star).Nodup := by
  induction roots with
  | nil => simp
  | cons r rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨s, hs, hEq⟩ := List.mem_map.mp hm
        have hstar := congrArg m.star hEq
        rw [m.star_invol, m.star_invol] at hstar
        exact hnd.1 (hstar ▸ hs)
      · exact ih hnd.2

/-- Active roots are duplicate-free and contain no mouth-partner pair. -/
def RootStarSeparatedV2 (roots : List Nat) : Prop :=
  roots.Nodup ∧ ∀ r ∈ roots, m.star r ∉ roots

private theorem roots_partners_nodup_v2
    {roots : List Nat}
    (hsep : RootStarSeparatedV2 m roots) :
    (roots ++ roots.map m.star).Nodup := by
  rw [List.nodup_append]
  refine ⟨hsep.1, nodup_map_star_v2 m hsep.1, ?_⟩
  intro a ha b hb hab
  obtain ⟨r, hr, hEq⟩ := List.mem_map.mp hb
  apply hsep.2 r hr
  have hstarA : m.star r = a := hEq.trans hab.symm
  rw [hstarA]
  exact ha

private theorem reserve_v2_not_partner
    {roots : List Nat} {r : Nat}
    (hr : m.star r ∉ roots) :
    r ∉ roots.map m.star := by
  intro hmem
  obtain ⟨a, ha, hEq⟩ := List.mem_map.mp hmem
  have hstar := congrArg m.star hEq
  rw [m.star_invol] at hstar
  apply hr
  rw [← hstar]
  exact ha

private theorem nodup_subset_length_v2
    {xs ys : List Nat}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ ys.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun hxy => hnd.1 (hxy ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      have hpos : 0 < ys.length := by
        cases ys with
        | nil => cases hx
        | cons _ _ => simp
      simp only [List.length_cons]
      omega

/-- **One-reserve finite injection.** -/
theorem one_reserve_component_count_v2
    (roots allCells : List Nat)
    (components : List (List Nat))
    (hsep : RootStarSeparatedV2 m roots)
    (hrootsSub : ∀ r ∈ roots,
      r ∈ allCells ∧ m.star r ∈ allCells)
    (hcomponentsSub : ∀ cells ∈ components,
      ∀ c ∈ cells, c ∈ allCells)
    (hcomponentsAwayRoots : ∀ cells ∈ components,
      ∀ c ∈ cells, c ∉ roots)
    (hdis : ComponentListsDisjointV2 components)
    (hreserve : ∀ cells ∈ components,
      ∃ r, IsComponentReserveV2 m roots cells r) :
    2 * roots.length + components.length ≤ allCells.length := by
  obtain ⟨reserves, hrel⟩ :=
    exists_component_reserve_list_v2 m roots components hreserve
  have hresNodup := component_reserves_nodup_v2 m hdis hrel
  have hrootPartnerNodup := roots_partners_nodup_v2 m hsep
  have hresAwayRoots : ∀ r ∈ reserves, r ∉ roots := by
    intro r hr
    rcases reserve_v2_mem_component m hrel r hr with
      ⟨cells, hc, hrc⟩
    exact hcomponentsAwayRoots cells hc r hrc
  have hstar_not_root : ∀ {comps : List (List Nat)} {rs : List Nat},
      PairForall (IsComponentReserveV2 m roots) comps rs →
      ∀ r ∈ rs, m.star r ∉ roots := by
    intro comps rs h
    induction h with
    | nil =>
        intro r hr
        cases hr
    | @cons cells x rest rs hx hrest ih =>
        intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with hr | hr
        · rw [hr]
          exact hx.2
        · exact ih r hr
  have hresAwayPartners : ∀ r ∈ reserves,
      r ∉ roots.map m.star := by
    intro r hr
    exact reserve_v2_not_partner m (hstar_not_root hrel r hr)
  have htotalNodup :
      ((roots ++ roots.map m.star) ++ reserves).Nodup := by
    rw [List.nodup_append]
    refine ⟨hrootPartnerNodup, hresNodup, ?_⟩
    intro x hx r hr hxr
    rcases List.mem_append.mp hx with hxRoot | hxPartner
    · apply hresAwayRoots r hr
      rw [← hxr]
      exact hxRoot
    · apply hresAwayPartners r hr
      rw [← hxr]
      exact hxPartner
  have htotalSub :
      ∀ c ∈ (roots ++ roots.map m.star) ++ reserves,
        c ∈ allCells := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact (hrootsSub c hc).1
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
        exact (hrootsSub r hr).2
    · rcases reserve_v2_mem_component m hrel c hc with
        ⟨cells, hcells, hcin⟩
      exact hcomponentsSub cells hcells c hcin
  have hle := nodup_subset_length_v2 htotalNodup htotalSub
  have hlen := reserve_v2_length m hrel
  simp only [List.length_append, List.length_map] at hle
  omega

end Echo
