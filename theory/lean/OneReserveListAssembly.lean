import OneReserveFromNoTail
import ReservedComponentCounting

/-!
# Assemble one semantic reserve per support component

This file is purely finite bookkeeping.  Given pairwise-disjoint component
cell lists and, for each component, one cell which is not the mouth partner of
an active lobe root, it constructs a duplicate-free reserve list.  The active
roots, their mouth partners, and the reserves form a disjoint list inside the
finite cell universe, giving

    2 * #activeRoots + #components ≤ #allCells.

Together with `mixed_epoch_two_thirds`, this is the complete counting bridge
from the local external-reflector obstruction to the `2/3` epoch exponent.
-/

namespace Echo

variable (m : Machine)

/-- Recursive pairwise disjointness for a list of component cell lists. -/
def ComponentListsDisjoint : List (List Nat) → Prop
  | [] => True
  | cells :: rest =>
      (∀ other ∈ rest, ∀ c ∈ cells, c ∉ other) ∧
      ComponentListsDisjoint rest

/-- A reserve belongs to its component and is not the partner of an active
root. -/
def IsComponentReserve (roots cells : List Nat) (r : Nat) : Prop :=
  r ∈ cells ∧ m.star r ∉ roots

/-- Choose one reserve for every component. -/
theorem exists_component_reserve_list
    (roots : List Nat) :
    ∀ components : List (List Nat),
      (∀ cells ∈ components,
        ∃ r, IsComponentReserve m roots cells r) →
      ∃ reserves,
        List.Forall₂ (IsComponentReserve m roots)
          components reserves := by
  intro components
  induction components with
  | nil =>
      intro _
      exact ⟨[], List.Forall₂.nil⟩
  | cons cells rest ih =>
      intro h
      obtain ⟨r, hr⟩ := h cells List.mem_cons_self
      obtain ⟨rs, hrs⟩ := ih (fun other ho =>
        h other (List.mem_cons_of_mem _ ho))
      exact ⟨r :: rs, List.Forall₂.cons hr hrs⟩

/-- Forall₂ gives equal lengths. -/
theorem component_reserve_lengths
    {roots : List Nat} :
    ∀ {components reserves : List (List Nat) × List Nat}, True := by
  intro
  trivial

private theorem reserve_forall₂_length
    {roots : List Nat} :
    ∀ {components : List (List Nat)} {reserves : List Nat},
      List.Forall₂ (IsComponentReserve m roots)
        components reserves →
      reserves.length = components.length := by
  intro components reserves h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem reserve_mem_component
    {roots : List Nat} :
    ∀ {components : List (List Nat)} {reserves : List Nat},
      List.Forall₂ (IsComponentReserve m roots)
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

/-- Reserves selected from pairwise-disjoint components are duplicate-free. -/
theorem component_reserves_nodup
    {roots : List Nat} :
    ∀ {components : List (List Nat)} {reserves : List Nat},
      ComponentListsDisjoint components →
      List.Forall₂ (IsComponentReserve m roots)
        components reserves →
      reserves.Nodup := by
  intro components reserves hdis hrel
  induction hrel with
  | nil => simp
  | @cons cells r rest rs hr hrest ih =>
      unfold ComponentListsDisjoint at hdis
      simp only [List.nodup_cons]
      constructor
      · intro hmem
        rcases reserve_mem_component m hrest r hmem with
          ⟨other, ho, hro⟩
        exact (hdis.1 other ho r hr.1) hro
      · exact ih hdis.2

/-- Every selected reserve lies in the finite cell universe if every component
does. -/
theorem component_reserves_subset
    {roots allCells : List Nat}
    {components : List (List Nat)} {reserves : List Nat}
    (hrel : List.Forall₂ (IsComponentReserve m roots)
      components reserves)
    (hsub : ∀ cells ∈ components, ∀ c ∈ cells, c ∈ allCells) :
    ∀ r ∈ reserves, r ∈ allCells := by
  intro r hr
  rcases reserve_mem_component m hrel r hr with
    ⟨cells, hc, hrc⟩
  exact hsub cells hc r hrc

/-- The star involution is injective. -/
theorem star_injective_assembly : Function.Injective m.star := by
  intro a b h
  have h' := congrArg m.star h
  simpa only [m.star_invol] using h'

private theorem nodup_map_star
    {roots : List Nat} (hnd : roots.Nodup) :
    (roots.map m.star).Nodup := by
  induction roots with
  | nil => simp
  | cons r rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨s, hs, hstar⟩ := List.mem_map.mp hm
        have hrs : r = s := star_injective_assembly m hstar.symm
        exact hnd.1 (hrs ▸ hs)
      · exact ih hnd.2

/-- Active roots are star-separated. -/
def RootStarSeparated (roots : List Nat) : Prop :=
  roots.Nodup ∧ ∀ r ∈ roots, m.star r ∉ roots

/-- The root list and its partner list concatenate without duplicates. -/
theorem roots_and_partners_nodup
    {roots : List Nat}
    (hsep : RootStarSeparated m roots) :
    (roots ++ roots.map m.star).Nodup := by
  rw [List.nodup_append]
  refine ⟨hsep.1, nodup_map_star m hsep.1, ?_⟩
  intro a ha b hb hab
  obtain ⟨r, hr, hbr⟩ := List.mem_map.mp hb
  apply hsep.2 r hr
  have har : a = m.star r := by
    exact hab.trans hbr.symm
  rwa [← har]

/-- A reserve is not in the partner list. -/
theorem reserve_not_mem_partners
    {roots : List Nat} {r : Nat}
    (hr : m.star r ∉ roots) :
    r ∉ roots.map m.star := by
  intro hmem
  obtain ⟨a, ha, har⟩ := List.mem_map.mp hmem
  apply hr
  have h := congrArg m.star har
  simpa only [m.star_invol] using h ▸ ha

/-- **Finite one-reserve injection.** -/
theorem one_reserve_component_count
    (roots allCells : List Nat)
    (components : List (List Nat))
    (hsep : RootStarSeparated m roots)
    (hrootsSub : ∀ r ∈ roots,
      r ∈ allCells ∧ m.star r ∈ allCells)
    (hcomponentsSub : ∀ cells ∈ components,
      ∀ c ∈ cells, c ∈ allCells)
    (hcomponentsAwayRoots : ∀ cells ∈ components,
      ∀ c ∈ cells, c ∉ roots)
    (hdis : ComponentListsDisjoint components)
    (hreserve : ∀ cells ∈ components,
      ∃ r, IsComponentReserve m roots cells r)
    (hallNodup : allCells.Nodup) :
    2 * roots.length + components.length ≤ allCells.length := by
  obtain ⟨reserves, hrel⟩ :=
    exists_component_reserve_list m roots components hreserve
  have hresNodup := component_reserves_nodup m hdis hrel
  have hresSub := component_reserves_subset m hrel hcomponentsSub
  have hrootPartnerNodup := roots_and_partners_nodup m hsep
  have hresAwayRoots : ∀ r ∈ reserves, r ∉ roots := by
    intro r hr
    rcases reserve_mem_component m hrel r hr with
      ⟨cells, hc, hrc⟩
    exact hcomponentsAwayRoots cells hc r hrc
  have hresAwayPartners : ∀ r ∈ reserves,
      r ∉ roots.map m.star := by
    intro r hr
    have hgood : m.star r ∉ roots := by
      induction hrel with
      | nil => cases hr
      | @cons cells x rest rs hx hrest ih =>
          simp only [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hx.2
          · exact ih hr
    exact reserve_not_mem_partners m hgood
  have htotalNodup :
      (roots ++ roots.map m.star ++ reserves).Nodup := by
    rw [List.nodup_append]
    refine ⟨hrootPartnerNodup, hresNodup, ?_⟩
    intro x hx r hr hxr
    have hxCases := List.mem_append.mp hx
    rcases hxCases with hxRoot | hxPartner
    · exact hresAwayRoots r hr (hxr ▸ hxRoot)
    · exact hresAwayPartners r hr (hxr ▸ hxPartner)
  have htotalSub : ∀ c ∈ roots ++ roots.map m.star ++ reserves,
      c ∈ allCells := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · exact (hrootsSub c hc).1
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
        exact (hrootsSub r hr).2
    · exact hresSub c hc
  have hle := reserved_nodup_subset_length_nat htotalNodup htotalSub
  have hlen := reserve_forall₂_length m hrel
  simp only [List.length_append, List.length_map] at hle
  omega

end Echo
