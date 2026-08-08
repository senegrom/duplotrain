import NoFullComponentFreezeCore

/-!
# Finite no-full component lists form one frozen block

This corrected wrapper concatenates the cells of finitely many represented
no-full non-lobe components and proves their joint snapshot is constant over
the support interval.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Concatenated cells. -/
def frozenComponentCells {lo hi : Nat} :
    List (CoreComponentInterval m e r0 lo hi) → List Nat
  | [] => []
  | comp :: rest => comp.cells ++ frozenComponentCells rest

/-- Every component starts with no represented full edge. -/
def FrozenComponentsNoFull {lo hi : Nat}
    (comps : List (CoreComponentInterval m e r0 lo hi)) : Prop :=
  ∀ comp ∈ comps, ∀ s ∈ comp.edges,
    ¬ Full m e r0 lo s

/-- Every cell in every component is non-lobed. -/
def FrozenComponentsNoLobe {lo hi : Nat}
    (comps : List (CoreComponentInterval m e r0 lo hi)) : Prop :=
  ∀ comp ∈ comps, ∀ c ∈ comp.cells, CoreNoLobe m c

/-- Joint prefix snapshot equals the left-end snapshot. -/
theorem frozenComponentList_snap_prefix
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (comps : List (CoreComponentInterval m e r0 lo hi))
    (hnfull : FrozenComponentsNoFull m e r0 lo comps)
    (hnlobe : FrozenComponentsNoLobe m e r0 comps) :
    ∀ d, lo+d ≤ hi →
      snap m e r0 (frozenComponentCells comps) (lo+d) =
        snap m e r0 (frozenComponentCells comps) lo := by
  intro d hbound
  induction comps with
  | nil => rfl
  | cons comp rest ih =>
      have hcompNoFull : ∀ s ∈ comp.edges,
          ¬ Full m e r0 lo s :=
        hnfull comp List.mem_cons_self
      have hcompNoLobe : ∀ c ∈ comp.cells, CoreNoLobe m c :=
        hnlobe comp List.mem_cons_self
      have hrestNoFull : FrozenComponentsNoFull m e r0 lo rest := by
        intro c hc
        exact hnfull c (List.mem_cons_of_mem _ hc)
      have hrestNoLobe : FrozenComponentsNoLobe m e r0 rest := by
        intro c hc
        exact hnlobe c (List.mem_cons_of_mem _ hc)
      have hc := component_snap_prefix m e r0 hrun hr0
        comp hcompNoFull hcompNoLobe d hbound
      have hr := ih hrestNoFull hrestNoLobe
      unfold snap frozenComponentCells at hc hr ⊢
      simp only [List.map_append]
      rw [hc, hr]

/-- Joint block constancy between arbitrary interval times. -/
theorem frozenComponentList_constant
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (comps : List (CoreComponentInterval m e r0 lo hi))
    (hnfull : FrozenComponentsNoFull m e r0 lo comps)
    (hnlobe : FrozenComponentsNoLobe m e r0 comps)
    {i j : Nat}
    (hiLo : lo ≤ i) (hiHi : i ≤ hi)
    (hjLo : lo ≤ j) (hjHi : j ≤ hi) :
    snap m e r0 (frozenComponentCells comps) i =
      snap m e r0 (frozenComponentCells comps) j := by
  have hiEq := frozenComponentList_snap_prefix m e r0 hrun hr0
    comps hnfull hnlobe (i-lo) (by omega)
  have hjEq := frozenComponentList_snap_prefix m e r0 hrun hr0
    comps hnfull hnlobe (j-lo) (by omega)
  have hiNorm : lo + (i-lo) = i := by omega
  have hjNorm : lo + (j-lo) = j := by omega
  rw [hiNorm] at hiEq
  rw [hjNorm] at hjEq
  exact hiEq.trans hjEq.symm

end Echo
