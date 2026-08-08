import NoFullComponentFreezeCore

/-!
# Finite lists of no-full components form one frozen block

Each represented no-full non-lobe component has its initial snapshot throughout
the fixed-support interval.  Concatenating finitely many such components gives
the `FrozenOn` block used by the complete epoch code.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Concatenated cells of a component list. -/
def coreComponentCells {lo hi : Nat} :
    List (CoreComponentInterval m e r0 lo hi) → List Nat
  | [] => []
  | comp :: rest => comp.cells ++ coreComponentCells rest

/-- Every component in the list starts with no full edge. -/
def ComponentsNoFullAtLeft {lo hi : Nat}
    (comps : List (CoreComponentInterval m e r0 lo hi)) : Prop :=
  ∀ comp ∈ comps, ∀ s ∈ comp.edges,
    ¬ Full m e r0 lo s

/-- Every listed component cell is non-lobed. -/
def ComponentsNoLobe {lo hi : Nat}
    (comps : List (CoreComponentInterval m e r0 lo hi)) : Prop :=
  ∀ comp ∈ comps, ∀ c ∈ comp.cells, CoreNoLobe m c

/-- Concatenated snapshot at any prefix equals the left-end snapshot. -/
theorem componentList_snap_prefix
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (comps : List (CoreComponentInterval m e r0 lo hi))
    (hnfull : ComponentsNoFullAtLeft m e r0 lo comps)
    (hnlobe : ComponentsNoLobe m lo comps) :
    ∀ d, lo+d ≤ hi →
      snap m e r0 (coreComponentCells comps) (lo+d) =
        snap m e r0 (coreComponentCells comps) lo := by
  intro d hbound
  induction comps with
  | nil => rfl
  | cons comp rest ih =>
      have hcompNoFull : ∀ s ∈ comp.edges,
          ¬ Full m e r0 lo s :=
        hnfull comp List.mem_cons_self
      have hcompNoLobe : ∀ c ∈ comp.cells, CoreNoLobe m c :=
        hnlobe comp List.mem_cons_self
      have hrestNoFull : ComponentsNoFullAtLeft m e r0 lo rest := by
        intro c hc
        exact hnfull c (List.mem_cons_of_mem _ hc)
      have hrestNoLobe : ComponentsNoLobe m lo rest := by
        intro c hc
        exact hnlobe c (List.mem_cons_of_mem _ hc)
      have hc := component_snap_prefix m e r0 hrun hr0
        comp hcompNoFull hcompNoLobe d hbound
      have hr := ih hrestNoFull hrestNoLobe
      unfold snap coreComponentCells at hc hr ⊢
      simp only [List.map_append]
      rw [hc, hr]

/-- The concatenated residual block is frozen on the interval. -/
theorem componentList_frozenOn
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {lo hi : Nat}
    (comps : List (CoreComponentInterval m e r0 lo hi))
    (hnfull : ComponentsNoFullAtLeft m e r0 lo comps)
    (hnlobe : ComponentsNoLobe m lo comps) :
    ∀ i, lo ≤ i → i ≤ hi → ∀ j, lo ≤ j → j ≤ hi,
      snap m e r0 (coreComponentCells comps) i =
        snap m e r0 (coreComponentCells comps) j := by
  intro i hiLo hiHi j hjLo hjHi
  have hiEq := componentList_snap_prefix m e r0 hrun hr0
    comps hnfull hnlobe (i-lo) (by omega)
  have hjEq := componentList_snap_prefix m e r0 hrun hr0
    comps hnfull hnlobe (j-lo) (by omega)
  have hiNorm : lo + (i-lo) = i := by omega
  have hjNorm : lo + (j-lo) = j := by omega
  rw [hiNorm] at hiEq
  rw [hjNorm] at hjEq
  exact hiEq.trans hjEq.symm

end Echo
