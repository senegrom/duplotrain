import FullyLobedComponentTrap

/-!
# A visited pre-tail component has an unreflected reserve cell

`FullyLobedComponentTrap` proves that if every cell of a selected-edge-closed
support component has an occupied lobe at its mouth partner, every visit starts
a four-step return orbit.  Taking the contrapositive gives the semantic input
for the `2/3` bound:

> in a visited component before such a tail, some cell's mouth partner fails
> to carry an occupied lobe at some time.

Any persistent active-lobe root is occupied throughout the support epoch.
Therefore the witness cell cannot be the mouth partner of an active lobe root;
it is exactly the extra reserved cell needed by the counting argument.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- The support entry at `k` recurs every four echo steps. -/
def FourReturnOrbitAt (k : Nat) : Prop :=
  ∀ n, e (k + 4*n) = e k

/-- No visit to the listed component from `lo` starts a four-return orbit. -/
def NoFourReturnComponentTailFrom
    (cells : List Nat) (lo : Nat) : Prop :=
  ∀ k, lo ≤ k → m.cellOf (e k) ∈ cells →
    ¬ FourReturnOrbitAt e k

/-- The component is actually visited from `lo`. -/
def ComponentVisitedFrom (cells : List Nat) (lo : Nat) : Prop :=
  ∃ k, lo ≤ k ∧ m.cellOf (e k) ∈ cells

/-- **Reserved-cell existence.**  A visited, selected-edge-closed component
with no four-return tail contains a cell whose mouth partner is not externally
lobed at some later time. -/
theorem exists_unreflected_component_cell
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) (lo : Nat)
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hvisit : ComponentVisitedFrom m e cells lo)
    (hnoTail : NoFourReturnComponentTailFrom m e cells lo) :
    ∃ c, c ∈ cells ∧
      ∃ j, lo ≤ j ∧
        ¬ OccupiedLobeAt m e r0 j (m.star c) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hall : FullyExternallyLobedFrom m e r0 cells lo := by
    intro j hj c hc
    apply Classical.byContradiction
    intro hnot
    apply hnone
    exact ⟨c, hc, j, hj, hnot⟩
  rcases hvisit with ⟨k, hk, hentry⟩
  have horbit : FourReturnOrbitAt e k :=
    fully_lobed_component_orbit m e r0 hrun hr0
      cells hclosed hall hk hentry
  exact (hnoTail k hk hentry) horbit

/-- A finite list of persistent active lobe roots.  Each listed cell has a
named lobe edge which stays occupied from `lo` onward. -/
def PersistentActiveLobeRoots
    (roots : List Nat) (lo : Nat) : Prop :=
  ∀ c ∈ roots,
    ∃ a,
      m.cellOf a = c ∧
      m.cellOf (m.bar a) = m.cellOf a ∧
      ∀ j, lo ≤ j → Occupied m e r0 j a

/-- A cell whose mouth partner fails to carry an occupied lobe at one time
cannot be the mouth partner of a persistent active lobe root. -/
theorem unreflected_not_active_partner
    (roots : List Nat) (lo c j : Nat)
    (hactive : PersistentActiveLobeRoots m e r0 roots lo)
    (hj : lo ≤ j)
    (hunreflected :
      ¬ OccupiedLobeAt m e r0 j (m.star c)) :
    m.star c ∉ roots := by
  intro hmem
  rcases hactive (m.star c) hmem with
    ⟨a, haCell, haLobe, haOcc⟩
  apply hunreflected
  exact ⟨a, haCell, haLobe, haOcc j hj⟩

/-- **One-reserve semantic theorem.**  Every visited pre-tail component has a
cell which is not the mouth partner of any persistent active lobe root. -/
theorem exists_component_reserve_against_active_lobes
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells roots : List Nat) (lo : Nat)
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hvisit : ComponentVisitedFrom m e cells lo)
    (hnoTail : NoFourReturnComponentTailFrom m e cells lo)
    (hactive : PersistentActiveLobeRoots m e r0 roots lo) :
    ∃ c, c ∈ cells ∧ m.star c ∉ roots := by
  rcases exists_unreflected_component_cell m e r0
      hrun hr0 cells lo hclosed hvisit hnoTail with
    ⟨c, hc, j, hj, hunreflected⟩
  exact ⟨c, hc,
    unreflected_not_active_partner m e r0 roots lo c j
      hactive hj hunreflected⟩

end Echo
