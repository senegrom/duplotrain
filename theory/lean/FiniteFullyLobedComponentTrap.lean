import ExternalLobeReflectionCore

/-!
# Finite-interval fully lobed component trap

For the fixed-support epoch argument we only know closure and lobe occupancy on
a finite interval `[I,J]`.  That is sufficient.  Every four-step block whose
endpoint remains in the interval returns to the same support entry, and the
identity iterates for all such blocks.

This finite formulation is directly compatible with canonical support epochs
and removes the unnecessarily global hypotheses of the first reserve draft.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Selected support edges stay in the component throughout `[I,J]`. -/
def SelectedClosedOn
    (cells : List Nat) (I J : Nat) : Prop :=
  ∀ k, I ≤ k → k ≤ J → ∀ c ∈ cells,
    m.cellOf (m.bar (reg m e r0 k c)) ∈ cells

/-- Every component cell has an occupied lobe at its mouth partner throughout
`[I,J]`. -/
def FullyExternallyLobedOn
    (cells : List Nat) (I J : Nat) : Prop :=
  ∀ k, I ≤ k → k ≤ J → ∀ c ∈ cells,
    OccupiedLobeAt m e r0 k (m.star c)

/-- The support entry at `k` returns every four steps for all phases remaining
inside the right endpoint. -/
def FourReturnOrbitOn (k J : Nat) : Prop :=
  ∀ n, k + 4*n ≤ J → e (k + 4*n) = e k

/-- One finite four-step roundtrip. -/
theorem fully_lobed_component_roundtrip_on
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {I J k : Nat}
    (hclosed : SelectedClosedOn m e r0 cells I J)
    (hlobed : FullyExternallyLobedOn m e r0 cells I J)
    (hkI : I ≤ k) (hk4J : k+4 ≤ J)
    (hentry : m.cellOf (e k) ∈ cells) :
    e (k+2) = m.bar (e k) ∧ e (k+4) = e k := by
  have hkJ : k ≤ J := by omega
  have hfirst : OccupiedLobeAt m e r0 k
      (m.star (m.cellOf (e k))) :=
    hlubed k hkI hkJ (m.cellOf (e k)) hentry
  have hl1 := next_lobe_of_occupied_partner m e r0 hrun hfirst
  have hreflect := lobe_entry_reflects m e r0 hrun hr0 hl1
  have hwrite : reg m e r0 k (m.cellOf (e k)) = e k :=
    reg_write m e r0 rfl
  have hnextCell : m.cellOf (e (k+2)) ∈ cells := by
    rw [hreflect]
    have hc := hclosed k hkI hkJ (m.cellOf (e k)) hentry
    rwa [hwrite] at hc
  have hsecond : OccupiedLobeAt m e r0 (k+2)
      (m.star (m.cellOf (e (k+2)))) :=
    hlubed (k+2) (by omega) (by omega)
      (m.cellOf (e (k+2))) hnextCell
  exact two_occupied_external_lobes_roundtrip
    m e r0 hrun hr0 hfirst hsecond

/-- **Finite fully-lobed component orbit.** -/
theorem fully_lobed_component_orbit_on
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {I J k : Nat}
    (hclosed : SelectedClosedOn m e r0 cells I J)
    (hlobed : FullyExternallyLobedOn m e r0 cells I J)
    (hkI : I ≤ k) (hkJ : k ≤ J)
    (hentry : m.cellOf (e k) ∈ cells) :
    FourReturnOrbitOn e k J := by
  intro n hbound
  induction n with
  | zero => rfl
  | succ n ih =>
      let q := k + 4*n
      have hqI : I ≤ q := by
        dsimp [q]
        omega
      have hq4J : q+4 ≤ J := by
        dsimp [q]
        omega
      have hqEntry : m.cellOf (e q) ∈ cells := by
        have hi := ih (by omega)
        rw [hi]
        exact hentry
      have hround := fully_lobed_component_roundtrip_on
        m e r0 hrun hr0 cells hclosed hlubed hqI hq4J hqEntry
      have hidx : q+4 = k + 4*(n+1) := by
        dsimp [q]
        omega
      calc
        e (k + 4*(n+1)) = e (q+4) := by rw [hidx]
        _ = e q := hround.2
        _ = e k := ih (by omega)

/-- The component is visited during the closed interval. -/
def ComponentVisitedOn
    (cells : List Nat) (I J : Nat) : Prop :=
  ∃ k, I ≤ k ∧ k ≤ J ∧ m.cellOf (e k) ∈ cells

/-- No component visit in `[I,J]` starts the finite four-return orbit. -/
def NoFourReturnComponentTailOn
    (cells : List Nat) (I J : Nat) : Prop :=
  ∀ k, I ≤ k → k ≤ J → m.cellOf (e k) ∈ cells →
    ¬ FourReturnOrbitOn e k J

/-- **Finite reserved-cell existence.** -/
theorem exists_unreflected_component_cell_on
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) (I J : Nat)
    (hclosed : SelectedClosedOn m e r0 cells I J)
    (hvisit : ComponentVisitedOn m e cells I J)
    (hnoTail : NoFourReturnComponentTailOn m e cells I J) :
    ∃ c, c ∈ cells ∧
      ∃ j, I ≤ j ∧ j ≤ J ∧
        ¬ OccupiedLobeAt m e r0 j (m.star c) := by
  classical
  by_contra hnone
  have hall : FullyExternallyLobedOn m e r0 cells I J := by
    intro j hjI hjJ c hc
    by_contra hnot
    apply hnone
    exact ⟨c, hc, j, hjI, hjJ, hnot⟩
  rcases hvisit with ⟨k, hkI, hkJ, hentry⟩
  have horbit := fully_lobed_component_orbit_on
    m e r0 hrun hr0 cells hclosed hall hkI hkJ hentry
  exact (hnoTail k hkI hkJ hentry) horbit

/-- Active roots persistent on a finite interval. -/
def PersistentActiveLobeRootsOn
    (roots : List Nat) (I J : Nat) : Prop :=
  ∀ c ∈ roots,
    ∃ a,
      m.cellOf a = c ∧
      m.cellOf (m.bar a) = m.cellOf a ∧
      ∀ j, I ≤ j → j ≤ J → Occupied m e r0 j a

/-- A finite unreflected witness excludes an active-root partner. -/
theorem unreflected_on_not_active_partner
    (roots : List Nat) (I J c j : Nat)
    (hactive : PersistentActiveLobeRootsOn m e r0 roots I J)
    (hjI : I ≤ j) (hjJ : j ≤ J)
    (hunreflected :
      ¬ OccupiedLobeAt m e r0 j (m.star c)) :
    m.star c ∉ roots := by
  intro hmem
  rcases hactive (m.star c) hmem with
    ⟨a, haCell, haLobe, haOcc⟩
  apply hunreflected
  exact ⟨a, haCell, haLobe, haOcc j hjI hjJ⟩

/-- **Finite one-reserve semantic theorem.** -/
theorem exists_component_reserve_on
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells roots : List Nat) (I J : Nat)
    (hclosed : SelectedClosedOn m e r0 cells I J)
    (hvisit : ComponentVisitedOn m e cells I J)
    (hnoTail : NoFourReturnComponentTailOn m e cells I J)
    (hactive : PersistentActiveLobeRootsOn m e r0 roots I J) :
    ∃ c, c ∈ cells ∧ m.star c ∉ roots := by
  rcases exists_unreflected_component_cell_on m e r0
      hrun hr0 cells I J hclosed hvisit hnoTail with
    ⟨c, hc, j, hjI, hjJ, hunreflected⟩
  exact ⟨c, hc,
    unreflected_on_not_active_partner m e r0
      roots I J c j hactive hjI hjJ hunreflected⟩

end Echo
