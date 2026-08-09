import ExternalLobeReflectionCore

/-!
# A fully externally lobed support component is a trap

Suppose a finite support component has these two properties from some time
onward:

* the jump edge selected by every component cell remains inside the component;
* the mouth partner of every component cell carries an occupied lobe edge.

Then every visit to the component is reflected twice and returns to the same
support entry after four echo steps.  Iterating gives an absorbing component
orbit.  Therefore any pre-tail *variable* tree component must contain at least
one cell whose mouth partner is not an active occupied lobe root—the reserved
cell used by the `2/3` counting theorem.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Every selected support edge of a listed cell stays inside the component. -/
def SelectedClosedFrom (cells : List Nat) (lo : Nat) : Prop :=
  ∀ k, lo ≤ k → ∀ c ∈ cells,
    m.cellOf (m.bar (reg m e r0 k c)) ∈ cells

/-- Every listed cell has an occupied lobe in its mouth partner. -/
def FullyExternallyLobedFrom (cells : List Nat) (lo : Nat) : Prop :=
  ∀ k, lo ≤ k → ∀ c ∈ cells,
    OccupiedLobeAt m e r0 k (m.star c)

/-- A visit to a fully externally lobed, selected-edge-closed component makes
a four-step roundtrip. -/
theorem fully_lobed_component_roundtrip
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {lo k : Nat}
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hlobed : FullyExternallyLobedFrom m e r0 cells lo)
    (hk : lo ≤ k)
    (hentry : m.cellOf (e k) ∈ cells) :
    e (k+2) = m.bar (e k) ∧ e (k+4) = e k := by
  have hfirst : OccupiedLobeAt m e r0 k
      (m.star (m.cellOf (e k))) :=
    hlobed k hk (m.cellOf (e k)) hentry
  have hl1 := next_lobe_of_occupied_partner m e r0 hrun hfirst
  have hreflect := lobe_entry_reflects m e r0 hrun hr0 hl1
  have hwrite : reg m e r0 k (m.cellOf (e k)) = e k :=
    reg_write m e r0 rfl
  have hnextCell : m.cellOf (e (k+2)) ∈ cells := by
    rw [hreflect]
    have hc := hclosed k hk (m.cellOf (e k)) hentry
    rwa [hwrite] at hc
  have hsecond : OccupiedLobeAt m e r0 (k+2)
      (m.star (m.cellOf (e (k+2)))) :=
    hlobed (k+2) (by omega)
      (m.cellOf (e (k+2))) hnextCell
  have hround := two_occupied_external_lobes_roundtrip
    m e r0 hrun hr0 hfirst hsecond
  exact hround

/-- The same support entry recurs every four steps. -/
theorem fully_lobed_component_orbit
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {lo k : Nat}
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hlobed : FullyExternallyLobedFrom m e r0 cells lo)
    (hk : lo ≤ k)
    (hentry : m.cellOf (e k) ∈ cells) :
    ∀ n, e (k + 4*n) = e k := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      let q := k + 4*n
      have hq : lo ≤ q := by
        dsimp [q]
        omega
      have hqEntry : m.cellOf (e q) ∈ cells := by
        rw [ih]
        exact hentry
      have hround := fully_lobed_component_roundtrip
        m e r0 hrun hr0 cells hclosed hlobed hq hqEntry
      have hidx : q+4 = k + 4*(n+1) := by
        dsimp [q]
        omega
      rw [← hidx, hround.2]
      exact ih

/-- A convenient contradiction form: a trajectory which never returns to its
starting entry cannot be visiting a fully externally lobed closed component. -/
theorem not_fully_lobed_of_no_four_return
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {lo k : Nat}
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hk : lo ≤ k)
    (hentry : m.cellOf (e k) ∈ cells)
    (hnoReturn : e (k+4) ≠ e k) :
    ¬ FullyExternallyLobedFrom m e r0 cells lo := by
  intro hlubed
  exact hnoReturn
    (fully_lobed_component_roundtrip m e r0 hrun hr0
      cells hclosed hlubed hk hentry).2

end Echo
