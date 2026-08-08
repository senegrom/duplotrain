import EndpointAccountingCore

/-!
# Before absorption, persistent active lobes are star-separated

The lobe dichotomy already proves that a star-paired persistent pair creates a
four-slot tail.  This file packages the contrapositive in the form needed by
fixed-support epoch construction.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- A four-slot tail starts at time `k`. -/
def HasFourTailFrom (k : Nat) : Prop :=
  ∃ a b, ∀ j, k ≤ j →
    e j = a ∨ e j = m.bar a ∨
    e j = b ∨ e j = m.bar b

/-- No four-slot tail begins at or before `hi` while staying after `lo`. -/
def NoFourTailIn (lo hi : Nat) : Prop :=
  ∀ k, lo ≤ k → k ≤ hi → ¬ HasFourTailFrom m e r0 k

/-- Persistent lobe witnesses are star-separated before absorption. -/
theorem persistent_lobes_starSeparated
    (hrun : IsRun m e r0)
    (lo hi : Nat) (active : List Nat)
    (hnd : active.Nodup)
    (hwit : ∀ c ∈ active,
      PersistentLobeWitness m e r0 lo hi c)
    (hno : NoFourTailIn m e r0 lo hi) :
    StarSeparated m active := by
  rcases persistent_lobes_separated_or_absorb m e r0 hrun
      lo hi active hnd hwit with hsep | habs
  · exact hsep
  · rcases habs with
      ⟨c, k, a, b, hc, hsc, hlo, hhi, htail⟩
    exact absurd ⟨a, b, htail⟩ (hno k hlo hhi)

/-- Quantitative half-density before absorption. -/
theorem persistent_lobes_half
    (hrun : IsRun m e r0)
    (lo hi : Nat) (active cells : List Nat)
    (hnd : active.Nodup)
    (hcells : cells.Nodup)
    (hcover : ∀ c ∈ active,
      c ∈ cells ∧ m.star c ∈ cells)
    (hwit : ∀ c ∈ active,
      PersistentLobeWitness m e r0 lo hi c)
    (hno : NoFourTailIn m e r0 lo hi) :
    2 * active.length ≤ cells.length := by
  exact starSeparated_count m active cells
    (persistent_lobes_starSeparated m e r0 hrun
      lo hi active hnd hwit hno)
    hcells hcover

end Echo
