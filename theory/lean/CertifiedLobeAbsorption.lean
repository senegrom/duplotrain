import PersistentLobeSeparationStandalone
import GrayTailCount

/-!
# Certified lobe absorption

The strict epoch argument only needs to exclude the exact event which destroys
half-density of active lobes: a visit to one occupied lobe while its mouth
partner also carries an occupied lobe.  At that instant the two lobe slots and
the partner register form precisely the certificate consumed by
`absorbed_snapshot_count`.

Using this exact certificate, rather than an arbitrary four-entry tail, gives
an exhaustive finite-interval dichotomy: either no certificate occurs, or a
first certificate occurs and every later complete snapshot belongs to a
four-state absorbed tail.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Exact data which initiates the already-proved two-lobe absorption. -/
def CertifiedLobeAbsorptionAt (k : Nat) : Prop :=
  ∃ a b,
    m.cellOf (m.bar a) = m.cellOf a ∧
    m.cellOf (m.bar b) = m.cellOf b ∧
    m.star (m.cellOf a) = m.cellOf b ∧
    e k = a ∧
    (reg m e r0 k (m.cellOf b) = b ∨
      reg m e r0 k (m.cellOf b) = m.bar b)

/-- No certified absorption begins in the closed interval. -/
def NoCertifiedLobeAbsorptionIn (lo hi : Nat) : Prop :=
  ∀ k, lo ≤ k → k ≤ hi →
    ¬ CertifiedLobeAbsorptionAt m e r0 k

/-- A certificate gives the standard four-entry absorbing tail. -/
theorem certifiedLobeAbsorption_entries
    (hrun : IsRun m e r0)
    {k : Nat}
    (hcert : CertifiedLobeAbsorptionAt m e r0 k) :
    StandaloneFourTailFrom m e r0 k := by
  rcases hcert with
    ⟨a, b, ha, hb, hAB, hstart, hreg⟩
  exact ⟨a, b, absorb_entries m e r0 hrun
    ha hb hAB hstart hreg⟩

/-- A certificate bounds every finite list of later complete snapshots by four. -/
theorem certifiedLobeAbsorption_snapshot_count
    (hrun : IsRun m e r0)
    {k : Nat}
    (hcert : CertifiedLobeAbsorptionAt m e r0 k)
    (cells ks : List Nat)
    (hks : ∀ j ∈ ks, k ≤ j)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ 4 := by
  rcases hcert with
    ⟨a, b, ha, hb, hAB, hstart, hreg⟩
  exact absorbed_snapshot_count m e r0 hrun
    ha hb hAB hstart hreg cells ks hks hnd

/-- A visited occupied lobe together with an occupied partner lobe produces
an exact absorption certificate at the visit time. -/
theorem visited_partner_lobes_certify
    {k a b : Nat}
    (ha : m.cellOf (m.bar a) = m.cellOf a)
    (hb : m.cellOf (m.bar b) = m.cellOf b)
    (hstar : m.star (m.cellOf a) = m.cellOf b)
    (hstart : e k = a)
    (hocc : Occupied m e r0 k b) :
    CertifiedLobeAbsorptionAt m e r0 k := by
  have hreg := standalone_occupied_lobe_cases m e r0 hb hocc
  exact ⟨a, b, ha, hb, hstar, hstart, hreg⟩

/-- **Before any certified absorption, active lobe cells are star-separated.** -/
theorem standaloneActiveLobes_starSeparated_noCertified
    (lo hi : Nat) (lobes : List Nat)
    (hnd : (standaloneActiveLobeCells m lobes).Nodup)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hvisit : ∀ a ∈ lobes,
      StandaloneLobeVisited m e r0 lo hi a)
    (hno : NoCertifiedLobeAbsorptionIn m e r0 lo hi) :
    StarSeparatedCore m (standaloneActiveLobeCells m lobes) := by
  constructor
  · exact hnd
  · intro c hc hstarMem
    obtain ⟨a, haMem, hac⟩ := List.mem_map.mp hc
    obtain ⟨b, hbMem, hbc⟩ := List.mem_map.mp hstarMem
    rcases hvisit a haMem with ⟨k, hkLo, hkHi, he | he⟩
    · have hstar : m.star (m.cellOf a) = m.cellOf b := by
        rw [hac, hbc]
      have hcert := visited_partner_lobes_certify m e r0
        (hloop a haMem) (hloop b hbMem) hstar he
        (hocc k hkLo hkHi b hbMem)
      exact (hno k hkLo hkHi) hcert
    · let a' := m.bar a
      have ha' : m.cellOf (m.bar a') = m.cellOf a' := by
        dsimp [a']
        rw [m.bar_invol]
        exact (hloop a haMem).symm
      have hcellA' : m.cellOf a' = m.cellOf a := by
        dsimp [a']
        exact hloop a haMem
      have hstar : m.star (m.cellOf a') = m.cellOf b := by
        rw [hcellA', hac, hbc]
      have hcert := visited_partner_lobes_certify m e r0
        ha' (hloop b hbMem) hstar he
        (hocc k hkLo hkHi b hbMem)
      exact (hno k hkLo hkHi) hcert

/-- Quantitative half-density under the exact no-certificate condition. -/
theorem standaloneActiveLobes_half_noCertified
    (lo hi : Nat) (lobes cells : List Nat)
    (hnd : (standaloneActiveLobeCells m lobes).Nodup)
    (hcells : cells.Nodup)
    (hclosed : ∀ c ∈ standaloneActiveLobeCells m lobes,
      c ∈ cells ∧ m.star c ∈ cells)
    (hloop : ∀ a ∈ lobes,
      m.cellOf (m.bar a) = m.cellOf a)
    (hocc : ∀ k, lo ≤ k → k ≤ hi → ∀ a ∈ lobes,
      Occupied m e r0 k a)
    (hvisit : ∀ a ∈ lobes,
      StandaloneLobeVisited m e r0 lo hi a)
    (hno : NoCertifiedLobeAbsorptionIn m e r0 lo hi) :
    2 * lobes.length ≤ cells.length := by
  have hsep := standaloneActiveLobes_starSeparated_noCertified
    m e r0 lo hi lobes hnd hloop hocc hvisit hno
  have hhalf := starSeparatedCore_count m
    (standaloneActiveLobeCells m lobes) cells
    hsep hcells hclosed
  simpa [standaloneActiveLobeCells] using hhalf

/-- Restrict the no-certificate property to a subinterval. -/
theorem noCertifiedLobeAbsorption_restrict
    {globalLo globalHi lo hi : Nat}
    (hno : NoCertifiedLobeAbsorptionIn m e r0
      globalLo globalHi)
    (hLo : globalLo ≤ lo) (hHi : hi ≤ globalHi) :
    NoCertifiedLobeAbsorptionIn m e r0 lo hi := by
  intro k hkLo hkHi hcert
  exact hno k (Nat.le_trans hLo hkLo)
    (Nat.le_trans hkHi hHi) hcert

end Echo
