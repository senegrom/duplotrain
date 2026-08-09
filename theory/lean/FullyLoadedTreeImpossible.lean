import TwoReflectorFiniteTrap
import LobeVariationVisit
import SupportWeightFibres

/-!
# A nontrivial tree component cannot be fully loaded by active lobes

For every cell `c` of an ordinary fixed-support tree component, suppose its
mouth partner `star c` is the root of a persistent occupied lobe component
whose root register varies on `[I,J]`.  Each such variation forces an actual
visit to `c`.

Choose the earliest component-cell visit.  The occupied lobe opposite that
cell reflects the walk across its current support edge.  If the far endpoint
is loaded too, the two-reflector theorem traps every remaining entry on those
two support cells and the two external lobe cells.  A third tree cell can
therefore never receive the partner visit required by its varying lobe.

Thus any ordinary tree component with at least three cells has an unloaded
cell.  This is the missing local dynamical statement behind the conditional
`2/3` bound in `TreeLobeNotFullTwoThirds.lean`.
-/

namespace Echo

private theorem nodup_subset_length_loaded
    {xs ys : List Nat}
    (hnd : xs.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons x rest ih =>
      rw [List.nodup_cons] at hnd
      have hx : x ∈ ys := hsub x List.mem_cons_self
      have hsub' : ∀ y ∈ rest, y ∈ ys.erase x := by
        intro y hy
        have hyS := hsub y (List.mem_cons_of_mem _ hy)
        have hyx : y ≠ x := fun h => hnd.1 (h ▸ hy)
        exact (List.mem_erase_of_ne hyx).mpr hyS
      have hle := ih hnd.2 hsub'
      rw [List.length_erase_of_mem hx] at hle
      simp only [List.length_cons]
      omega

private theorem exists_third_cell
    (cells : List Nat) (hnd : cells.Nodup)
    (hlen : 3 ≤ cells.length)
    {c d : Nat} (hc : c ∈ cells) (hd : d ∈ cells)
    (hcd : c ≠ d) :
    ∃ z, z ∈ cells ∧ z ≠ c ∧ z ≠ d := by
  apply Classical.byContradiction
  intro hnone
  have hsub : ∀ z ∈ cells, z ∈ [c,d] := by
    intro z hz
    by_cases hzc : z = c
    · simp [hzc]
    by_cases hzd : z = d
    · simp [hzd]
    exfalso
    apply hnone
    exact ⟨z, hz, hzc, hzd⟩
  have hle := nodup_subset_length_loaded hnd hsub
  simp at hle
  omega

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Data saying that the mouth partner of `c` is a persistent active external
lobe. -/
def LoadedByActiveLobe
    (I J : Nat) (cells : List Nat) (c : Nat) : Prop :=
  ∃ a,
    m.cellOf a = m.star c ∧
    m.cellOf (m.bar a) = m.cellOf a ∧
    (∀ k, I ≤ k → k ≤ J → Occupied m e r0 k a) ∧
    VariesOnInterval m e r0 I J (m.cellOf a) ∧
    m.cellOf a ∉ cells

/-- **Fully-loaded tree contradiction.**

`selectedTarget` and `selectedNonlobe` are exactly the two local properties
provided by `SupportTreeEpoch.selected_target_mem` and
`SupportTreeEpoch.selected_nonlobe`. -/
theorem fully_loaded_tree_impossible
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (I J : Nat) (cells : List Nat)
    (hcellsNodup : cells.Nodup)
    (hsize : 3 ≤ cells.length)
    (hselectedTarget : ∀ k, I ≤ k → k ≤ J →
      ∀ c ∈ cells,
        m.cellOf (m.bar (reg m e r0 k c)) ∈ cells)
    (hselectedNonlobe : ∀ k, I ≤ k → k ≤ J →
      ∀ c ∈ cells, ¬ LobeSlot m (reg m e r0 k c))
    (hload : ∀ c ∈ cells,
      LoadedByActiveLobe m e r0 I J cells c) : False := by
  classical
  obtain ⟨seed, hseed⟩ : ∃ c, c ∈ cells := by
    cases hc : cells with
    | nil =>
        rw [hc] at hsize
        simp at hsize
    | cons c rest =>
        exact ⟨c, by rw [hc]; exact List.mem_cons_self⟩
  rcases hload seed hseed with
    ⟨seedLobe, hseedRoot, hseedLoop,
      hseedOcc, hseedVar, hseedOut⟩
  obtain ⟨w, hwI, hwJ, hwPartner⟩ :=
    varying_occupied_lobe_has_partner_visit
      m e r0 hrun hr0 hseedLoop hseedOcc hseedVar
  have hwCell : m.cellOf (e w) = seed := by
    calc
      m.cellOf (e w) = m.star (m.cellOf seedLobe) := hwPartner
      _ = m.star (m.star seed) := by rw [hseedRoot]
      _ = seed := m.star_invol seed
  let candidates := (List.range J).filter fun k =>
    decide (I ≤ k ∧ m.cellOf (e k) ∈ cells)
  have hwCandidate : w ∈ candidates := by
    dsimp [candidates]
    exact List.mem_filter.mpr
      ⟨List.mem_range.mpr hwJ,
        decide_eq_true ⟨hwI, hwCell ▸ hseed⟩⟩
  cases hcandidates : candidates with
  | nil =>
      rw [hcandidates] at hwCandidate
      cases hwCandidate
  | cons first rest =>
      let k0 := fibreMinFrom first rest
      have hk0Candidate : k0 ∈ candidates := by
        rw [hcandidates]
        exact fibreMinFrom_mem first rest
      have hk0Filter :
          k0 ∈ (List.range J).filter (fun k =>
            decide (I ≤ k ∧ m.cellOf (e k) ∈ cells)) := by
        simpa only [candidates] using hk0Candidate
      have hk0Data := List.mem_filter.mp hk0Filter
      have hk0J : k0 < J := List.mem_range.mp hk0Data.1
      have hk0Cond : I ≤ k0 ∧ m.cellOf (e k0) ∈ cells :=
        of_decide_eq_true hk0Data.2
      have hk0I : I ≤ k0 := hk0Cond.1
      have hk0Cell : m.cellOf (e k0) ∈ cells := hk0Cond.2
      have hk0Min : ∀ q, q ∈ candidates → k0 ≤ q := by
        intro q hq
        have hqList : q ∈ first :: rest := by
          rw [← hcandidates]
          exact hq
        dsimp [k0]
        exact fibreMinFrom_le_mem first rest q hqList
      let c := m.cellOf (e k0)
      have hc : c ∈ cells := by
        simpa only [c] using hk0Cell
      rcases hload c hc with
        ⟨a, haRoot, haLoop, haOcc, haVar, haOut⟩
      have haPartner : m.cellOf (e k0) =
          m.star (m.cellOf a) := by
        have h := congrArg m.star haRoot
        rw [m.star_invol] at h
        exact h.symm
      let d := m.cellOf (m.bar (e k0))
      have hreg : reg m e r0 k0 c = e k0 := by
        dsimp [c]
        exact reg_write m e r0 rfl
      have hd : d ∈ cells := by
        have ht := hselectedTarget k0 hk0I (by omega) c hc
        rw [hreg] at ht
        simpa only [d] using ht
      have hcd : c ≠ d := by
        intro h
        have hlobe : LobeSlot m (reg m e r0 k0 c) := by
          unfold LobeSlot
          rw [hreg]
          simpa only [c, d] using h.symm
        exact (hselectedNonlobe k0 hk0I (by omega) c hc) hlobe
      rcases hload d hd with
        ⟨b, hbRoot, hbLoop, hbOcc, hbVar, hbOut⟩
      have hbPartner : m.cellOf (m.bar (e k0)) =
          m.star (m.cellOf b) := by
        have h := congrArg m.star hbRoot
        rw [m.star_invol] at h
        simpa only [d] using h.symm
      have htrap := two_reflector_edge_entries_until
        m e r0 hrun (k := k0) (J := J)
        (x := e k0) (a := a) (b := b)
        rfl haLoop haPartner hbLoop hbPartner
        (fun q hq0 hqJ => haOcc q (Nat.le_trans hk0I hq0) hqJ)
        (fun q hq0 hqJ => hbOcc q (Nat.le_trans hk0I hq0) hqJ)
      obtain ⟨z, hz, hzc, hzd⟩ :=
        exists_third_cell cells hcellsNodup hsize hc hd hcd
      rcases hload z hz with
        ⟨g, hgRoot, hgLoop, hgOcc, hgVar, hgOut⟩
      obtain ⟨q, hqI, hqJ, hqPartner⟩ :=
        varying_occupied_lobe_has_partner_visit
          m e r0 hrun hr0 hgLoop hgOcc hgVar
      have hqCell : m.cellOf (e q) = z := by
        calc
          m.cellOf (e q) = m.star (m.cellOf g) := hqPartner
          _ = m.star (m.star z) := by rw [hgRoot]
          _ = z := m.star_invol z
      have hqCandidate : q ∈ candidates := by
        dsimp [candidates]
        exact List.mem_filter.mpr
          ⟨List.mem_range.mpr hqJ,
            decide_eq_true ⟨hqI, hqCell ▸ hz⟩⟩
      have hk0q : k0 ≤ q := hk0Min q hqCandidate
      have hqTrap := htrap q hk0q (by omega)
      rcases hqTrap with hqx | hqbarx | hqa | hqbara | hqb | hqbarb
      · apply hzc
        calc
          z = m.cellOf (e q) := hqCell.symm
          _ = m.cellOf (e k0) := by rw [hqx]
          _ = c := rfl
      · apply hzd
        calc
          z = m.cellOf (e q) := hqCell.symm
          _ = m.cellOf (m.bar (e k0)) := by rw [hqbarx]
          _ = d := rfl
      · apply haOut
        have hcell : m.cellOf a = z := by
          calc
            m.cellOf a = m.cellOf (e q) := by rw [hqa]
            _ = z := hqCell
        rw [hcell]
        exact hz
      · apply haOut
        have hcell : m.cellOf a = z := by
          calc
            m.cellOf a = m.cellOf (m.bar a) := haLoop.symm
            _ = m.cellOf (e q) := by rw [hqbara]
            _ = z := hqCell
        rw [hcell]
        exact hz
      · apply hbOut
        have hcell : m.cellOf b = z := by
          calc
            m.cellOf b = m.cellOf (e q) := by rw [hqb]
            _ = z := hqCell
        rw [hcell]
        exact hz
      · apply hbOut
        have hcell : m.cellOf b = z := by
          calc
            m.cellOf b = m.cellOf (m.bar b) := hbLoop.symm
            _ = m.cellOf (e q) := by rw [hqbarb]
            _ = z := hqCell
        rw [hcell]
        exact hz

end Echo
