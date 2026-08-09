import VisibleChipReduction
import CertifiedLobeAbsorption

/-!
# The two collapsed visible-chip geometries

`VisibleChipReduction` isolates two degeneracies of the external-reflector
configuration.  This file discharges both of them under the hypotheses from
which that configuration is extracted.

* If the support edge has both ends in one cell, that edge is itself a lobe.
  Together with the occupied lobe in its mouth partner, the current visit is
  an exact certified lobe absorption and hence has at most four later register
  snapshots.
* If the support edge directly joins mouth-partner cells, the geometry is
  impossible in a fully externally lobed closed component.  Two-step
  reflection leaves the original cell's register at the support endpoint,
  while external lobing of the reflected endpoint requires that same register
  to occupy an internal lobe.  Register uniqueness then says that the support
  edge was internal after all, contradicting the mouth-partner hypothesis.

The recurrence transport lemmas at the beginning promote a four-snapshot
bound beginning at a later visit back to the start of an exact recurrent
tail.  No finiteness, small-machine, or enumeration assumption is used.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Exact register recurrence may be iterated through any number of periods. -/
theorem exactRecurrentTail_reg_add_mul
    {K q t : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (ht : K ≤ t) :
    ∀ n c, reg m e r0 (t + n*q) c = reg m e r0 t c := by
  intro n
  induction n with
  | zero =>
      intro c
      simp
  | succ n ih =>
      intro c
      have hidx : t + (n+1)*q = (t + n*q) + q := by
        simp only [Nat.succ_mul]
        omega
      rw [hidx, hrec.2.2 (t + n*q) c (by omega)]
      exact ih c

/-- Snapshot form of iterated exact recurrence. -/
theorem exactRecurrentTail_snap_add_mul
    {K q t : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (ht : K ≤ t)
    (cells : List Nat) :
    ∀ n, snap m e r0 cells (t + n*q) = snap m e r0 cells t := by
  intro n
  unfold snap
  apply List.map_congr_left
  intro c _
  exact exactRecurrentTail_reg_add_mul m e r0 hrec ht n c

private theorem le_add_mul_of_pos (j k q : Nat) (hq : 0 < q) :
    k ≤ j + k*q := by
  induction k with
  | zero => omega
  | succ k ih =>
      rw [Nat.succ_mul]
      omega

/-- A four-snapshot bound beginning anywhere on an exact recurrent tail also
holds from the original tail start.  Every earlier sample is shifted forward
by `k` whole periods, without changing its snapshot. -/
theorem fourSnapshotTail_pullback_recurrent
    {K q k : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (_hKk : K ≤ k)
    (htail : FourSnapshotTail m e r0 k) :
    FourSnapshotTail m e r0 K := by
  intro cells ks hks hnd
  let shifted := ks.map (fun j => j + k*q)
  have hshifted : ∀ j ∈ shifted, k ≤ j := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
    exact le_add_mul_of_pos t k q hrec.1
  have hmaps : shifted.map (snap m e r0 cells) =
      ks.map (snap m e r0 cells) := by
    dsimp [shifted]
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    exact exactRecurrentTail_snap_add_mul m e r0 hrec
      (hks j hj) cells k
  have hnd' : (shifted.map (snap m e r0 cells)).Nodup := by
    rw [hmaps]
    exact hnd
  have hle := htail cells shifted hshifted hnd'
  simpa [shifted] using hle

/-- Same-cell collapse is exactly a certified two-lobe absorption: the
support edge is one lobe and the occupied edge in its mouth partner is the
other. -/
theorem same_cell_collapse_certifies_absorption
    {k x : Nat}
    (hstart : e k = x)
    (hcollapse : m.cellOf (m.bar x) = m.cellOf x)
    (hpartner : OccupiedLobeAt m e r0 k
      (m.star (m.cellOf x))) :
    CertifiedLobeAbsorptionAt m e r0 k := by
  rcases hpartner with ⟨b, hbCell, hbLobe, hbOcc⟩
  exact visited_partner_lobes_certify m e r0
    hcollapse hbLobe hbCell.symm hstart hbOcc

/-- Consequently the same-cell collapse has at most four complete register
snapshots after the collapsed support entry is visited. -/
theorem same_cell_collapse_snapshots_four
    (hrun : IsRun m e r0)
    {k x : Nat}
    (hstart : e k = x)
    (hcollapse : m.cellOf (m.bar x) = m.cellOf x)
    (hpartner : OccupiedLobeAt m e r0 k
      (m.star (m.cellOf x))) :
    FourSnapshotTail m e r0 k := by
  intro cells ks hks hnd
  exact certifiedLobeAbsorption_snapshot_count m e r0 hrun
    (same_cell_collapse_certifies_absorption
      m e r0 hstart hcollapse hpartner)
    cells ks hks hnd

/-- The other collapsed geometry cannot occur at a visit to a fully
externally lobed selected-edge-closed component. -/
theorem mouth_partner_collapse_impossible
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {lo k x : Nat}
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hlobed : FullyExternallyLobedFrom m e r0 cells lo)
    (hk : lo ≤ k)
    (hentry : m.cellOf (e k) ∈ cells)
    (hstart : e k = x)
    (hcollapse : m.cellOf (m.bar x) = m.star (m.cellOf x)) :
    False := by
  have hfirst : OccupiedLobeAt m e r0 k
      (m.star (m.cellOf (e k))) :=
    hlobed k hk (m.cellOf (e k)) hentry
  have hlobe1 : LobeEntryAt m e (k+1) :=
    next_lobe_of_occupied_partner m e r0 hrun hfirst
  have hcell1 : m.cellOf (e (k+1)) = m.star (m.cellOf x) := by
    calc
      m.cellOf (e (k+1)) = m.cellOf (m.bar (e (k+1))) := hlobe1.symm
      _ = m.star (m.cellOf (e k)) := (witness m e r0 hrun hr0 k).1
      _ = m.star (m.cellOf x) := by rw [hstart]
  have hreflect : e (k+2) = m.bar x := by
    have h := lobe_entry_reflects m e r0 hrun hr0 hlobe1
    rw [hstart] at h
    exact h
  have hreg0 : reg m e r0 k (m.cellOf x) = x := by
    calc
      reg m e r0 k (m.cellOf x) = e k :=
        reg_write m e r0 (congrArg m.cellOf hstart)
      _ = x := hstart
  have hreg2 : reg m e r0 (k+2) (m.cellOf x) = x := by
    have hstable := reg_stable m e r0 (i := k)
      (c := m.cellOf x) 2 (by
        intro i hi hbound
        have hiCases : i = k+1 ∨ i = k+2 := by omega
        rcases hiCases with rfl | rfl
        · rw [hcell1]
          exact m.star_ne _
        · rw [hreflect, hcollapse]
          exact m.star_ne _)
    exact hstable.trans hreg0
  have hnextMem : m.cellOf (e (k+2)) ∈ cells := by
    have hc := hclosed k hk (m.cellOf (e k)) hentry
    have hw : reg m e r0 k (m.cellOf (e k)) = e k :=
      reg_write m e r0 rfl
    rw [hw, hstart] at hc
    rw [hreflect]
    exact hc
  have hsecond := hlobed (k+2) (by omega)
    (m.cellOf (e (k+2))) hnextMem
  have hsecondX : OccupiedLobeAt m e r0 (k+2) (m.cellOf x) := by
    rw [hreflect, hcollapse, m.star_invol] at hsecond
    exact hsecond
  rcases hsecondX with ⟨b, hbCell, hbLobe, hbOcc⟩
  have hcases := external_lobe_register_cases m e r0
    hbCell hbLobe hbOcc
  have hsame : m.cellOf (m.bar x) = m.cellOf x := by
    rcases hcases with hb | hb
    · have hxb : x = b := hreg2.symm.trans hb
      simpa [hxb] using hbLobe
    · have hxb : x = m.bar b := hreg2.symm.trans hb
      have hbarx : m.bar x = b := by
        rw [hxb, m.bar_invol]
      calc
        m.cellOf (m.bar x) = m.cellOf b := by rw [hbarx]
        _ = m.cellOf x := hbCell
  exact m.star_ne (m.cellOf x) (hcollapse.symm.trans hsame)

/-- In the component context, every collapsed reflector geometry therefore
reduces to the same-cell case. -/
theorem collapsed_geometry_is_same_cell
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {lo k x : Nat}
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hlobed : FullyExternallyLobedFrom m e r0 cells lo)
    (hk : lo ≤ k)
    (hentry : m.cellOf (e k) ∈ cells)
    (hstart : e k = x)
    (hcollapsed : CollapsedReflectorGeometry m x) :
    m.cellOf (m.bar x) = m.cellOf x := by
  rcases hcollapsed with hsame | hmouth
  · exact hsame
  · exact (mouth_partner_collapse_impossible
      m e r0 hrun hr0 cells hclosed hlobed hk hentry hstart hmouth).elim

/-- **Collapsed branch closed.**  On an exact recurrent tail, either of the
two collapsed geometries from `VisibleChipReduction` gives a four-snapshot
bound for the entire recurrent tail. -/
theorem collapsed_geometry_recurrent_snapshots_four
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {K q lo k x : Nat}
    (hrec : ExactRecurrentTail m e r0 K q)
    (hKlo : K ≤ lo)
    (cells : List Nat)
    (hclosed : SelectedClosedFrom m e r0 cells lo)
    (hlobed : FullyExternallyLobedFrom m e r0 cells lo)
    (hk : lo ≤ k)
    (hentry : m.cellOf (e k) ∈ cells)
    (hstart : e k = x)
    (hcollapsed : CollapsedReflectorGeometry m x) :
    FourSnapshotTail m e r0 K := by
  have hsame := collapsed_geometry_is_same_cell
    m e r0 hrun hr0 cells hclosed hlobed hk hentry hstart hcollapsed
  have hpartner : OccupiedLobeAt m e r0 k
      (m.star (m.cellOf x)) := by
    have h := hlobed k hk (m.cellOf (e k)) hentry
    rwa [hstart] at h
  have htail := same_cell_collapse_snapshots_four
    m e r0 hrun hstart hsame hpartner
  exact fourSnapshotTail_pullback_recurrent
    m e r0 hrec (Nat.le_trans hKlo hk) htail

end Echo
