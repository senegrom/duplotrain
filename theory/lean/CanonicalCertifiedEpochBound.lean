import CanonicalProjectedEpochFrame
import SupportRelativeCertifiedEpochBound

/-!
# Canonical strict epoch bound before certified absorption

All code coordinates are derived from a complete finite frame and one reference
support.  The caller supplies only the fixed-support interval and the exact
statement that no certified lobe absorption begins there.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Completely canonical strict bound for one fixed-support interval with no
certified lobe absorption.** -/
theorem canonical_noCertified_epoch_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi k0 : Nat)
    (cells slots ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0 lo hi cells slots)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi)
    (hnoAbsorb : NoCertifiedLobeAbsorptionIn m e r0 lo hi)
    (hks : ∀ k ∈ ks, lo ≤ k ∧ k ≤ hi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤ 2^(7*cells.length+18) := by
  let lobes := canonicalActiveLobes m e r0 lo hi slots k0
  let projected := canonicalProjectedCells m e r0
    lo hi cells slots k0
  let edges := canonicalProjectedEdges m e r0 lo hi slots k0
  apply support_relative_noCertified_epoch_bound m e r0
    hrun hr0 lo hi cells projected edges lobes ks hfixed
  · dsimp [edges]
    exact canonicalProjected_allFull_represented m e r0 hr0
      frame hfixed hk0
  · dsimp [lobes]
    exact canonical_support_replay_cover m e r0
      frame.toFiniteEpochFrame hfixed hk0
  · dsimp [lobes, projected]
    exact canonicalProjectedCells_length m e r0
      frame.toFiniteEpochFrame
  · exact frame.cells_nodup
  · dsimp [projected]
    exact canonicalProjectedCells_nodup m e r0 frame.cells_nodup
  · dsimp [edges]
    exact canonicalProjectedEdgeEnds_nodup m e r0
      frame.slots_nodup
  · dsimp [projected, edges]
    exact canonicalProjected_selected m e r0 hr0 frame hfixed hk0
  · dsimp [projected, edges]
    exact canonicalProjected_confirmed_cell m e r0 frame hfixed hk0
  · dsimp [edges]
    exact canonicalProjectedEdges_occupied m e r0 hfixed hk0
  · dsimp [lobes]
    exact canonicalActiveLobeCells_nodup m e r0
      frame.slots_nodup
  · dsimp [lobes]
    exact canonicalActiveLobeCells_closed m e r0
      frame.toFiniteEpochFrame
  · dsimp [lobes]
    exact canonicalActiveLobes_loop m e r0
  · dsimp [lobes]
    exact canonicalActiveLobes_occupied m e r0 hfixed hk0
  · dsimp [lobes]
    exact canonicalActiveLobes_visited m e r0 hfixed hk0
  · exact hnoAbsorb
  · exact hks
  · exact hnd

end Echo
