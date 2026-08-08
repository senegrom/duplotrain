import CanonicalCertifiedEpochBound
import RelevantCanonicalFrame
import SupportRelativeFibonacciEpochBound

/-!
# Canonical Fibonacci-exact epoch bounds

Parallel direct-count versions of the canonical strict epoch theorems.  The
canonical coordinate construction is unchanged; only the terminal sparse-code
count is replaced by `fibBalancedCapacity`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Canonical direct count for one fixed-support interval with no certified
lobe absorption. -/
theorem canonical_noCertified_fibonacci_epoch_bound
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
    ks.length ≤ fibBalancedCapacity cells.length := by
  let lobes := canonicalActiveLobes m e r0 lo hi slots k0
  let projected := canonicalProjectedCells m e r0
    lo hi cells slots k0
  let edges := canonicalProjectedEdges m e r0 lo hi slots k0
  apply support_relative_noCertified_fibonacci_bound m e r0
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

/-- Constructible relevant-frame direct count under the older pre-absorption
hypothesis. -/
theorem relevant_canonical_preAbsorption_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (lo hi k0 : Nat)
    (cells slots ks : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0 lo hi cells)
    (hfixed : PairedSupportFixed m e r0 lo hi)
    (hk0 : lo ≤ k0 ∧ k0 ≤ hi)
    (hnoTail : StandaloneNoFourTailIn m e r0 lo hi)
    (hks : ∀ k ∈ ks, lo ≤ k ∧ k ≤ hi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ fibBalancedCapacity cells.length := by
  let finiteFrame := frame.toFiniteEpochFrame lo hi
  let lobes := canonicalActiveLobes m e r0 lo hi slots k0
  let projected := canonicalProjectedCells m e r0
    lo hi cells slots k0
  let edges := canonicalProjectedEdges m e r0 lo hi slots k0
  apply support_relative_preAbsorption_fibonacci_bound m e r0
    hrun hr0 lo hi cells projected edges lobes ks hfixed
  · dsimp [edges]
    exact relevant_canonicalProjected_allFull_represented
      m e r0 hr0 frame hfullRelevant hfixed hk0
  · dsimp [lobes]
    exact canonical_support_replay_cover m e r0
      finiteFrame hfixed hk0
  · dsimp [lobes, projected]
    exact canonicalProjectedCells_length m e r0 finiteFrame
  · exact frame.cells_nodup
  · dsimp [projected]
    exact canonicalProjectedCells_nodup m e r0 frame.cells_nodup
  · dsimp [edges]
    exact canonicalProjectedEdgeEnds_nodup m e r0 frame.slots_nodup
  · dsimp [projected, edges]
    exact relevant_canonicalProjected_selected
      m e r0 hr0 frame hfixed hk0
  · dsimp [projected, edges]
    exact relevant_canonicalProjected_confirmed_cell
      m e r0 frame hfixed hk0
  · dsimp [edges]
    exact relevant_canonicalProjectedEdges_occupied
      m e r0 hfixed hk0
  · dsimp [lobes]
    exact canonicalActiveLobeCells_nodup m e r0 frame.slots_nodup
  · dsimp [lobes]
    exact canonicalActiveLobeCells_closed m e r0 finiteFrame
  · dsimp [lobes]
    exact canonicalActiveLobes_loop m e r0
  · dsimp [lobes]
    exact canonicalActiveLobes_occupied m e r0 hfixed hk0
  · dsimp [lobes]
    exact canonicalActiveLobes_visited m e r0 hfixed hk0
  · exact hnoTail
  · exact hks
  · exact hnd

end Echo
