import CanonicalUnconditionalGlobalBound

/-!
# Explicit `N`-cell strict-base corollaries

The abstract finite-frame theorem measures its polynomial factor using the
number of listed slots.  A physical compilation with at most two relevant
slots per represented switch/cell satisfies `slots.length ≤ 2*N`.  Under that
single size fact the unconditional bound becomes

    T^8 ≤ (4*N + 2)^8 * 2^(7*N + 18).

The at-most-`N` version below is the natural interface for a concrete wiring:
a forest compilation can have fewer cells than switches and does not need to
pad the frame with dummy components.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Explicit strict-base bound for an `N`-cell finite frame with at most
`2*N` relevant slots.** -/
theorem finiteFrame_N_strict_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hcells : cells.length = N)
    (hslots : slots.length ≤ 2*N)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤
      blockCoreEighth (4*N + 2) * 2^(7*N+18) := by
  have hbase := canonical_unconditional_global_bound m e r0
    hrun hr0 globalLo globalHi cells slots ks frame hks hnd
  have hfactorNat : 2 * (slots.length + 1) ≤ 4*N + 2 := by
    omega
  have hfactor := blockCoreEighth_mono hfactorNat
  have hmul := Nat.mul_le_mul_right
    (2^(7*cells.length+18)) hfactor
  have hstep := Nat.le_trans hbase hmul
  rw [hcells] at hstep
  exact hstep

/-- **Explicit strict-base bound for a finite frame with at most `N` cells
and at most `2*N` relevant slots.**  This is the form used by the concrete
track-to-echo compilation. -/
theorem finiteFrame_atMost_N_strict_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : CompleteFiniteEpochFrame m e r0
      globalLo globalHi cells slots)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2*N)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    blockCoreEighth ks.length ≤
      blockCoreEighth (4*N + 2) * 2^(7*N+18) := by
  have hbase := canonical_unconditional_global_bound m e r0
    hrun hr0 globalLo globalHi cells slots ks frame hks hnd
  have hfactorNat : 2 * (slots.length + 1) ≤ 4*N + 2 := by
    omega
  have hfactor := blockCoreEighth_mono hfactorNat
  have hfactorStep := Nat.mul_le_mul_right
    (2^(7*cells.length+18)) hfactor
  have hmid := Nat.le_trans hbase hfactorStep
  have hexpNat : 7*cells.length + 18 ≤ 7*N + 18 := by
    omega
  have hexp : 2^(7*cells.length+18) ≤ 2^(7*N+18) :=
    Nat.pow_le_pow_right (by omega) hexpNat
  have hexpStep := Nat.mul_le_mul_left
    (blockCoreEighth (4*N+2)) hexp
  exact Nat.le_trans hmid hexpStep

end Echo
