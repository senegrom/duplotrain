import RelevantFibonacciGlobalBound
import FibonacciCapacityMonotone

/-!
# Explicit `N`-cell Fibonacci upper bound

For a constructible relevant echo frame with at most `N` cells and at most
`2*N` slots, the complete register snapshots satisfy

    T ≤ (2*N + 1) * fibBalancedCapacity N + 4.

Since

    fibBalancedCapacity N
      = 2^(N/2) * F_(((N+1)/2)+2),

this is asymptotically `O(N * (sqrt (2*phi))^N)`, with exponential base
about `1.79891`.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Explicit constructible `N`-cell complete-snapshot bound.** -/
theorem relevant_finiteFrame_N_fibonacci_bound
    (hrun : IsRun m e r0)
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (N globalLo globalHi : Nat)
    (cells slots ks : List Nat)
    (frame : ProperRelevantFiniteFrame m e r0 cells slots)
    (hfullRelevant : FullEdgesRelevant m e r0
      globalLo globalHi cells)
    (hcells : cells.length ≤ N)
    (hslots : slots.length ≤ 2*N)
    (hks : ∀ k ∈ ks, globalLo ≤ k ∧ k ≤ globalHi)
    (hnd : (ks.map (snap m e r0 cells)).Nodup) :
    ks.length ≤ (2*N + 1) * fibBalancedCapacity N + 4 := by
  have hbase := relevant_unconditional_global_fibonacci_bound m e r0
    hrun hr0 globalLo globalHi cells slots ks frame
    hfullRelevant hks hnd
  have hfactor : slots.length + 1 ≤ 2*N + 1 := by
    omega
  have hcap : fibBalancedCapacity cells.length ≤
      fibBalancedCapacity N :=
    fibBalancedCapacity_mono hcells
  have hmul :
      (slots.length + 1) * fibBalancedCapacity cells.length ≤
        (2*N + 1) * fibBalancedCapacity N :=
    Nat.mul_le_mul hfactor hcap
  omega

end Echo
