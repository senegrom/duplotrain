import StateLawCoefficientOneTop
import WiringCompletion

/-!
# Known-edge frontier on total wirings

Probe a bounded total wiring for `N+1` steps, so a first revisit is
unavoidable. A stable cycle closes the count; otherwise construct the
first reflector and repeat the live probe from its opposite end. The
remaining possibilities are a cycle, a changed contact, or a protected
pair. No separate argument about probes ending at free ports is needed.

`StateLawNAddFourSharp` first completes arbitrary partial wirings and
transfers every original live sample into this setting.
-/

namespace GeneralN

/-- A literal first damaging contact reached after manufacturing one
reflector from the original known-edge start. -/
structure KnownEdgeChangedContact
    (w : Wiring) (e : Nat) (start : Nat × Tongues) : Type where
  A : ManufacturedReflector w start.1 e
  grooves : PathGrooves A.toSupported.paths A.activatedState
  base : A.baseState = start.2
  contact : PartialSecondRunSharp.ChangedContact w A

/-- A literal pair reached by the two probes. Each reflector's supported
paths are grooved in its activated state, and the second starts from exactly
the first reflector's activated state. -/
structure KnownEdgeProtectedPair
    (w : Wiring) (e : Nat) (start : Nat × Tongues) : Type where
  A : ManufacturedReflector w start.1 e
  B : ManufacturedReflector w e start.1
  A_grooves : PathGrooves A.toSupported.paths A.activatedState
  B_grooves : PathGrooves B.toSupported.paths B.activatedState
  A_base : A.baseState = start.2
  B_base : B.baseState = A.activatedState

/- Known-edge N+4 frontier.

For an arbitrary finite list of live sample times with pairwise-distinct
restricted tongue vectors, either there are at most N+4 samples, or the run
has reached one of exactly two concrete residuals:

1. a support-changing ChangedContact after the first manufactured reflector;
2. a support-protected pair of opposite manufactured reflectors.

The proof is only the sharp first/second-probe decomposition. It deliberately
does not invoke any closure theorem for either residual. -/
/-- On a total wiring, both probes are live. The only nontrivial outcomes
are therefore a first changed contact or a pair of manufactured reflectors;
there are no first- or second-probe death cases to count. -/
theorem known_edge_N_add_four_or_changed_contact_or_protected_pair
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (htotal : ∀ p, p < 3 * N → ∃ q, w.link p = some q)
    {start : Nat × Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (_hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 4 ∨
      Nonempty (KnownEdgeChangedContact w e start) ∨
      Nonempty (KnownEdgeProtectedPair w e start) := by
  obtain ⟨firstFinish, hfirst⟩ :=
    stepN_live_of_total hN htotal (N + 1) start (hN _ _ hentry).2
  rcases first_activated_count_outcome_sharp hN hfirst hentry with hcycleA | hreflectorA
  · left
    have hshort := hcycleA times hnd
    omega
  · obtain ⟨A, stateA, hA, hbaseA, hactivatedA, _hreachA, _hpreservesA⟩ := hreflectorA
    subst stateA
    have hentryB : w.link start.1 = some e := w.symm _ _ hentry
    have hndA : (times.map
        (restrictedTonguesAt w N (start.1, A.baseState))).Nodup := by
      simpa [hbaseA] using hnd
    obtain ⟨secondFinish, hsecond⟩ := stepN_live_of_total hN htotal
      (N + 1) (e, A.activatedState) (hN _ _ hentry).1
    rcases first_activated_trace_outcome_sharp_partial
        hN hsecond hentryB with hcycleB | hreflectorB
    · obtain ⟨C⟩ := hcycleB
      by_cases hend : PathGrooves A.toSupported.paths C.atRepeat.2
      · left
        have hsmall := simple_lead_one_vector_tail_distinct_le_N_add_three
          hN A hA C.lead_trace C.lead_simple hend C.positive_settled times hndA
        omega
      · right
        left
        obtain ⟨D⟩ :=
          PartialSecondRunSharp.ManufacturedReflector.changedContact_of_broken_simple
            A hA C.lead_trace C.lead_simple hend
        exact ⟨{ A := A, grooves := hA, base := hbaseA, contact := D }⟩
    · right
      right
      obtain ⟨B, stateB, hB, hbaseB, hactivatedB⟩ := hreflectorB
      subst stateB
      exact ⟨{
        A := A, B := B, A_grooves := hA, B_grooves := hB,
        A_base := hbaseA, B_base := hbaseB
      }⟩

end GeneralN
