import CrossingCallerWindowExtraction
import SharpSixEventAssembly

/-!
# Canonical caller extraction for the serial/serial residue

The serial continuation previously retained only a return configuration and
the inequality saying that the previous write of the first escape is no later
than the repeat time.  This file recovers the physical caller used to build
that continuation and places the previous write relative to the caller's
actual absolute interval.
-/

namespace GeneralN

/-- The tail serial window supplies its actual caller trace, completed return,
first post-return productive escape, and an exhaustive placement of that
escape's previous write.  The middle placement is precisely the pair of
`hleftStart`/`hleftEnd` hypotheses consumed by
`early_crossing_caller_exact_false`; the two outer placements are kept
explicit rather than hidden in a coarse `left ≤ repeatTime` certificate. -/
theorem RawOverlappingFiveWindowReduction.tail_serial_canonical_caller_escape
    {w : Wiring} {N initialEdge : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    (R : RawOverlappingFiveWindowReduction w N start)
    (hserial : FiveFrameSerialBreak
      R.z1 R.a2 R.a3 R.a4 R.a5) :
    ∃ (g oldEntry q edge repeatTime returnTime escape : Nat)
        (base mouthState u settled : Tongues)
        (caller : List Passage),
      stepN w R.a1 start = some (g, base) ∧
      PhysicalTrace w (g, base) caller (oldEntry, mouthState) ∧
      PassagesGrooved settled caller ∧
      w.link edge = some g ∧
      stepN w repeatTime start = some (q, u) ∧
      returnTime = repeatTime + caller.length + 1 ∧
      stepN w returnTime start = some (edge, settled) ∧
      returnTime ≤ escape ∧
      escape ≤ R.z1 ∧
      RawProductiveAt w N start escape ∧
      (forall t, returnTime ≤ t -> t < escape ->
        ¬ RawProductiveAt w N start t) ∧
      (RawFirstWriterAt w N start escape ∨
        ∃ left,
          RawLastWriterFrame w N start left escape ∧
          left ≤ repeatTime ∧
          (left < R.a1 ∨
            (R.a1 ≤ left ∧ left < R.a1 + caller.length) ∨
            R.a1 + caller.length ≤ left)) := by
  obtain ⟨g, base, oldEntry, mouthState, q, u, settled, edge,
      repeatTime, caller, hbefore, hcaller, _hsimple, hgrooved,
      _hcallerLe, hedge, hrepeat, _hrepeatAfterOpen,
      _hrepeatBeforeClose, hreturnBeforeClose, _hcontact,
      hlocalReturn, hpointwise, _hcover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry
      R.event1 R.event2 R.event3 R.event4 R.event5
      R.frame1 R.frame2 R.frame3 R.frame4 R.frame5 hserial
  let returnTime := repeatTime + caller.length + 1
  have habsoluteReturn :
      stepN w returnTime start = some (edge, settled) := by
    rw [show returnTime = repeatTime + (caller.length + 1) by
      dsimp [returnTime]
      omega]
    rw [stepN_add, hrepeat]
    exact hlocalReturn
  have hreturnBeforeClose : returnTime ≤ R.z1 := by
    simpa [returnTime, Nat.add_assoc] using hreturnBeforeClose
  obtain ⟨escape, hreturnEscape, hescapeClose, hproductive,
      hminimal, hfirst | ⟨left, F, hleftRepeat⟩⟩ :=
    first_productive_escape_first_or_crosses_caller
      (N := N) (repeatTime := repeatTime)
      (span := caller.length + 1) (returnTime := returnTime)
      (right := R.z1) (q := q)
      hrepeat hpointwise (by rfl) hreturnBeforeClose R.event1.1
  · exact ⟨g, oldEntry, q, edge, repeatTime, returnTime, escape,
      base, mouthState, u, settled, caller,
      hbefore, hcaller, hgrooved, hedge, hrepeat, rfl,
      habsoluteReturn, hreturnEscape, hescapeClose, hproductive,
      hminimal, Or.inl hfirst⟩
  · have hplacement :
        left < R.a1 ∨
          (R.a1 ≤ left ∧ left < R.a1 + caller.length) ∨
          R.a1 + caller.length ≤ left := by
      by_cases hbeforeCaller : left < R.a1
      · exact Or.inl hbeforeCaller
      · by_cases hinsideCaller : left < R.a1 + caller.length
        · exact Or.inr (Or.inl ⟨by omega, hinsideCaller⟩)
        · exact Or.inr (Or.inr (by omega))
    exact ⟨g, oldEntry, q, edge, repeatTime, returnTime, escape,
      base, mouthState, u, settled, caller,
      hbefore, hcaller, hgrooved, hedge, hrepeat, rfl,
      habsoluteReturn, hreturnEscape, hescapeClose, hproductive,
      hminimal, Or.inr ⟨left, F, hleftRepeat, hplacement⟩⟩

end GeneralN
