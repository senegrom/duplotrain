import ConcreteTraceRegisters

/-!
# A segmented concrete run satisfies the echo recurrence

A certified concrete run records landed cascades and the physical facing
transition from each cascade landing to the next branch entry.  The next entry
is not assumed to satisfy the echo formula.

At read time `k`, split on whether the partner cell has previously ascended.
If so, choose its greatest ascent index and use interval non-interference plus
`trace_last_writer_retrace`.  If not, use the physical initial slot and the
initial-pin preservation theorem.  In both cases the independently recorded
physical facing transition has the same deterministic `stepN` left-hand side,
so its endpoint must be the jump partner of the selected register.  This proves
`Echo.IsRun`.
-/

namespace GeneralN

/-- Partner root-cell read after the ascent at time `k`. -/
noncomputable def tracePartnerCell {w : Wiring}
    (trace : ConcreteAscentTrace w) (k : Nat) : Nat :=
  mateNat (physicalCell w (trace.entry k))

/-- A segmented concrete ascent run with physical initial tree states and
physical facing transitions. -/
structure CertifiedConcreteEchoRun (w : Wiring)
    extends ConcreteAscentTrace w where
  initialRegister : Nat → Nat
  initialWellFormed : ∀ c,
    (canonicalEchoMachine w).cellOf (initialRegister c) = c
  initialPhysical : ∀ k,
    (∀ i, i ≤ k →
      physicalCell w (entry i) ≠
        tracePartnerCell toConcreteAscentTrace k) →
    ∃ f,
      initialRegister (tracePartnerCell toConcreteAscentTrace k) =
          encodeSlot f ∧
      IsCanonicalEchoSlot w f ∧
      ProperMouthRoot w (entryRoot w f) ∧
      physicalCell w f = tracePartnerCell toConcreteAscentTrace k ∧
      Agrees (boundary 0) (entryAction w f)
  facing : ∀ k f,
    Echo.reg (canonicalEchoMachine w)
      (encodedEntries entry) initialRegister k
      (tracePartnerCell toConcreteAscentTrace k) = encodeSlot f →
    stepN w (entryAction w f).length
      (landing k, boundary (k + 1)) =
      some (entry (k + 1), boundary (k + 1))

/-- The current partner cell is the root code of the current cascade's
landing switch. -/
theorem tracePartnerCell_eq_landingCode
    {w : Wiring} (trace : ConcreteAscentTrace w) (k : Nat) :
    tracePartnerCell trace k =
      rootCode w (trace.landing k / 3) := by
  have hp : IsDescentEntry w (trace.entry k) :=
    (trace.freeSlot k).1
  have hstar := canonicalEchoMachine_star_entry
    hp (trace.properRoot k)
  have hlanding := entryLanding_eq_of_descent (trace.descent k)
  simpa [tracePartnerCell, physicalCell, canonicalEchoMachine,
    encodedMachine, encodedCellOf_encodeSlot, canonicalPhysicalCellOf,
    hlanding] using hstar

/-- The landing root of a proper current cascade is itself a proper mouth
root. -/
theorem trace_landingRoot_proper
    {w : Wiring} (trace : ConcreteAscentTrace w) (k : Nat) :
    ProperMouthRoot w (trace.landing k / 3) := by
  rcases trace.properRoot k with ⟨s, hmouth, hne⟩
  have hp : IsDescentEntry w (trace.entry k) :=
    (trace.freeSlot k).1
  have hcanonical := entryRoot_mouthPaired hp
  have hs : s = entryLanding w (trace.entry k) / 3 :=
    mouthPaired_right_unique hmouth hcanonical
  have hlanding := entryLanding_eq_of_descent (trace.descent k)
  subst s
  rw [hlanding] at hne hmouth
  exact ⟨entryRoot w (trace.entry k),
    mouthPaired_symm hmouth, hne.symm⟩

/-- Any proper physical entry stored in the current partner cell has exactly
the current landing root. -/
theorem stored_partner_root_eq_landing
    {w : Wiring} (trace : ConcreteAscentTrace w) (k f : Nat)
    (hfProper : ProperMouthRoot w (entryRoot w f))
    (hfCell : physicalCell w f = tracePartnerCell trace k) :
    entryRoot w f = trace.landing k / 3 := by
  apply rootCode_injective_on_proper
    hfProper (trace_landingRoot_proper trace k)
  have hpartner := tracePartnerCell_eq_landingCode trace k
  unfold physicalCell at hfCell
  exact hfCell.trans hpartner

/-- A stored entry in the partner cell has a different root from the current
ascent. -/
theorem stored_partner_root_ne_current
    {w : Wiring} (trace : ConcreteAscentTrace w) (k f : Nat)
    (hfCell : physicalCell w f = tracePartnerCell trace k) :
    entryRoot w f ≠ entryRoot w (trace.entry k) := by
  intro hroot
  have hsameCell : physicalCell w f =
      physicalCell w (trace.entry k) := by
    unfold physicalCell
    rw [hroot]
  have hmate : tracePartnerCell trace k =
      physicalCell w (trace.entry k) :=
    hfCell.symm.trans hsameCell
  exact mateNat_ne (physicalCell w (trace.entry k))
    (by simpa [tracePartnerCell] using hmate)

/-- No later write to a partner cell implies no later ascent of the stored
root. -/
theorem no_later_partner_cell_no_later_root
    {w : Wiring} (trace : ConcreteAscentTrace w)
    {start current f : Nat}
    (hfRoot : entryRoot w f = entryRoot w (trace.entry start))
    (hcell : physicalCell w (trace.entry start) =
      tracePartnerCell trace current)
    (hno : ∀ i, start < i → i ≤ current →
      physicalCell w (trace.entry i) ≠
        tracePartnerCell trace current) :
    ∀ i, start < i → i ≤ current →
      entryRoot w (trace.entry start) ≠
        entryRoot w (trace.entry i) := by
  intro i hiLo hiHi hroot
  apply hno i hiLo hiHi
  unfold physicalCell
  rw [← hroot]
  exact hcell

/-- Retrace an untouched physical initial register at the current partner
root. -/
theorem initial_writer_retrace
    {w : Wiring} (trace : ConcreteAscentTrace w)
    (k f : Nat)
    (hfSlot : IsCanonicalEchoSlot w f)
    (hfProper : ProperMouthRoot w (entryRoot w f))
    (hfCell : physicalCell w f = tracePartnerCell trace k)
    (hno : ∀ i, i ≤ k →
      physicalCell w (trace.entry i) ≠ tracePartnerCell trace k)
    (hinitial : Agrees (trace.boundary 0) (entryAction w f)) :
    stepN w (entryAction w f).length
      (trace.landing k, trace.boundary (k + 1)) =
      some (wireBar w f, trace.boundary (k + 1)) := by
  have hf : IsDescentEntry w f := hfSlot.1
  have hroot : entryRoot w f = trace.landing k / 3 :=
    stored_partner_root_eq_landing trace k f hfProper hfCell
  have hnoRoot : ∀ i, i ≤ k →
      entryRoot w f ≠ entryRoot w (trace.entry i) := by
    intro i hi hEq
    apply hno i hi
    unfold physicalCell
    rw [← hEq]
    exact hfCell
  have hagree := trace_initial_writer_agrees
    trace f hf k hnoRoot hinitial
  let witness := chosenDescentWitness w f hf
  have hd := witness.descent
  have hentry := canonicalEchoSlot_reverse_link hfSlot
  have hret := retrace hd (wireBar w f) hentry
    (trace.boundary (k + 1)) (by
      have haction := entryAction_eq_of_descent hd
      rwa [haction] at hagree)
  have hlandingStem := descent_landing_stem (trace.descent k)
  have hlanding : trace.landing k = 3 * entryRoot w f := by
    have hstem := stem_eq_three_mul_div hlandingStem
    rw [← hroot] at hstem
    omega
  rw [entryAction_eq_of_descent hd, hlanding,
    entryRoot_eq_of_descent hd]
  exact hret

/-- **Central compiler theorem.**  Every certified segmented concrete run is
a run of the canonical echo machine. -/
theorem certifiedConcreteEcho_isRun
    {w : Wiring} (run : CertifiedConcreteEchoRun w) :
    Echo.IsRun (canonicalEchoMachine w)
      (encodedEntries run.entry) run.initialRegister := by
  intro k
  let trace := run.toConcreteAscentTrace
  let partner := tracePartnerCell trace k
  by_cases hprev : ∃ j, j ≤ k ∧
      physicalCell w (trace.entry j) = partner
  · obtain ⟨j, hjk, hjCell, hjLast⟩ :=
      exists_last_le k hprev
    have hreg :
        Echo.reg (canonicalEchoMachine w)
          (encodedEntries trace.entry) run.initialRegister k partner =
          encodeSlot (trace.entry j) :=
      canonical_reg_last_entry trace.entry run.initialRegister
        hjCell hjk hjLast
    have hjProper := trace.properRoot j
    have hjRoot : entryRoot w (trace.entry j) =
        trace.landing k / 3 :=
      stored_partner_root_eq_landing trace k (trace.entry j)
        hjProper hjCell
    have hnoRoot : ∀ i, j < i → i ≤ k →
        entryRoot w (trace.entry j) ≠
          entryRoot w (trace.entry i) := by
      intro i hiLo hiHi hEq
      apply hjLast i hiLo hiHi
      unfold physicalCell
      rw [← hEq]
      exact hjCell
    let count := k - j
    have hjcount : j + count = k := by
      dsimp [count]
      omega
    have hret := trace_last_writer_retrace
      trace j count (by
        intro i hiLo hiHi
        apply hnoRoot i hiLo
        rwa [hjcount] at hiHi)
      (by rw [hjcount]; exact hjRoot.symm)
    have hface := run.facing k (trace.entry j) (by
      simpa [trace, partner] using hreg)
    rw [hjcount] at hret
    rw [hret] at hface
    have hnext : trace.entry (k + 1) =
        wireBar w (trace.entry j) := by
      injection hface with h
      exact (congrArg Prod.fst h).symm
    have hstarcell : (canonicalEchoMachine w).star
        ((canonicalEchoMachine w).cellOf (encodedEntries run.entry k)) =
        partner := by
      simp [encodedEntries, canonicalEchoMachine, encodedMachine,
        encodedCellOf_encodeSlot, partner, trace, tracePartnerCell,
        physicalCell, canonicalPhysicalCellOf]
    rw [hstarcell]
    have hreg' : Echo.reg (canonicalEchoMachine w)
        (encodedEntries run.entry) run.initialRegister k partner =
        encodeSlot (trace.entry j) := hreg
    rw [hreg']
    have hbar : (canonicalEchoMachine w).bar
        (encodeSlot (trace.entry j)) =
        encodeSlot (wireBar w (trace.entry j)) := by
      simp [canonicalEchoMachine, encodedMachine, encodedBar_encodeSlot]
    rw [hbar]
    exact congrArg encodeSlot hnext
  · have hno : ∀ i, i ≤ k →
        physicalCell w (trace.entry i) ≠ partner := by
      intro i hi hEq
      exact hprev ⟨i, hi, hEq⟩
    obtain ⟨f, hfInit, hfSlot, hfProper,
        hfCell, hfAgrees⟩ :=
      run.initialPhysical k (by
        simpa [trace, partner] using hno)
    have hreg0 :
        Echo.reg (canonicalEchoMachine w)
          (encodedEntries trace.entry) run.initialRegister k partner =
          run.initialRegister partner :=
      canonical_reg_initial trace.entry run.initialRegister
        k partner hno
    have hreg :
        Echo.reg (canonicalEchoMachine w)
          (encodedEntries trace.entry) run.initialRegister k partner =
          encodeSlot f := by
      rw [hreg0, hfInit]
    have hret := initial_writer_retrace
      trace k f hfSlot hfProper
      (by simpa [trace, partner] using hfCell)
      (by simpa [trace, partner] using hno) hfAgrees
    have hface := run.facing k f (by
      simpa [trace, partner] using hreg)
    rw [hret] at hface
    have hnext : trace.entry (k + 1) = wireBar w f := by
      injection hface with h
      exact (congrArg Prod.fst h).symm
    have hstarcell : (canonicalEchoMachine w).star
        ((canonicalEchoMachine w).cellOf (encodedEntries run.entry k)) =
        partner := by
      simp [encodedEntries, canonicalEchoMachine, encodedMachine,
        encodedCellOf_encodeSlot, partner, trace, tracePartnerCell,
        physicalCell, canonicalPhysicalCellOf]
    rw [hstarcell]
    have hreg' : Echo.reg (canonicalEchoMachine w)
        (encodedEntries run.entry) run.initialRegister k partner =
        encodeSlot f := hreg
    rw [hreg']
    have hbar : (canonicalEchoMachine w).bar (encodeSlot f) =
        encodeSlot (wireBar w f) := by
      simp [canonicalEchoMachine, encodedMachine, encodedBar_encodeSlot]
    rw [hbar]
    exact congrArg encodeSlot hnext

end GeneralN
