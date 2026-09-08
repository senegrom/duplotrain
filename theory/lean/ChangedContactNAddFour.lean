import StateLawCoefficientOneTop

/-!
# The changed-contact `N+4` bound

The existing changed-support theorem pays `N+3` for the compressed lead and
two further Gray corners.  For a flip reflector, however, the facing action
switch is deliberately absent from the reusable support.  Unless the strict
pre-contact approach productively first-writes that switch, it is a reserved
ambient coordinate. Reserving it lowers the lead to `N+2`. If it is written,
the runway retrace makes it the last productive write, recovering a historical
corner and leaving only one fresh vector over the generic `N+3` lead.

Everything here is symbolic in `N`; no finite enumeration is used.
-/


/-!
## Productive writes cannot happen inside a pointwise retrace

A settled retrace window (every depth shows the settled tongue state)
admits no productive write: the vectors before and after any interior
step coincide.  Extracted from the serial-continuation module so the
sharp changed-contact and protected-pair closures do not depend on the
six-event programme.
-/

namespace GeneralN

/-- A productive write cannot occur strictly inside a window whose every
depth carries the settled state. -/
theorem productive_not_inside_pointwise_retrace
    {w : Wiring} {N repeatTime span openTime q : Nat}
    {start : Nat × Tongues} {old settled : Tongues}
    (hrepeat : stepN w repeatTime start = some (q, old))
    (hpointwise : ∀ d, d ≤ span →
      ∃ port, stepN w d (q, old) =
        some (port, if d = 0 then old else settled))
    (hproductive : RawProductiveAt w N start openTime)
    (hafter : repeatTime < openTime) :
    repeatTime + span ≤ openTime := by
  apply Nat.le_of_not_gt
  intro hinside
  have hconstant {d : Nat} (hd : 0 < d) (hspan : d ≤ span) :
      restrictedTonguesAt w N start (repeatTime + d) = VectorCount.restrict N settled := by
    obtain ⟨port, hport⟩ := hpointwise d hspan
    simp [restrictedTonguesAt, tonguesAt, stepN_add, hrepeat, hport, Nat.ne_of_gt hd]
  have htime : repeatTime + (openTime - repeatTime) = openTime := by omega
  have htimeSucc : repeatTime + (openTime - repeatTime + 1) = openTime + 1 := by omega
  have hbefore := hconstant (d := openTime - repeatTime) (by omega) (by omega)
  have hafter := hconstant (d := openTime - repeatTime + 1) (by omega) (by omega)
  exact hproductive.2 (by simpa only [htime, htimeSucc] using hafter.trans hbefore.symm)


/-- A switch-simple physical trace cannot return to its literal starting
port and then continue.  The raw writer at time zero and at the return time
would both be the switch of that port, contradicting the indexed `Nodup`
property of the passage word.  The tongue states need not agree. -/
theorem PhysicalTrace.no_strict_return_to_start_port
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    {k : Nat} {returned : Tongues}
    (hpositive : 0 < k)
    (hinside : k < passages.length)
    (hreturn : stepN w k start = some (start.1, returned)) : False := by
  have hzero :=
    htrace.rawWriterAt_eq_passageSwitch_getElem
      (k := 0) (by omega)
  have hreturned :=
    htrace.rawWriterAt_eq_passageSwitch_getElem
      (k := k) hinside
  have hwriters :
      rawWriterAt w start 0 = rawWriterAt w start k := by
    simp [rawWriterAt, rawEntryAt, stepN, hreturn]
  have hpair := List.pairwise_iff_getElem.mp hsimple
  have hne := hpair 0 k (by simpa using (show 0 < passages.length by omega))
    (by simpa using hinside) hpositive
  apply hne
  simpa [hzero, hreturned] using hwriters


/-- Writing a flip reflector's action switch on a switch-simple trace whose
endpoints groove its support forces a constant-tongue retrace of the runway
back to the start port, so no later time before the trace ends is productive. -/
theorem ManufacturedFlipReflector.no_productive_after_action_writer
    {w : Wiring} {N g e : Nat} (R : ManufacturedFlipReflector w g e)
    {state : Tongues} {approach : List Passage} {finish : Nat × Tongues}
    (htrace : PhysicalTrace w (e, state) approach finish)
    (hsimple : SwitchSimple approach)
    (hstart : PathGrooves (ManufacturedReflector.flip R).toSupported.paths state)
    (hfinish : PathGrooves (ManufacturedReflector.flip R).toSupported.paths finish.2)
    {t : Nat} (ht : t ∈ rawFirstWriterTimes w N (e, state) approach.length)
    (hwriter : rawWriterAt w (e, state) t = R.actionSwitch) :
    ∀ j, t < j → j < approach.length → ¬ RawProductiveAt w N (e, state) j := by
  intro j htj hjBound hjProd
  have htData := mem_rawFirstWriterTimes_iff.mp ht
  obtain ⟨cur, next, hcur, hnext, hstep, hexit, _⟩ :=
    rawProductiveAt_is_endpoint_pivot htData.2.1
  have hactionArrive : arrive cur.2 cur.1 = (R.mouth, next.2) := by
    apply Prod.ext
    · change exitPort cur = R.mouth
      rw [hexit, hwriter]
      unfold ManufacturedFlipReflector.actionSwitch
      have := R.mouth_is_stem
      omega
    · exact (step_some_parts hstep).2.symm
  have hpostRunwayGrooved : PassagesGrooved next.2 R.runway :=
    (htrace.pathGrooves_at_prefix_of_endpoints hsimple hstart hfinish
      (by omega) hnext) R.runway List.mem_cons_self
  have hpointwise := physicalTrace_contact_retraces_prefix_pointwise
    R.runwayTrace hpostRunwayGrooved R.entryEdge hactionArrive
  have hback := physicalTrace_contact_retraces_prefix
    R.runwayTrace hpostRunwayGrooved R.entryEdge hactionArrive
  let returnTime := t + (R.runway.length + 1)
  have hreturn : stepN w returnTime (e, state) = some (e, next.2) := by
    rw [show returnTime = t + (R.runway.length + 1) from rfl, stepN_add, hcur]
    simpa [reversePassages_length, Nat.add_comm] using hback.sound
  have hbound : approach.length ≤ returnTime := by
    apply Nat.le_of_not_gt
    intro hinside
    exact htrace.no_strict_return_to_start_port hsimple
      (by dsimp [returnTime]; omega) hinside hreturn
  have hout := productive_not_inside_pointwise_retrace
    hcur hpointwise hjProd htj
  dsimp [returnTime] at hbound
  omega


/-- Productive first-writer coordinates in the strict approach to the first
support-changing contact. -/
def PartialSecondRunSharp.ChangedContact.approachFirstWriterSwitches
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w A) (N : Nat) : List Nat :=
  (rawFirstWriterTimes w N (e, A.activatedState)
      C.approach.length).map
    (rawWriterAt w (e, A.activatedState))


/-- Reserving the flip action coordinate lowers the changed-contact history
from `N+3` to `N+2`. -/
theorem PartialSecondRunSharp.ChangedContact.compressedLead_length_le_N_add_two_of_action_absent
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {R : ManufacturedFlipReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w (.flip R))
    (hA : PathGrooves (ManufacturedReflector.flip R).toSupported.paths
      (ManufacturedReflector.flip R).activatedState)
    (habsent : R.actionSwitch ∉ C.approachFirstWriterSwitches N) :
    (C.compressedLead N).length ≤ N + 2 := by
  have hbound := (ManufacturedReflector.flip R).continuationHistory_length_le
    hN rfl C.approach_trace C.approach_simple hA C.old_grooves [R.actionSwitch]
    (by simp) (by simpa using R.action_lt hN)
    (by simpa using R.action_not_mem_reusable) (by simpa only [List.mem_singleton, forall_eq, PartialSecondRunSharp.ChangedContact.approachFirstWriterSwitches] using habsent)
  simpa [PartialSecondRunSharp.ChangedContact.compressedLead] using hbound

/-- Every sharp changed contact is bounded by `N+4`.  Backward contacts and
stay-reflector contacts already have zero local novelty; the flip-reflector
case is exactly the runway-retrace theorem. -/
theorem PartialSecondRunSharp.ChangedContact.all_run_distinct_le_N_add_four
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    {A : ManufacturedReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w A)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + 4 := by
  rcases C.direction with hbackward | hforward
  · have hsmall := C.backward_all_run_distinct_le_N_add_three
      hN hA hbackward times hlive hnd
    omega
  · cases A with
    | stay R =>
        have hcount := C.changed_all_run_distinct_le_compressedLead_add_budget
          hA times hlive hnd (C.forward_stay_zero_novelty hforward _)
        have hlength := C.compressedLead_length_le hN hA
        omega
    | flip R =>
        by_cases haction : R.actionSwitch ∈ C.approachFirstWriterSwitches N
        · obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp haction
          have htData := mem_rawFirstWriterTimes_iff.mp ht
          have hlast := R.no_productive_after_action_writer C.approach_trace
            C.approach_simple hA C.old_grooves ht hwriter
          have hrecover := last_productive_recovers C.approach_trace.sound
            htData.1 htData.2.1 hlast
          rw [hwriter] at hrecover
          have hcorner : VectorCount.restrict N (flipAt C.contactState R.actionSwitch) ∈
              C.compressedLead N := by
            rw [hrecover]
            exact C.mem_compressedLead_of_approach (Nat.le_of_lt htData.1)
          have hcount := C.changed_all_run_distinct_le_compressedLead_add_budget
            (budget := 1) hA times hlive hnd (by
              refine ⟨[VectorCount.restrict N (flipAt C.nextState R.actionSwitch)], by simp, ?_⟩
              intro k hk
              have h := C.forward_flip_corner_cover (N := N) hforward _ k hk
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
              rcases h with h | h | h
              · exact Or.inl h
              · exact Or.inr h
              · exact Or.inl (h ▸ hcorner))
          have hlength := C.compressedLead_length_le hN hA
          omega
        · have hcount := C.changed_all_run_distinct_le_compressedLead_add_budget
            (budget := 2) hA times hlive hnd
            ⟨_, by simp, C.forward_flip_corner_cover hforward _⟩
          have hlength := C.compressedLead_length_le_N_add_two_of_action_absent hN hA haction
          omega

end GeneralN
