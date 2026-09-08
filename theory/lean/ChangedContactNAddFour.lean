import StateLawCoefficientOneTop

/-!
# The changed-contact `N+4` bound

The existing changed-support theorem pays `N+3` for the compressed lead and
two further Gray corners.  For a flip reflector, however, the facing action
switch is deliberately absent from the reusable support.  Unless the strict
pre-contact approach productively writes that switch, it is a reserved
ambient coordinate. Reserving it lowers the lead to `N+2`. If it is written,
the runway retrace makes it the last productive write, recovering a historical
corner and leaving only one fresh vector over the generic `N+3` lead.

Everything here is symbolic in `N`; no finite enumeration is used.
-/

namespace GeneralN

/-- Writing a flip reflector's action switch on a switch-simple trace whose
endpoints groove its support forces a constant-tongue retrace of the runway
back to the start port. It is the last productive write, so undoing it in
the final vector recovers its historical pre-vector. -/
theorem ManufacturedFlipReflector.action_writer_recovers
    {w : Wiring} {N g e : Nat} (R : ManufacturedFlipReflector w g e)
    {state : Tongues} {approach : List Passage} {finish : Nat × Tongues}
    (htrace : PhysicalTrace w (e, state) approach finish)
    (hsimple : SwitchSimple approach)
    (hstart : PathGrooves (ManufacturedReflector.flip R).toSupported.paths state)
    (hfinish : PathGrooves (ManufacturedReflector.flip R).toSupported.paths finish.2)
    {t : Nat} (ht : t ∈ rawProductiveTimes w N (e, state) approach.length)
    (hwriter : rawWriterAt w (e, state) t = R.actionSwitch) :
    VectorCount.restrict N (flipAt finish.2 R.actionSwitch) =
      restrictedTonguesAt w N (e, state) t := by
  have htData := mem_rawProductiveTimes_iff.mp ht
  rw [← hwriter]
  apply last_productive_recovers htrace.sound htData.1 htData.2
  intro j htj hjBound hjProd
  obtain ⟨cur, next, hcur, hnext, hstep, hexit, _⟩ :=
    rawProductiveAt_is_endpoint_pivot htData.2
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
    have heq := htrace.rawWriterAt_injective hsimple (i := 0) (by omega) hinside
      (by simp [rawWriterAt, rawEntryAt, stepN, hreturn])
    dsimp [returnTime] at heq
    omega
  dsimp [returnTime] at hbound
  have hconstant {d : Nat} (hd : 0 < d) (hspan : d ≤ R.runway.length + 1) :
      restrictedTonguesAt w N (e, state) (t + d) = VectorCount.restrict N next.2 := by
    obtain ⟨port, hport⟩ := hpointwise d hspan
    simp [restrictedTonguesAt, tonguesAt, stepN_add, hcur, hport, Nat.ne_of_gt hd]
  have htime : t + (j - t) = j := by omega
  have htimeSucc : t + (j - t + 1) = j + 1 := by omega
  have hbefore := hconstant (d := j - t) (by omega) (by omega)
  have hafter := hconstant (d := j - t + 1) (by omega) (by omega)
  exact hjProd.2 (by simpa only [htime, htimeSucc] using hafter.trans hbefore.symm)

/-- Productive writer coordinates in the strict approach to the first
support-changing contact. -/
def PartialSecondRunSharp.ChangedContact.approachWriterSwitches
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    (C : PartialSecondRunSharp.ChangedContact w A) (N : Nat) : List Nat :=
  (rawProductiveTimes w N (e, A.activatedState)
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
    (habsent : R.actionSwitch ∉ C.approachWriterSwitches N) :
    (C.compressedLead N).length ≤ N + 2 := by
  have hbound := (ManufacturedReflector.flip R).continuationHistory_length_le
    hN rfl C.approach_trace C.approach_simple hA C.old_grooves [R.actionSwitch]
    (by simp) (by simpa using R.action_lt hN)
    (by simpa using R.action_not_mem_reusable) (by simpa only [List.mem_singleton, forall_eq, PartialSecondRunSharp.ChangedContact.approachWriterSwitches] using habsent)
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
        by_cases haction : R.actionSwitch ∈ C.approachWriterSwitches N
        · obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp haction
          have hcorner : VectorCount.restrict N (flipAt C.contactState R.actionSwitch) ∈
              C.compressedLead N := by
            rw [R.action_writer_recovers C.approach_trace C.approach_simple hA C.old_grooves ht hwriter]
            exact C.mem_compressedLead_of_approach (Nat.le_of_lt (mem_rawProductiveTimes_iff.mp ht).1)
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
