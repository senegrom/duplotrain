import TwoHistoryUnionCharge
import StateLawTwoSharp
import ProtectedRepairFour

/-!
# First-contact continuation

The endpoint-groove-preserved branch does not need a recursive residual.
Switch simplicity makes every productive writer in the second exploration
survive to its pre-return endpoint.  Consequently every such writer is
outside the first reflector's reusable support, and the two sets of
coordinates are charged once.  `TwoHistoryUnionCharge` packages this as an
`N+3` construction history.  The uniform protected-repair theorem supplies
the four-corner tail; its initial corner is already in that history, so the
whole raw trajectory has at most `N+6` distinct tongue vectors.
-/

namespace GeneralN

/-- **Stable first-contact branch, raw all-times form.**

Suppose two opposite manufactured reflectors are traversed in sequence.  If
the first reflector's support is still grooved at the second reflector's
pre-return endpoint, then every pairwise-distinct family of restricted tongue
vectors sampled anywhere on the complete trajectory has size at most `N+6`.

There is no tail certificate in this statement.  The four-vector tail is the
unconditional `manufactured_pair_protected_repair_distinct_le_four`; the
coefficient-one prefix is discharged by the permanent-writer bridge in
`TwoHistoryUnionCharge`.
-/
theorem ManufacturedReflector.preReturn_grooved_all_run_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + 6 := by
  have hreachA := A.manufacturing_journey_reaches_activated hA
  have hreachB := B.manufacturing_journey_reaches_activated hB
  have hreachB' : stepN w
      (B.exploration.length + B.runway.length + 1)
      (e, A.activatedState) = some (g, B.activatedState) := by
    rw [← hbase]
    exact hreachB
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have htail : forall tailTimes : List Nat,
      (forall k, List.Mem k tailTimes ->
        (stepN w k (g, B.activatedState)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup ->
      tailTimes.length <= 4 := by
    intro tailTimes htailLive htailNodup
    exact manufactured_pair_protected_repair_distinct_le_four
      A B hAatBase hB tailTimes htailLive htailNodup
  exact
    two_manufacturing_journeys_preserved_support_then_four_tail_le_N_add_six
      hN A B A.activatedState B.activatedState
      rfl rfl hreachA hA hbase rfl hreachB' hB hpre htail
      times hlive hnd

/-! ## First damaging contact -/

/-- **Damaging first-contact branch, raw all-times form.**

The literal approach to the first old-support passage which changes a
tongue may contain any number of harmless old-support contacts.  They are
not recursively classified.  `damageContactHistory` compresses that whole
approach to its productive first writers; switch simplicity makes every
such write survive to the contact state, so its writer is outside the old
reusable support.  The two disjoint coordinate sets cost at most `N`, the
two construction boundaries cost three, and the classified contact tail
costs two more.
-/
theorem ManufacturedReflector.first_damaging_contact_all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (C : SecondHistoryContactData w A B)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    {next : Tongues}
    (harrive : arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged : Ne (next (C.fresh.1 / 3))
      (C.contactState (C.fresh.1 / 3)))
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + 5 := by
  let firstTravel :=
    A.exploration.length + A.runway.length + 1
  let localTimes :=
    (times.filter (fun k => decide (firstTravel < k))).map
      (fun k => k - firstTravel)
  let history := C.damageContactHistory N next
  have hreachA :
      stepN w firstTravel (g, A.baseState) =
        some (e, A.activatedState) := by
    simpa [firstTravel] using
      A.manufacturing_journey_reaches_activated hA
  have hreachBoundary :
      stepN w firstTravel (g, A.baseState) =
        some (e, B.baseState) := by
    simpa [hbase] using hreachA
  have hlocalCover :
      NoveltyCoverOn w N (e, B.baseState) localTimes history 2 := by
    dsimp [localTimes, history]
    exact C.changed_contact_two_novelty_charged
      harrive hchanged _
  obtain ⟨fresh, hfreshLength, hlocalMem⟩ := hlocalCover
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times history 2 := by
    refine ⟨fresh, hfreshLength, ?_⟩
    intro k hk
    by_cases hprefix : k <= firstTravel
    . have hm := A.manufacturing_journey_mem_sharpHistory
        (N := N) hA (j := k) (by
          simpa [firstTravel] using hprefix)
      apply List.mem_append_left
      dsimp [history]
      unfold SecondHistoryContactData.damageContactHistory
      exact List.mem_append_left _
        (A.mem_sharpHistoryCore_of_mem hm)
    . have hafter : firstTravel < k := by omega
      let q := k - firstTravel
      have hkEq : k = firstTravel + q := by
        dsimp [q]
        omega
      have hkFiltered :
          List.Mem k
            (times.filter (fun t => decide (firstTravel < t))) := by
        apply List.mem_filter.mpr
        exact And.intro hk (by simp [hafter])
      have hqMem : List.Mem q localTimes := by
        dsimp [localTimes]
        apply List.mem_map.mpr
        exact ⟨k, hkFiltered, rfl⟩
      have hglobalLive := hlive k hk
      have hlocalLive :
          (stepN w q (e, B.baseState)).isSome := by
        rw [hkEq, stepN_add, hreachBoundary] at hglobalLive
        exact hglobalLive
      have hlocalExists : exists finish,
          stepN w q (e, B.baseState) = some finish := by
        cases hrun : stepN w q (e, B.baseState) with
        | none =>
            simp [hrun] at hlocalLive
        | some finish =>
            exact ⟨finish, rfl⟩
      have hshift :=
        tonguesAt_add_of_reaches hreachBoundary hlocalExists
      have hvector :
          restrictedTonguesAt w N (g, A.baseState) k =
            restrictedTonguesAt w N (e, B.baseState) q := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [hvector]
      exact hlocalMem q hqMem
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  have hhistory : history.length <= N + 3 := by
    dsimp [history]
    exact C.damageContactHistory_length_le_N_add_three
      hN hbase hbaseGrooves next
  omega

/-- The exact non-recursive split requested by the first-contact argument.
Either the old support is still grooved at the second pre-return, or the
first passage which damages that support yields physical contact data and
an actual tongue change.  Earlier harmless contacts remain inside
`C.approach`; they are never turned into recursive residual problems. -/
theorem ManufacturedReflector.preReturn_grooved_or_first_damaging_contact
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState) :
    PathGrooves A.toSupported.paths B.preReturn.2 \/
      exists C : SecondHistoryContactData w A B, exists next : Tongues,
        And (arrive C.contactState C.fresh.1 = (C.fresh.2, next))
          (Ne (next (C.fresh.1 / 3))
            (C.contactState (C.fresh.1 / 3))) := by
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hA
  by_cases hpre : PathGrooves A.toSupported.paths B.preReturn.2
  . exact Or.inl hpre
  . right
    obtain ⟨approach, p, x, suffix, u, v, path, old,
        hsplit, hprefix, hgrooves, harrive,
        hpath, hold, hswitch, hchanged, _hExit⟩ :=
      B.exploration_trace.first_changed_support_passage
        hbaseGrooves hpre
    have hfull := B.exploration_trace
    rw [hsplit] at hfull
    obtain ⟨middle, hbefore, hafter⟩ := hfull.split_append
    have hmiddle : middle = (p, u) := by
      have h1 := hbefore.sound
      have h2 := hprefix.sound
      rw [h2] at h1
      exact (Option.some.inj h1).symm
    subst middle
    let C : SecondHistoryContactData w A B := {
      approach := approach
      fresh := (p, x)
      suffix := suffix
      contactState := u
      split := hsplit
      approach_trace := hprefix
      suffix_trace := hafter
      old_grooves := hgrooves
      touches := ⟨path, hpath, old, hold, by
        simpa [passageSwitch] using hswitch⟩
    }
    refine ⟨C, v, ?_, ?_⟩
    . simpa [C] using harrive
    . simpa [C] using hchanged

/-- **First-contact Gray-tail theorem.**

For two opposite manufactured reflectors, every duplicate-free family of
raw restricted tongue vectors sampled at arbitrary live times has cardinality
at most `N+6`.  This theorem has no recursive residual, no tail certificate,
and no auxiliary hypothesis: preserved support takes the verified four-tail
branch, while damaged support stops at its first changing passage and takes
the charged two-novelty branch.
-/
theorem ManufacturedReflector.first_contact_gray_tail_all_run_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hA : PathGrooves A.toSupported.paths A.activatedState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + 6 := by
  rcases A.preReturn_grooved_or_first_damaging_contact
      B hbase hA with hpre | ⟨C, next, harrive, hchanged⟩
  . exact A.preReturn_grooved_all_run_distinct_le_N_add_six
      hN B hbase hA hB hpre times hlive hnd
  . have hdamage : times.length <= N + 5 :=
      A.first_damaging_contact_all_run_distinct_le_N_add_five
        hN B C hbase hA harrive hchanged times hlive hnd
    omega

end GeneralN
