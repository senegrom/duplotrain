import RunwaySpliceNovelty
import SharpStateLawAssembly

/-!
# Raw time shifting and switch-simple traces

Shifting a run to a reached local start preserves its restricted tongue
vectors, its liveness, and its raw writer names, and a physical trace names
the writer of every productive step by its passage switch.  On a
switch-simple trace no repeated-writer novelty occurs, and every vector of
the trace already lies in the first-writer history.  These are the
time-indexed facts the global history extraction of the sharp bound uses.
-/

namespace GeneralN

/-- A raw trajectory shifted to a reached configuration has exactly the same
restricted tongue vectors. -/
theorem restrictedTonguesAt_add_of_reach
    {w : Wiring} {N shift d : Nat}
    {start middle finish : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hfinish : stepN w d middle = some finish) :
    restrictedTonguesAt w N start (shift + d) =
      restrictedTonguesAt w N middle d := by
  simp [restrictedTonguesAt, tonguesAt, stepN_add, hreach, hfinish]

/-- A successful absolute suffix of a reached raw configuration is a
successful local suffix.  This tiny transport fact lets the global-history
argument use the local changed-forward novelty theorem without assuming an
all-time liveness oracle. -/
theorem stepN_suffix_some_of_reach
    {w : Wiring} {shift d : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hglobal : (stepN w (shift + d) start).isSome) :
    ∃ finish, stepN w d middle = some finish := by
  rw [stepN_add, hreach] at hglobal
  simpa using (Option.isSome_iff_exists.mp hglobal)

/-- Transport one live post-time from an ambient raw run to a reached local
run. -/
theorem restrictedTonguesAt_sub_of_reach
    {w : Wiring} {N shift t : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hshift : shift ≤ t)
    (hlive : (stepN w t start).isSome) :
    restrictedTonguesAt w N start t =
      restrictedTonguesAt w N middle (t - shift) := by
  have ht : t = shift + (t - shift) := by omega
  have hglobal' :
      (stepN w (shift + (t - shift)) start).isSome := by
    rw [← ht]
    exact hlive
  obtain ⟨finish, hfinish⟩ := stepN_suffix_some_of_reach
    hreach hglobal'
  have htransport := restrictedTonguesAt_add_of_reach
    (N := N) hreach hfinish
  rw [← ht] at htransport
  exact htransport

/-- Raw writer names are invariant under shifting to a reached local run. -/
theorem rawWriterAt_add_of_reach
    {w : Wiring} {shift d : Nat}
    {start middle : Nat × Tongues}
    (hreach : stepN w shift start = some middle)
    (hlive : (stepN w d middle).isSome) :
    rawWriterAt w start (shift + d) =
      rawWriterAt w middle d := by
  obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hlive
  simp [rawWriterAt, rawEntryAt, stepN_add, hreach, hfinish]


theorem PhysicalTrace.rawWriterAt_eq_passageSwitch_getElem
    {w : Wiring} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish) :
    ∀ {k : Nat} (hk : k < passages.length),
      rawWriterAt w start k = passageSwitch passages[k] := by
  intro k hk
  induction htrace generalizing k with
  | nil => simp at hk
  | @cons p x q u v passages finish harrive hlink tail ih =>
      cases k with
      | zero =>
          simp [rawWriterAt, rawEntryAt, stepN, passageSwitch]
      | succ k =>
          have hkTail : k < passages.length := by
            simp only [List.length_cons] at hk
            omega
          have hstep : step w (p, u) = some (q, v) := by
            simp [step, harrive, hlink]
          have hreach : stepN w 1 (p, u) = some (q, v) := by
            simpa [stepN] using hstep
          obtain ⟨cfg, hcfg⟩ := stepN_prefix_some
            (d := k) (K := passages.length)
            (Nat.le_of_lt hkTail) tail.sound
          have hcfgSome : (stepN w k (q, v)).isSome := by
            rw [hcfg]
            simp
          have hwriter := rawWriterAt_add_of_reach hreach hcfgSome
          have htail := ih hkTail
          simpa [Nat.one_add] using hwriter.trans htail

/-- Every productive event inside a switch-simple physical construction is
globally the first productive event of its writer.  This is the raw-history
extraction missing from the older five-frame formulation: passage simplicity
controls the complete absolute run prefix, not merely a local certificate. -/
theorem PhysicalTrace.rawProductiveAt_first_of_switchSimple
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    ∀ {k : Nat}, k < passages.length →
      RawProductiveAt w N start k →
      RawFirstWriterAt w N start k := by
  intro k hk hprod
  refine ⟨hprod, ?_⟩
  intro j hj hprodj hwriter
  have hjBound : j < passages.length := Nat.lt_trans hj hk
  have hwriterJ := htrace.rawWriterAt_eq_passageSwitch_getElem hjBound
  have hwriterK := htrace.rawWriterAt_eq_passageSwitch_getElem hk
  have hpair := List.pairwise_iff_getElem.mp hsimple
  have hne := hpair j k (by simpa using hjBound) (by simpa using hk) hj
  apply hne
  simpa [hwriterJ, hwriterK] using hwriter

/-- A switch-simple physical construction prefix contains no repeated-writer
novelty event.  This is the event-level form of the global history
extraction, and follows from the time-indexed passage theorem above. -/
theorem PhysicalTrace.rawRepeatedWriterNovelTimes_eq_nil_of_switchSimple
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    rawRepeatedWriterNovelTimes w N start passages.length = [] := by
  cases htimes : rawRepeatedWriterNovelTimes w N start passages.length with
  | nil => rfl
  | cons k rest =>
      exfalso
      have hkMem :
          k ∈ rawRepeatedWriterNovelTimes w N start passages.length := by
        rw [htimes]
        exact List.mem_cons_self
      have hkData := mem_rawRepeatedWriterNovelTimes_iff.mp hkMem
      have hkFirst := htrace.rawProductiveAt_first_of_switchSimple
        hsimple hkData.1 hkData.2.1
      exact hkData.2.2.1 hkFirst

/-- Every state of a switch-simple physical construction prefix belongs to
the canonical initial-plus-first-writer history.  This is an unconditional
global raw-history extraction, including the endpoint of the trace. -/
theorem PhysicalTrace.restrictedTonguesAt_mem_rawFirstWriterHistory
    {w : Wiring} {N : Nat} {start finish : Nat × Tongues}
    {passages : List Passage}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages) :
    ∀ k, k ≤ passages.length →
      restrictedTonguesAt w N start k ∈
        rawFirstWriterHistory w N start passages.length := by
  intro k hk
  have hcover := restrictedTonguesAt_mem_finite_writer_cover
    w N start passages.length k hk
  have hempty :=
    htrace.rawRepeatedWriterNovelTimes_eq_nil_of_switchSimple
      (N := N) hsimple
  unfold rawRepeatedWriterFresh at hcover
  rw [hempty] at hcover
  simpa using hcover

end GeneralN
