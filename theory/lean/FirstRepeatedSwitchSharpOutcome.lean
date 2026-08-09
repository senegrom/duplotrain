import FirstWriterRetraceFree
import FiveFrameObstruction
import SharpCertificateClosure

/-!
# The sharp outcome of the first repeated switch

`five_serial_novelties_force_exact_caller_retrace` closes the local
first-revisit fork in the serial five-frame branch: the simple-cycle outcome
is incompatible with the later globally novel frames, so the train must
retrace the complete caller runway.

That exact retrace is not, by itself, a four-novelty theorem.  The returned
configuration can still be globally new.  The first section retains an
earlier complete-configuration diagnostic:

* if the caller return finishes no later than the post-state of the first
  repeated novelty, then its complete configuration has never occurred
  before;
* hence the serial branch produces either a return which runs past that
  post-state, or a genuinely fresh complete-configuration return.

The second alternative is only a diagnostic and is superseded below for the
known-edge setting used by `StateLaw`.
`five_serial_novelties_completed_retrace_one_novelty` is stronger: the caller
return completes before the first closing novelty and has one constant
settled vector.  The final section below proves that, when this is the first
repeated-writer novelty, both contact vectors and the entire completed
retrace are already paid for by `rawFirstWriterHistory`.  It then proves the
exact cancellation requested for a later outward first-writer turn: the
physical reverse is forced, its close vector equals the first-writer
post-vector, and a repeated novel close inside that reverse is impossible.

No bounded enumeration, irreflexivity assumption, or unproved extraction
premise occurs here.
-/

namespace GeneralN

/-- The raw run reaches a complete configuration for the first time at
`time`.  This is stronger than freshness of the represented `N`-tongue
vector because it also fixes the train's entry port. -/
def RawFreshConfigurationAt
    (w : Wiring) (start : Nat × Tongues) (time : Nat) : Prop :=
  ∃ configuration,
    stepN w time start = some configuration ∧
    ∀ earlier, earlier < time →
      stepN w earlier start ≠ some configuration

/-- A novel post-state forbids every earlier complete-configuration replay
on the prefix leading to it.  Equal complete configurations have equal
deterministic suffixes, so such a replay would make the post-state's
restricted tongue vector occur at an earlier raw time. -/
theorem RawRepeatedWriterNovelAt.no_complete_replay_before_post
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {close : Nat}
    (H : RawRepeatedWriterNovelAt w N start close)
    {time earlier : Nat} {configuration : Nat × Tongues}
    (htime : time ≤ close + 1)
    (hearlier : earlier < time)
    (hreachedEarlier :
      stepN w earlier start = some configuration)
    (hreachedTime :
      stepN w time start = some configuration) : False := by
  let suffix := close + 1 - time
  have htimeSuffix : time + suffix = close + 1 := by
    dsimp [suffix]
    omega
  have hearlierSuffix : earlier + suffix < close + 1 := by
    dsimp [suffix]
    omega
  have hsameSuffix :
      stepN w (earlier + suffix) start =
        stepN w (close + 1) start := by
    calc
      stepN w (earlier + suffix) start =
          stepN w suffix configuration := by
        simp only [stepN_add, hreachedEarlier, Option.bind_some]
      _ = stepN w (time + suffix) start := by
        simp only [stepN_add, hreachedTime, Option.bind_some]
      _ = stepN w (close + 1) start := by
        rw [htimeSuffix]
  have hsameVector :
      restrictedTonguesAt w N start (earlier + suffix) =
        restrictedTonguesAt w N start (close + 1) := by
    simpa [restrictedTonguesAt, tonguesAt] using
      congrArg
        (fun result : Option (Nat × Tongues) =>
          VectorCount.restrict N (result.getD start).2)
        hsameSuffix
  apply H.2.2
  apply List.mem_map.mpr
  exact ⟨earlier + suffix,
    List.mem_range.mpr hearlierSuffix, hsameVector⟩

/-- At every time up to a repeated novelty's post-state, the complete
configuration is fresh.  Otherwise deterministic replay contradicts the
novel post-vector.  Times beyond the post-state form the only alternative. -/
theorem RawRepeatedWriterNovelAt.late_or_fresh_configuration
    {w : Wiring} {N : Nat} {start : Nat × Tongues} {close : Nat}
    (H : RawRepeatedWriterNovelAt w N start close)
    (time : Nat) :
    close + 1 < time ∨ RawFreshConfigurationAt w start time := by
  by_cases hlate : close + 1 < time
  · exact Or.inl hlate
  · right
    have htime : time ≤ close + 1 := by omega
    obtain ⟨post, hpost⟩ := Option.isSome_iff_exists.mp H.1.1
    let suffix := close + 1 - time
    have hsplit : close + 1 = time + suffix := by
      dsimp [suffix]
      omega
    cases hreached : stepN w time start with
    | none =>
        rw [hsplit, stepN_add, hreached] at hpost
        contradiction
    | some configuration =>
        refine ⟨configuration, hreached, ?_⟩
        intro earlier hearlier hreplay
        exact H.no_complete_replay_before_post
          htime hearlier hreplay hreached

/-- Exact raw outcome forced by five serial repeated novelties.  Besides the
physical caller retrace, the structure exposes the only conclusion justified
about that return without a further global repair theorem: it is late, or it
lands in a first-ever complete configuration. -/
structure SerialCallerReturnEscape
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (close : Nat) where
  openTime : Nat
  before : Nat × Tongues
  atRepeat : Nat × Tongues
  repeatTime : Nat
  backSteps : Nat
  settled : Tongues
  reaches_before : stepN w openTime start = some before
  reaches_repeat : stepN w repeatTime start = some atRepeat
  repeat_after_open : openTime ≤ repeatTime
  repeat_before_close : repeatTime < close
  back_positive : 0 < backSteps
  back_bounded : backSteps ≤ N + 1
  exact_caller_return :
    stepN w backSteps atRepeat =
      (w.link before.1).map (fun ell => (ell, settled))
  absolute_caller_return :
    stepN w (repeatTime + backSteps) start =
      (w.link before.1).map (fun ell => (ell, settled))
  late_or_fresh :
    close + 1 < repeatTime + backSteps ∨
      RawFreshConfigurationAt w start (repeatTime + backSteps)

/-- **Early complete-configuration diagnostic for the serial branch.**

The concrete first repeated switch cannot settle on its simple-cycle branch;
it retraces its caller exactly.  The completed return then either lies after
the first novelty's post-state, or is a globally fresh complete
configuration.  The later exact-cancellation section replaces freshness as
the useful charge once a known incoming edge and a first-writer turn are
available. -/
theorem five_serial_novelties_force_caller_return_escape
    {w : Wiring} {N : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (H₀ : RawRepeatedWriterNovelAt w N start z₀)
    (H₁ : RawRepeatedWriterNovelAt w N start z₁)
    (H₂ : RawRepeatedWriterNovelAt w N start z₂)
    (H₃ : RawRepeatedWriterNovelAt w N start z₃)
    (H₄ : RawRepeatedWriterNovelAt w N start z₄)
    {a₀ q₀ a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄ : Nat}
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hserial : FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄) :
    Nonempty (SerialCallerReturnEscape w N start z₀) := by
  obtain ⟨before, atRepeat, repeatTime, backSteps, settled,
      hbefore, hrepeat, hopen, hbeforeClose, hbackPositive,
      hbackBounded, hreturn⟩ :=
    five_serial_novelties_force_exact_caller_retrace
      hN H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  have habsolute :
      stepN w (repeatTime + backSteps) start =
        (w.link before.1).map (fun ell => (ell, settled)) := by
    rw [stepN_add, hrepeat]
    exact hreturn
  exact ⟨{
    openTime := a₀
    before := before
    atRepeat := atRepeat
    repeatTime := repeatTime
    backSteps := backSteps
    settled := settled
    reaches_before := hbefore
    reaches_repeat := hrepeat
    repeat_after_open := hopen
    repeat_before_close := hbeforeClose
    back_positive := hbackPositive
    back_bounded := hbackBounded
    exact_caller_return := hreturn
    absolute_caller_return := habsolute
    late_or_fresh :=
      H₀.late_or_fresh_configuration (repeatTime + backSteps)
  }⟩

/-! ## The first-writer charge after exact retrace -/

/-- Before the first repeated-writer novelty, every represented tongue vector
belongs to the initial-plus-first-writer history.  The generic finite writer
cover has a repeated-novelty summand, but that summand cannot contain a prefix
vector: an event before `first` contradicts `hfirst`, while an event at or
after `first` is novel relative to that earlier prefix time. -/
theorem restrictedTonguesAt_mem_firstHistory_before_first_repeated
    {w : Wiring} {N : Nat} {start : Nat × Tongues}
    {first K time : Nat}
    (hfirst : ∀ k, k < first →
      ¬ RawRepeatedWriterNovelAt w N start k)
    (hfirstK : first ≤ K)
    (htime : time ≤ first) :
    restrictedTonguesAt w N start time ∈
      rawFirstWriterHistory w N start K := by
  have hcovered :=
    restrictedTonguesAt_mem_finite_writer_cover
      w N start K time (by omega)
  rcases List.mem_append.mp hcovered with hhistory | hrepeated
  · exact hhistory
  · obtain ⟨k, hk, hvector⟩ := List.mem_map.mp hrepeated
    have Hk : RawRepeatedWriterNovelAt w N start k :=
      (mem_rawRepeatedWriterNovelTimes_iff.mp hk).2
    by_cases hkfirst : k < first
    · exact (hfirst k hkfirst Hk).elim
    · have htimeBefore : time < k + 1 := by omega
      exact (Hk.2.2.post_ne_earlier htimeBefore hvector).elim

/-- **First-writer-history invariant for the serial first repeat.**

Assume `z₀` is the first repeated-writer novelty of the raw run.  In the
serial five-frame branch, choose the later frame whose opening lies after
`z₀`.  The exact caller retrace completes before `z₀`, hence before that later
productive opening.  Its contact vector and its constant settled vector both
occur no later than `z₀`, so both are in `rawFirstWriterHistory`.  Therefore
every sample on the complete retrace has a zero-exception novelty cover over
that history.

This is the raw induction invariant suggested by the first-repeat proof: the
backward segment itself spends no repeated-novelty budget.  Any later failure
to replay or settle must occur after the returned input edge; the remaining
task is to show that its first genuine forward escape is a first writer (or
enters the already proved two-reflector Gray tail). -/
theorem five_serial_first_retrace_is_first_writer_history
    {w : Wiring} {N initialEdge K : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (H₀ : RawRepeatedWriterNovelAt w N start z₀)
    (H₁ : RawRepeatedWriterNovelAt w N start z₁)
    (H₂ : RawRepeatedWriterNovelAt w N start z₂)
    (H₃ : RawRepeatedWriterNovelAt w N start z₃)
    (H₄ : RawRepeatedWriterNovelAt w N start z₄)
    (hfirst : ∀ k, k < z₀ →
      ¬ RawRepeatedWriterNovelAt w N start k)
    (hz₀K : z₀ ≤ K)
    {a₀ q₀ a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄ : Nat}
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hserial : FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄) :
    ∃ (laterOpen repeatTime : Nat) (caller : List Passage)
        (q : Nat) (u settled : Tongues) (edge : Nat),
      RawProductiveAt w N start laterOpen ∧
      z₀ ≤ laterOpen ∧
      stepN w repeatTime start = some (q, u) ∧
      stepN w (caller.length + 1) (q, u) = some (edge, settled) ∧
      repeatTime + caller.length + 1 ≤ z₀ ∧
      repeatTime + caller.length + 1 ≤ laterOpen ∧
      VectorCount.restrict N u ∈
        rawFirstWriterHistory w N start K ∧
      VectorCount.restrict N settled ∈
        rawFirstWriterHistory w N start K ∧
      (∀ time, time ≤ z₀ →
        restrictedTonguesAt w N start time ∈
          rawFirstWriterHistory w N start K) ∧
      (∀ times,
        (∀ time, time ∈ times →
          repeatTime ≤ time ∧
          time ≤ repeatTime + caller.length + 1) →
        NoveltyCoverOn w N start times
          (rawFirstWriterHistory w N start K) 0) := by
  obtain ⟨_g, _base, _oldEntry, _mouthState, q, u, settled,
      edge, repeatTime, caller, _hbefore, _hcaller, _hsimple,
      _hgrooved, _hcallerLe, _hedge, hrepeat, _hopen,
      hrepeatBeforeClose, hreturnBeforeClose, _hcontact,
      hreturn, hpointwise, _honeCover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  obtain ⟨laterOpen, hcloseOpen, hlaterProductive⟩ :
      ∃ laterOpen, z₀ ≤ laterOpen ∧
        RawProductiveAt w N start laterOpen := by
    rcases hserial with h₁ | h₂ | h₃ | h₄
    · exact ⟨a₁, h₁, F₁.outer.open_productive⟩
    · exact ⟨a₂, h₂, F₂.outer.open_productive⟩
    · exact ⟨a₃, h₃, F₃.outer.open_productive⟩
    · exact ⟨a₄, h₄, F₄.outer.open_productive⟩
  have hprefixHistory : ∀ time, time ≤ z₀ →
      restrictedTonguesAt w N start time ∈
        rawFirstWriterHistory w N start K := by
    intro time htime
    exact restrictedTonguesAt_mem_firstHistory_before_first_repeated
      hfirst hz₀K htime
  have huHistory : VectorCount.restrict N u ∈
      rawFirstWriterHistory w N start K := by
    have hvector : restrictedTonguesAt w N start repeatTime =
        VectorCount.restrict N u := by
      simp [restrictedTonguesAt, tonguesAt, hrepeat]
    rw [← hvector]
    exact hprefixHistory repeatTime (by omega)
  obtain ⟨portOne, hlocalOne⟩ := hpointwise 1 (by omega)
  have hglobalOne : stepN w (repeatTime + 1) start =
      some (portOne, settled) := by
    rw [stepN_add, hrepeat]
    simpa using hlocalOne
  have hsettledHistory : VectorCount.restrict N settled ∈
      rawFirstWriterHistory w N start K := by
    have hvector : restrictedTonguesAt w N start (repeatTime + 1) =
        VectorCount.restrict N settled := by
      simp [restrictedTonguesAt, tonguesAt, hglobalOne]
    rw [← hvector]
    exact hprefixHistory (repeatTime + 1) (by omega)
  have hzeroCover : ∀ times,
      (∀ time, time ∈ times →
        repeatTime ≤ time ∧
        time ≤ repeatTime + caller.length + 1) →
      NoveltyCoverOn w N start times
        (rawFirstWriterHistory w N start K) 0 := by
    intro times htimes
    refine ⟨[], by simp, ?_⟩
    intro time htime
    simp only [List.append_nil]
    have hb := htimes time htime
    let d := time - repeatTime
    have hdLe : d ≤ caller.length + 1 := by
      dsimp [d]
      omega
    have htimeEq : repeatTime + d = time := by
      dsimp [d]
      omega
    obtain ⟨port, hlocal⟩ := hpointwise d hdLe
    have hglobal : stepN w time start =
        some (port, if d = 0 then u else settled) := by
      rw [← htimeEq, stepN_add, hrepeat]
      exact hlocal
    have hvector : restrictedTonguesAt w N start time =
        VectorCount.restrict N (if d = 0 then u else settled) := by
      simp [restrictedTonguesAt, tonguesAt, hglobal]
    rw [hvector]
    by_cases hd : d = 0
    · simpa [hd] using huHistory
    · simpa [hd] using hsettledHistory
  exact ⟨laterOpen, repeatTime, caller, q, u, settled, edge,
    hlaterProductive, hcloseOpen, hrepeat, hreturn,
    hreturnBeforeClose, by omega, huHistory, hsettledHistory,
    hprefixHistory, hzeroCover⟩

/-! ## Exact cancellation after a first-writer turn -/

/-- Absolute time of the turning event in a switch-simple outward
exploration which starts after a completed caller return. -/
def outwardTurnTime (returnTime : Nat)
    (runway loop : List Passage) : Nat :=
  returnTime + (runway.length + (loop.length + 1))

/-- **Exact first-writer cancellation theorem.**

Start from a configuration reached after a completed caller return.  Follow a
switch-simple runway and excursion to the first revisited switch.  If the
revisit exits through the old runway mouth, it is a genuine turn: the train
traverses the complete runway backwards and returns over its incoming edge.

When that turning step is a globally first productive writer, the tongue
vector at every positive depth of the reverse is the turning step's
post-vector.  In particular the final return vector is exactly that
first-writer post-vector and is already present in `rawFirstWriterHistory`.

This theorem derives the reverse from physical track data and delegates only
the zero-cost accounting to `FirstWriterRetraceFree`; it assumes neither a
tail certificate nor the desired vector equality. -/
theorem completed_return_first_writer_turn_exact_cancellation
    {w : Wiring} {N horizon returnTime edge g p x q : Nat}
    {global : Nat × Tongues}
    {base mouthState u v : Tongues}
    {runway loop : List Passage}
    (hreturn : stepN w returnTime global = some (g, base))
    (hrunway :
      PhysicalTrace w (g, base) runway (p, mouthState))
    (hexcursion :
      PhysicalTrace w (p, mouthState) ((p, x) :: loop) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: loop))
    (hsameSwitch : p / 3 = q / 3)
    (hcontact : arrive u q = (p, v))
    (hentry : w.link edge = some g)
    (hfirst : RawFirstWriterAt w N global
      (outwardTurnTime returnTime runway loop))
    (hturnBeforeHorizon :
      outwardTurnTime returnTime runway loop < horizon) :
    PhysicalTrace w (q, u)
        ((q, p) :: reversePassages runway) (edge, v) ∧
      stepN w (runway.length + 1) (q, u) = some (edge, v) ∧
      stepN w
          (outwardTurnTime returnTime runway loop +
            runway.length + 1) global = some (edge, v) ∧
      restrictedTonguesAt w N global
          (outwardTurnTime returnTime runway loop +
            runway.length + 1) =
        restrictedTonguesAt w N global
          (outwardTurnTime returnTime runway loop + 1) ∧
      restrictedTonguesAt w N global
          (outwardTurnTime returnTime runway loop +
            runway.length + 1) ∈
        rawFirstWriterHistory w N global horizon := by
  let turn := outwardTurnTime returnTime runway loop
  have hturnReach : stepN w turn global = some (q, u) := by
    dsimp [turn, outwardTurnTime]
    rw [stepN_add, hreturn]
    simpa using (hrunway.append hexcursion).sound
  have hsupport : PathGrooves [runway, loop] v :=
    crossed_revisit_support_grooved
      hrunway hexcursion hsimple hsameSwitch hcontact
  have hgrooved : PassagesGrooved v runway :=
    (pathGrooves_pair.mp hsupport).1
  have hreverse : PhysicalTrace w (q, u)
      ((q, p) :: reversePassages runway) (edge, v) :=
    physicalTrace_contact_retraces_prefix
      hrunway hgrooved hentry hcontact
  have hlocalReturn :
      stepN w (runway.length + 1) (q, u) = some (edge, v) := by
    have hsound := hreverse.sound
    simpa [reversePassages_length] using hsound
  have habsoluteReturn :
      stepN w (turn + runway.length + 1) global =
        some (edge, v) := by
    rw [show turn + runway.length + 1 =
        turn + (runway.length + 1) by omega,
      stepN_add, hturnReach]
    exact hlocalReturn
  have hcancel :
      restrictedTonguesAt w N global
          (turn + runway.length + 1) =
        restrictedTonguesAt w N global (turn + 1) :=
    completed_retrace_endpoint_eq_turn_post
      hrunway hgrooved hentry hcontact hturnReach
  have hreturnVector :
      restrictedTonguesAt w N global
          (turn + runway.length + 1) =
        VectorCount.restrict N v :=
    completed_retrace_at_positive_vector_eq_contact
      hrunway hgrooved hentry hcontact hturnReach
        (j := turn + runway.length + 1) (by omega) (by omega)
  have hcontactHistory : VectorCount.restrict N v ∈
      rawFirstWriterHistory w N global horizon :=
    first_writer_retrace_contact_mem_history
      hrunway hgrooved hentry hcontact hturnReach hfirst
        hturnBeforeHorizon
  have hreturnHistory :
      restrictedTonguesAt w N global
          (turn + runway.length + 1) ∈
        rawFirstWriterHistory w N global horizon := by
    rw [hreturnVector]
    exact hcontactHistory
  change PhysicalTrace w (q, u)
        ((q, p) :: reversePassages runway) (edge, v) ∧
      stepN w (runway.length + 1) (q, u) = some (edge, v) ∧
      stepN w (turn + runway.length + 1) global = some (edge, v) ∧
      restrictedTonguesAt w N global
          (turn + runway.length + 1) =
        restrictedTonguesAt w N global (turn + 1) ∧
      restrictedTonguesAt w N global
          (turn + runway.length + 1) ∈
        rawFirstWriterHistory w N global horizon
  exact ⟨hreverse, hlocalReturn, habsoluteReturn,
    hcancel, hreturnHistory⟩

/-- A repeated-writer novelty cannot close during the reverse generated by a
globally first-writer turn.  Its alleged post-vector is literally the
first-writer post-vector, at an earlier raw time, and is therefore both
historical and non-novel. -/
theorem completed_return_first_writer_turn_cancels_novel_close
    {w : Wiring} {N horizon returnTime close edge g p x q : Nat}
    {global : Nat × Tongues}
    {base mouthState u v : Tongues}
    {runway loop : List Passage}
    (hreturn : stepN w returnTime global = some (g, base))
    (hrunway :
      PhysicalTrace w (g, base) runway (p, mouthState))
    (hexcursion :
      PhysicalTrace w (p, mouthState) ((p, x) :: loop) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: loop))
    (hsameSwitch : p / 3 = q / 3)
    (hcontact : arrive u q = (p, v))
    (hentry : w.link edge = some g)
    (hfirst : RawFirstWriterAt w N global
      (outwardTurnTime returnTime runway loop))
    (hturnBeforeHorizon :
      outwardTurnTime returnTime runway loop < horizon)
    (hcloseAfterTurn :
      outwardTurnTime returnTime runway loop < close)
    (hcloseInsideReverse :
      close + 1 ≤ outwardTurnTime returnTime runway loop +
        runway.length + 1) :
    restrictedTonguesAt w N global (close + 1) =
        restrictedTonguesAt w N global
          (outwardTurnTime returnTime runway loop + 1) ∧
      restrictedTonguesAt w N global (close + 1) ∈
        rawFirstWriterHistory w N global horizon ∧
      ¬ RawNovelAt w N global close ∧
      ¬ RawRepeatedWriterNovelAt w N global close := by
  let turn := outwardTurnTime returnTime runway loop
  have hturnReach : stepN w turn global = some (q, u) := by
    dsimp [turn, outwardTurnTime]
    rw [stepN_add, hreturn]
    simpa using (hrunway.append hexcursion).sound
  have hsupport : PathGrooves [runway, loop] v :=
    crossed_revisit_support_grooved
      hrunway hexcursion hsimple hsameSwitch hcontact
  have hgrooved : PassagesGrooved v runway :=
    (pathGrooves_pair.mp hsupport).1
  have hturnVector :
      restrictedTonguesAt w N global (turn + 1) =
        VectorCount.restrict N v :=
    completed_retrace_at_positive_vector_eq_contact
      hrunway hgrooved hentry hcontact hturnReach
        (j := turn + 1) (by omega) (by omega)
  have hcloseVector :
      restrictedTonguesAt w N global (close + 1) =
        VectorCount.restrict N v :=
    completed_retrace_at_positive_vector_eq_contact
      hrunway hgrooved hentry hcontact hturnReach
        (j := close + 1) (by
          dsimp [turn]
          omega) (by
          dsimp [turn]
          exact hcloseInsideReverse)
  have hcontactHistory : VectorCount.restrict N v ∈
      rawFirstWriterHistory w N global horizon :=
    first_writer_retrace_contact_mem_history
      hrunway hgrooved hentry hcontact hturnReach hfirst
        hturnBeforeHorizon
  have hcloseHistory :
      restrictedTonguesAt w N global (close + 1) ∈
        rawFirstWriterHistory w N global horizon := by
    rw [hcloseVector]
    exact hcontactHistory
  have hnotNovel : ¬ RawNovelAt w N global close := by
    intro hnovel
    apply hnovel
    apply List.mem_map.mpr
    exact ⟨turn + 1, List.mem_range.mpr (by
      dsimp [turn]
      omega), hturnVector.trans hcloseVector.symm⟩
  change restrictedTonguesAt w N global (close + 1) =
        restrictedTonguesAt w N global (turn + 1) ∧
      restrictedTonguesAt w N global (close + 1) ∈
        rawFirstWriterHistory w N global horizon ∧
      ¬ RawNovelAt w N global close ∧
      ¬ RawRepeatedWriterNovelAt w N global close
  exact ⟨hcloseVector.trans hturnVector.symm, hcloseHistory,
    hnotNovel, fun H => hnotNovel H.2.2⟩

/-- **Precise residual after exact cancellation.**

A globally novel close cannot be at, or anywhere inside, the completed
reverse.  Therefore any surviving serial close lies strictly after the
reverse has returned over the incoming edge.  Notice that this conclusion
does not need the turn to be a first writer; first-writer status is needed
only to charge the repeated contact vector to `rawFirstWriterHistory`. -/
theorem novel_close_after_completed_turn_reverse
    {w : Wiring} {N returnTime close edge g p x q : Nat}
    {global : Nat × Tongues}
    {base mouthState u v : Tongues}
    {runway loop : List Passage}
    (hreturn : stepN w returnTime global = some (g, base))
    (hrunway :
      PhysicalTrace w (g, base) runway (p, mouthState))
    (hexcursion :
      PhysicalTrace w (p, mouthState) ((p, x) :: loop) (q, u))
    (hsimple : SwitchSimple (runway ++ (p, x) :: loop))
    (hsameSwitch : p / 3 = q / 3)
    (hcontact : arrive u q = (p, v))
    (hentry : w.link edge = some g)
    (Hclose : RawNovelAt w N global close)
    (hcloseAfterTurn :
      outwardTurnTime returnTime runway loop < close) :
    outwardTurnTime returnTime runway loop + runway.length < close := by
  let turn := outwardTurnTime returnTime runway loop
  have hturnReach : stepN w turn global = some (q, u) := by
    dsimp [turn, outwardTurnTime]
    rw [stepN_add, hreturn]
    simpa using (hrunway.append hexcursion).sound
  have hsupport : PathGrooves [runway, loop] v :=
    crossed_revisit_support_grooved
      hrunway hexcursion hsimple hsameSwitch hcontact
  have hgrooved : PassagesGrooved v runway :=
    (pathGrooves_pair.mp hsupport).1
  apply Classical.byContradiction
  intro hnot
  have hinside : close + 1 ≤ turn + runway.length + 1 := by
    dsimp [turn] at hnot ⊢
    omega
  have hturnVector :
      restrictedTonguesAt w N global (turn + 1) =
        VectorCount.restrict N v :=
    completed_retrace_at_positive_vector_eq_contact
      hrunway hgrooved hentry hcontact hturnReach
        (j := turn + 1) (by omega) (by omega)
  have hcloseVector :
      restrictedTonguesAt w N global (close + 1) =
        VectorCount.restrict N v :=
    completed_retrace_at_positive_vector_eq_contact
      hrunway hgrooved hentry hcontact hturnReach
        (j := close + 1) (by
          dsimp [turn]
          omega) hinside
  apply Hclose
  apply List.mem_map.mpr
  exact ⟨turn + 1, List.mem_range.mpr (by
    dsimp [turn]
    omega), hturnVector.trans hcloseVector.symm⟩

/-! ## The concrete first post-retrace escape -/

/-- **Raw serial residual with no tail assumption.**

Five serial repeated novelties force an exact caller return.  Select the
first productive event after that completed return, no later than the later
serial close.  It has exactly two possible histories:

* it is a globally first productive writer; or
* its canonical previous write lies at or before the original caller
  contact, exposing a genuine crossing-caller frame.

This is the strongest presently proved classification of the selected
serial continuation.  In the first-writer branch, the cancellation theorems
above apply once that escape is identified as a crossed first-revisit turn.
They then force any novel selected close strictly beyond the completed
reverse; equality after that reverse is deliberately not claimed. -/
theorem five_serial_novelties_first_post_retrace_escape
    {w : Wiring} {N initialEdge : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (hentry : w.link initialEdge = some start.1)
    {z₀ z₁ z₂ z₃ z₄ : Nat}
    (H₀ : RawRepeatedWriterNovelAt w N start z₀)
    (H₁ : RawRepeatedWriterNovelAt w N start z₁)
    (H₂ : RawRepeatedWriterNovelAt w N start z₂)
    (H₃ : RawRepeatedWriterNovelAt w N start z₃)
    (H₄ : RawRepeatedWriterNovelAt w N start z₄)
    {a₀ q₀ a₁ q₁ a₂ q₂ a₃ q₃ a₄ q₄ : Nat}
    (F₀ : RawNovelClosingFrame w N start a₀ q₀ z₀)
    (F₁ : RawNovelClosingFrame w N start a₁ q₁ z₁)
    (F₂ : RawNovelClosingFrame w N start a₂ q₂ z₂)
    (F₃ : RawNovelClosingFrame w N start a₃ q₃ z₃)
    (F₄ : RawNovelClosingFrame w N start a₄ q₄ z₄)
    (hserial : FiveFrameSerialBreak z₀ a₁ a₂ a₃ a₄) :
    ∃ (q : Nat) (old settled : Tongues) (edge repeatTime : Nat)
        (caller : List Passage) (close escape : Nat),
      stepN w repeatTime start = some (q, old) ∧
      stepN w (caller.length + 1) (q, old) =
        some (edge, settled) ∧
      stepN w (repeatTime + caller.length + 1) start =
        some (edge, settled) ∧
      RawRepeatedWriterNovelAt w N start close ∧
      repeatTime + caller.length + 1 ≤ escape ∧
      escape ≤ close ∧
      RawProductiveAt w N start escape ∧
      (∀ t, repeatTime + caller.length + 1 ≤ t → t < escape →
        ¬ RawProductiveAt w N start t) ∧
      (RawFirstWriterAt w N start escape ∨
        ∃ left, RawLastWriterFrame w N start left escape ∧
          left ≤ repeatTime) := by
  obtain ⟨_g, _base, _oldEntry, _mouthState, q, old, settled,
      edge, repeatTime, caller, _hbefore, _hcaller, _hsimple,
      _hgrooved, _hcallerLe, _hedge, hrepeat, _hrepeatAfterOpen,
      _hrepeatBeforeClose, hreturnBeforeClose, _hcontact,
      hlocalReturn, hpointwise, _hcover⟩ :=
    five_serial_novelties_completed_retrace_one_novelty
      hN hentry H₀ H₁ H₂ H₃ H₄ F₀ F₁ F₂ F₃ F₄ hserial
  let span := caller.length + 1
  let returnTime := repeatTime + span
  have habsoluteReturn :
      stepN w returnTime start = some (edge, settled) := by
    dsimp [returnTime, span]
    rw [stepN_add, hrepeat]
    exact hlocalReturn
  obtain ⟨close, Hclose, hreturnClose⟩ :
      ∃ close, RawRepeatedWriterNovelAt w N start close ∧
        returnTime ≤ close := by
    rcases hserial with h₁ | h₂ | h₃ | h₄
    · refine ⟨z₁, H₁, ?_⟩
      dsimp [returnTime, span]
      have horder := F₁.outer.order
      omega
    · refine ⟨z₂, H₂, ?_⟩
      dsimp [returnTime, span]
      have horder := F₂.outer.order
      omega
    · refine ⟨z₃, H₃, ?_⟩
      dsimp [returnTime, span]
      have horder := F₃.outer.order
      omega
    · refine ⟨z₄, H₄, ?_⟩
      dsimp [returnTime, span]
      have horder := F₄.outer.order
      omega
  have hpointwise' : ∀ d, d ≤ span →
      ∃ port, stepN w d (q, old) =
        some (port, if d = 0 then old else settled) := by
    simpa [span] using hpointwise
  obtain ⟨escape, hreturnEscape, hescapeClose, hescapeProductive,
      hminimal, houtcome⟩ :=
    first_productive_escape_first_or_crosses_caller
      hrepeat hpointwise' (by rfl : returnTime = repeatTime + span)
        hreturnClose Hclose.1
  refine ⟨q, old, settled, edge, repeatTime, caller, close, escape,
    hrepeat, hlocalReturn, ?_, Hclose, ?_, hescapeClose,
    hescapeProductive, ?_, houtcome⟩
  · simpa [returnTime, span, Nat.add_assoc] using habsoluteReturn
  · simpa [returnTime, span, Nat.add_assoc] using hreturnEscape
  · intro t ht hte
    apply hminimal t
    · simpa [returnTime, span, Nat.add_assoc] using ht
    · exact hte

end GeneralN
