import KoizumiFramePersistence
import TrackTrace

/-!
# The two-switch one-shot `C,D,C` obstruction

This file adversarially checks the proposed linear-counter gadget: enter an
isolated module containing two lazy points, productively write `C,D,C`, leave
the module, and concatenate disjoint copies.

The raw dynamics has two independent obstructions.

* Two productive visits to the same writer leave through the same fixed stem
  port. If the trace up to the second visit is switch-simple, the second
  visit is therefore the same-direction branch of the first-revisit fork and
  enters an absorbing cycle.
* Without simplicity, every live three-step run in an isolated two-switch
  wiring has already reached the global first-revisit fork: it either never
  falls, or retraces through the input edge. It cannot leave through a new
  output edge to the next disjoint copy.

The self-pivot extraction is retained explicitly: an exact productive word
`C,D,C` has a train-curve self-pivot at `D` or at the closing `C`.

No bounded enumeration, recurrence assumption, or unproved sharp state-law
hypothesis is used.
-/

namespace GeneralN

/-- An exact three-event productive word `C,D,C` on the interval from
`first` to `close`. Quiet raw steps may occur between the three productive
events, but there is no fourth productive event in the open interval. -/
structure RawCDCWord
    (w : Wiring) (N : Nat) (start : Nat × Tongues)
    (C D first middle close : Nat) : Prop where
  first_lt_middle : first < middle
  middle_lt_close : middle < close
  first_productive : RawProductiveAt w N start first
  middle_productive : RawProductiveAt w N start middle
  close_productive : RawProductiveAt w N start close
  first_writer : rawWriterAt w start first = C
  middle_writer : rawWriterAt w start middle = D
  close_writer : rawWriterAt w start close = C
  writers_ne : Not (C = D)
  only_middle : forall j, first < j -> j < close ->
    RawProductiveAt w N start j -> j = middle

/-- The self-anchor consequence of the exact `C,D,C` word. The general
repeated-writer theorem says that a self-pivot occurs at the closing `C` or
strictly inside its frame; exactness of the word identifies an interior
self-pivot with `D`. -/
theorem RawCDCWord.self_at_middle_or_close
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Nat × Tongues} {C D first middle close : Nat}
    (H : RawCDCWord w N start C D first middle close) :
    Or (RawTrainCurveSelfAt w start close)
      (RawTrainCurveSelfAt w start middle) := by
  have hsame : rawWriterAt w start first =
      rawWriterAt w start close :=
    H.first_writer.trans H.close_writer.symm
  rcases repeated_writer_close_self_or_interior_self hN
      (Nat.lt_trans H.first_lt_middle H.middle_lt_close)
      H.first_productive H.close_productive hsame with
    hclose | hinterior
  · exact Or.inl hclose
  · obtain ⟨j, hfirst, hclose, hprod, hself⟩ := hinterior
    have hj : j = middle := H.only_middle j hfirst hclose hprod
    subst j
    exact Or.inr hself

/-- A raw interval together with a switch-simple physical trace certificate.
This certificate is directly checkable against `stepN`; it does not compile
the track into a stronger abstract machine. -/
structure RawSwitchSimpleBetween
    (w : Wiring) (start : Nat × Tongues) (left right : Nat) where
  leftConfig : Nat × Tongues
  rightConfig : Nat × Tongues
  passages : List Passage
  left_at : stepN w left start = some leftConfig
  right_at : stepN w right start = some rightConfig
  length_eq : passages.length = right - left
  trace : PhysicalTrace w leftConfig passages rightConfig
  simple : SwitchSimple passages

/-- A productive revisit of one writer closes into the absorbing
same-direction branch whenever the intervening physical trace is
switch-simple. This is the raw fixed-stem obstruction behind the failure of
the minimal two-switch `C,D,C` module. -/
theorem productive_repeat_simple_frame_settles
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Nat × Tongues} {left right : Nat}
    (horder : left < right)
    (hleft : RawProductiveAt w N start left)
    (hright : RawProductiveAt w N start right)
    (hsame : rawWriterAt w start left = rawWriterAt w start right)
    (S : RawSwitchSimpleBetween w start left right) :
    SettlesOnSimpleCycle w S.rightConfig := by
  obtain ⟨P⟩ := rawProductiveAt_koizumiPivot hN hleft
  obtain ⟨Q⟩ := rawProductiveAt_koizumiPivot hN hright
  have hPcfg : P.before = S.leftConfig :=
    Option.some.inj (P.before_at.symm.trans S.left_at)
  have hQcfg : Q.before = S.rightConfig :=
    Option.some.inj (Q.before_at.symm.trans S.right_at)
  have hwriter : P.writer = Q.writer :=
    P.writer_eq.trans (hsame.trans Q.writer_eq.symm)
  have hbaseTrace : PhysicalTrace w P.before S.passages Q.before := by
    simpa [hPcfg, hQcfg] using S.trace
  cases hpassages : S.passages with
  | nil =>
      have hzero : right - left = 0 := by
        simpa [hpassages] using S.length_eq.symm
      omega
  | cons passage rest =>
      rcases passage with ⟨p, x⟩
      have htrace : PhysicalTrace w P.before ((p, x) :: rest) Q.before := by
        simpa [hpassages] using hbaseTrace
      have hsimple : SwitchSimple ((p, x) :: rest) := by
        simpa [hpassages] using S.simple
      have hp : P.before.1 = p := htrace.head_arrive.1
      obtain ⟨afterOpen, harriveOpen⟩ := htrace.head_arrive.2
      have hx : exitPort P.before = x := by
        unfold exitPort
        rw [hp]
        exact congrArg Prod.fst harriveOpen
      have hxStem : x = 3 * P.writer := by
        rw [← hx, P.exited_stem]
      have hpartsQ := step_some_parts Q.physical_step
      have harriveQ : arrive Q.before.2 Q.before.1 =
          (3 * Q.writer, Q.after.2) := by
        apply Prod.ext
        · exact Q.exited_stem
        · exact hpartsQ.2.symm
      have hnext : arrive Q.before.2 Q.before.1 = (x, Q.after.2) := by
        simpa [hxStem, hwriter] using harriveQ
      have hPpair : P.before = (p, P.before.2) := by
        apply Prod.ext
        · exact hp
        · rfl
      have hQpair : Q.before = (Q.before.1, Q.before.2) := by
        exact Prod.eta Q.before
      have htrace' : PhysicalTrace w (p, P.before.2)
          ((p, x) :: rest) (Q.before.1, Q.before.2) := by
        rw [← hPpair, ← hQpair]
        exact htrace
      have hcycle := htrace'.simple_same_exit_enters_period
        hsimple hnext
      have hresult : SettlesOnSimpleCycle w Q.before := by
        refine ⟨((Q.before.1, x) :: rest).length, Q.after.2,
          by simp, ?_, ?_⟩
        · change stepN w ((Q.before.1, x) :: rest).length
            (Q.before.1, Q.before.2) =
              some (Q.before.1, Q.after.2)
          exact hcycle.1
        · exact hcycle.2
      rw [← hQcfg]
      exact hresult

/-- In particular, a switch-simple exact `C,D,C` frame enters an absorbing
simple cycle at its closing event. -/
theorem RawCDCWord.simple_frame_settles
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Nat × Tongues} {C D first middle close : Nat}
    (H : RawCDCWord w N start C D first middle close)
    (S : RawSwitchSimpleBetween w start first close) :
    SettlesOnSimpleCycle w S.rightConfig := by
  exact productive_repeat_simple_frame_settles hN
    (Nat.lt_trans H.first_lt_middle H.middle_lt_close)
    H.first_productive H.close_productive
    (H.first_writer.trans H.close_writer.symm) S

private theorem stepN_prefix_isSome_local
    {w : Wiring} {start : Nat × Tongues} {small large : Nat}
    (hle : small <= large)
    (hlarge : (stepN w large start).isSome) :
    (stepN w small start).isSome := by
  let rest := large - small
  have hsplit : large = small + rest := by
    dsimp [rest]
    omega
  rw [hsplit, stepN_add] at hlarge
  cases hsmall : stepN w small start with
  | none => simp [hsmall] at hlarge
  | some middle => simp

/-- Settling on a simple cycle means exactly that the train can never fall
off at any later finite time, not merely that one displayed period works. -/
theorem SettlesOnSimpleCycle.never_falls
    {w : Wiring} {config : Nat × Tongues}
    (H : SettlesOnSimpleCycle w config) :
    forall n, (stepN w n config).isSome := by
  obtain ⟨period, settled, hperiodPos, honce, hfixed⟩ := H
  have hsettled : forall n,
      (stepN w n (config.1, settled)).isSome := by
    intro n
    refine Nat.strongRecOn (motive := fun n =>
      (stepN w n (config.1, settled)).isSome) n ?_
    intro n ih
    by_cases hshort : n < period
    · exact stepN_prefix_isSome_local (Nat.le_of_lt hshort)
        (by simp [hfixed])
    · let rest := n - period
      have hperiodLe : period <= n := Nat.le_of_not_gt hshort
      have hrestLt : rest < n := by
        dsimp [rest]
        omega
      have hsplit : n = period + rest := by
        dsimp [rest]
        omega
      rw [hsplit, stepN_add, hfixed]
      exact ih rest hrestLt
  intro n
  by_cases hshort : n < period
  · exact stepN_prefix_isSome_local (Nat.le_of_lt hshort)
      (by simp [honce])
  · let rest := n - period
    have hperiodLe : period <= n := Nat.le_of_not_gt hshort
    have hsplit : n = period + rest := by
      dsimp [rest]
      omega
    rw [hsplit, stepN_add, honce]
    exact hsettled rest

/-- The switch-simple `C,D,C` closure is therefore incompatible with any
later fall-off time. -/
theorem RawCDCWord.simple_frame_never_falls
    {w : Wiring} {N : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Nat × Tongues} {C D first middle close : Nat}
    (H : RawCDCWord w N start C D first middle close)
    (S : RawSwitchSimpleBetween w start first close) :
    forall n, (stepN w n S.rightConfig).isSome :=
  (H.simple_frame_settles hN S).never_falls

/-- **Complete isolated two-switch fork.**

Before cutting either boundary edge, the exact structural result says that
the first repeat either starts a non-falling trajectory or returns over the
plain-track edge attached to the original input port. This explicitly names
the return edge and is the form used when reasoning about gluing modules. -/
theorem two_switch_first_repeat_cycle_or_input_return
    {w : Wiring}
    (hports : forall p q, w.link p = some q ->
      And (p < 6) (q < 6))
    {start finish : Nat × Tongues}
    (hlive : stepN w 3 start = some finish) :
    exists atRepeat visited,
      And (stepN w visited start = some atRepeat)
      (And (visited <= 2)
        (Or (forall n, (stepN w n atRepeat).isSome)
          (exists backSteps, exists settled : Tongues,
            And (backSteps <= 3)
              (stepN w backSteps atRepeat =
                (w.link start.1).map
                  (fun ell => (ell, settled)))))) := by
  have hN : forall p q, w.link p = some q ->
      And (p < 3 * 2) (q < 3 * 2) := by
    intro p q hlink
    have h := hports p q hlink
    omega
  obtain ⟨atRepeat, visited, hat, hvisited, hcycle | hreturn⟩ :=
    first_repeat_outcome_of_long_run
      (w := w) (N := 2) hN (by simpa using hlive)
  · exact ⟨atRepeat, visited, hat, by omega,
      Or.inl hcycle.never_falls⟩
  · obtain ⟨backSteps, settled, hback, hreturn⟩ := hreturn
    exact ⟨atRepeat, visited, hat, by omega, Or.inr
      ⟨backSteps, settled, by omega, hreturn⟩⟩

/-- **Complete isolated two-switch fork.**

If all track edges belong to the two represented switches and the input edge
is cut open, every run which survives three steps has already done one of
two things: entered a trajectory which can never fall, or retraced and fallen
through that same input edge. There is no third outcome which leaves through
a fresh output edge. -/
theorem isolated_two_switch_first_repeat_outcome
    {w : Wiring}
    (hports : forall p q, w.link p = some q ->
      And (p < 6) (q < 6))
    {start finish : Nat × Tongues}
    (hinputOpen : w.link start.1 = none)
    (hlive : stepN w 3 start = some finish) :
    exists atRepeat visited,
      And (stepN w visited start = some atRepeat)
      (And (visited <= 2)
        (Or (forall n, (stepN w n atRepeat).isSome)
          (exists backSteps,
            And (backSteps <= 3)
              (stepN w backSteps atRepeat = none)))) := by
  have houtcome := two_switch_first_repeat_cycle_or_input_return
    hports hlive
  obtain ⟨atRepeat, visited, hat, hvisited, hcycle | hreturn⟩ :=
    houtcome
  · exact ⟨atRepeat, visited, hat, by omega,
      Or.inl hcycle⟩
  · obtain ⟨backSteps, settled, hback, hreturn⟩ := hreturn
    refine ⟨atRepeat, visited, hat, by omega, Or.inr
      ⟨backSteps, by omega, ?_⟩⟩
    simpa [hinputOpen] using hreturn

/-- The exact adversarial conclusion for a two-switch `C,D,C` word. The
self-anchor is `D` or the closing `C`; independently, the isolated module
either never falls or returns through its input. Therefore disjoint copies
cannot be concatenated as forward one-shot counters. -/
theorem isolated_two_switch_CDC_outcome
    {w : Wiring}
    (hports : forall p q, w.link p = some q ->
      And (p < 6) (q < 6))
    {start : Nat × Tongues}
    (hinputOpen : w.link start.1 = none)
    {C D first middle close : Nat}
    (H : RawCDCWord w 2 start C D first middle close) :
    And
      (Or (RawTrainCurveSelfAt w start close)
        (RawTrainCurveSelfAt w start middle))
      (exists atRepeat visited,
        And (stepN w visited start = some atRepeat)
        (And (visited <= 2)
          (Or (forall n, (stepN w n atRepeat).isSome)
            (exists backSteps,
              And (backSteps <= 3)
                (stepN w backSteps atRepeat = none))))) := by
  have hN : forall p q, w.link p = some q ->
      And (p < 3 * 2) (q < 3 * 2) := by
    intro p q hlink
    have h := hports p q hlink
    omega
  have hthreeLe : 3 <= close + 1 := by
    have h01 := H.first_lt_middle
    have h12 := H.middle_lt_close
    omega
  have hthree : (stepN w 3 start).isSome :=
    stepN_prefix_isSome_local hthreeLe H.close_productive.1
  obtain ⟨finish, hfinish⟩ := Option.isSome_iff_exists.mp hthree
  exact ⟨H.self_at_middle_or_close hN,
    isolated_two_switch_first_repeat_outcome
      hports hinputOpen hfinish⟩

end GeneralN
