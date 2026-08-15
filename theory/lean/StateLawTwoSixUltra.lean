import StateLawTwoSharper

/-!
# The arbitrary-start boundary charge

This file isolates the first-history case split needed to remove the final
singleton in state_law_linear_two_sharper. It intentionally imports the
shared proof chain without modifying it.
-/

namespace GeneralN

/-- If the switch written by the arbitrary initial trailing move is absent
from the first manufactured exploration, reserving that switch shrinks the
exploration budget by one. Consequently the original vector can be adjoined
to the sharp construction history without increasing its N + 2 budget. -/
theorem initial_boundary_history_length_le_of_entry_writer_absent
    {w : Wiring} {N g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hk0 : k0 < N)
    (habsent : Not (List.Mem k0 (A.exploration.map passageSwitch)))
    (original : Tongues) :
    (VectorCount.restrict N original ::
      A.sharpConstructionHistory N).length <= N + 2 := by
  have hsimple : (A.exploration.map passageSwitch).Nodup := by
    exact A.exploration_simple
  have hreserved :
      (k0 :: A.exploration.map passageSwitch).Nodup := by
    rw [List.nodup_cons]
    exact And.intro habsent hsimple
  have hinRange : forall C,
      List.Mem C (k0 :: A.exploration.map passageSwitch) -> C < N := by
    intro C hC
    rcases List.mem_cons.mp hC with hEq | hC
    case inl =>
      rw [hEq]
      exact hk0
    case inr =>
      let passage := Exists.choose (List.mem_map.mp hC)
      have hdata := Exists.choose_spec (List.mem_map.mp hC)
      have hlt :=
        A.exploration_trace.switch_lt hN passage hdata.1
      exact Eq.mp (congrArg (fun z => z < N) hdata.2) hlt
  have hlength := nodup_nat_lt_length hreserved hinRange
  simp only [List.length_cons, List.length_map] at hlength
  simp [ManufacturedReflector.sharpConstructionHistory]
  omega

/-- Exact data at the unique occurrence of k0 in a switch-simple first
exploration. The prefix preserves k0; the occurrence either leaves the
whole tongue state unchanged or flips exactly k0. -/
structure InitialEntryWriterOccurrence
    (w : Wiring) (g e k0 : Nat)
    (A : ManufacturedReflector w g e) where
  before : List Passage
  after : List Passage
  p : Nat
  x : Nat
  nextPort : Nat
  middle : Tongues
  next : Tongues
  split : A.exploration = before ++ (p, x) :: after
  switch_eq : passageSwitch (p, x) = k0
  before_trace :
    PhysicalTrace w (g, A.baseState) before (p, middle)
  arrive_eq : arrive middle p = (x, next)
  link_eq : w.link x = some nextPort
  reach : stepN w (before.length + 1) (g, A.baseState) =
    some (nextPort, next)
  prefix_foreign : forall passage,
    List.Mem passage before -> Ne (passageSwitch passage) k0
  prefix_preserves : middle k0 = A.baseState k0
  state_case : Or (next = middle) (next = flipAt middle k0)

/-- Split the first manufactured exploration at its unique k0 passage. -/
theorem first_entry_writer_occurrence_dichotomy
    {w : Wiring} {g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (hmem : List.Mem k0 (A.exploration.map passageSwitch)) :
    Nonempty (InitialEntryWriterOccurrence w g e k0 A) := by
  let passage := Exists.choose (List.mem_map.mp hmem)
  have hpassageData := Exists.choose_spec (List.mem_map.mp hmem)
  have hpassage : List.Mem passage A.exploration := hpassageData.1
  have hswitchRaw : passageSwitch passage = k0 := hpassageData.2
  let p := passage.1
  let x := passage.2
  have hpassageEq : passage = (p, x) := by
    simp [p, x]
  rw [hpassageEq] at hpassage hswitchRaw
  have hswitch : passageSwitch (p, x) = k0 := hswitchRaw
  have hpSwitch : p / 3 = k0 := by
    simpa [passageSwitch] using hswitch
  let splitData := List.append_of_mem hpassage
  let before := Exists.choose splitData
  let after := Exists.choose (Exists.choose_spec splitData)
  have hsplit : A.exploration = before ++ (p, x) :: after :=
    Exists.choose_spec (Exists.choose_spec splitData)
  have htrace := A.exploration_trace
  rw [hsplit] at htrace
  let traceData := htrace.split_append
  let configuration := Exists.choose traceData
  have hbefore := (Exists.choose_spec traceData).1
  have hrest := (Exists.choose_spec traceData).2
  have hport : configuration.1 = p := hrest.head_arrive.1
  let middle := configuration.2
  have hconfiguration : configuration = (p, middle) :=
    Prod.ext hport rfl
  change PhysicalTrace w (g, A.baseState) before configuration at hbefore
  change PhysicalTrace w configuration ((p, x) :: after) A.preReturn at hrest
  rw [hconfiguration] at hbefore hrest
  cases hrest with
  | @cons _ _ nextPort _ next _ _ harrive hlink hafter =>
      have hsimple :
          (before.map passageSwitch ++
            passageSwitch (p, x) :: after.map passageSwitch).Nodup := by
        have hs := A.exploration_simple
        unfold SwitchSimple at hs
        rw [hsplit] at hs
        simpa only [List.map_append, List.map_cons] using hs
      have hparts := List.nodup_append.mp hsimple
      have hprefixForeign : forall prior,
          List.Mem prior before -> Ne (passageSwitch prior) k0 := by
        intro prior hprior hEq
        have hleft : List.Mem k0 (before.map passageSwitch) :=
          List.mem_map.mpr
            (Exists.intro prior (And.intro hprior hEq))
        have hright : List.Mem k0
            (passageSwitch (p, x) :: after.map passageSwitch) := by
          exact List.mem_cons.mpr (Or.inl hswitch.symm)
        exact hparts.2.2 k0 hleft k0 hright rfl
      have hmiddleK : middle k0 = A.baseState k0 := by
        exact hbefore.preserves k0 hprefixForeign
      have hreach :
          stepN w (before.length + 1) (g, A.baseState) =
            some (nextPort, next) := by
        rw [stepN_add, hbefore.sound]
        simp [stepN, step, harrive, hlink]
      have hstate : Or (next = middle) (next = flipAt middle k0) := by
        by_cases hchanged : Ne (next (p / 3)) (middle (p / 3))
        case pos =>
          apply Or.inr
          have hflip := changed_arrival_eq_flipAt harrive hchanged
          simpa [hpSwitch] using hflip
        case neg =>
          apply Or.inl
          funext j
          by_cases hj : j = p / 3
          case pos =>
            subst j
            exact Classical.not_not.mp hchanged
          case neg =>
            exact arrive_preserves_other harrive hj
      exact Nonempty.intro {
        before := before
        after := after
        p := p
        x := x
        nextPort := nextPort
        middle := middle
        next := next
        split := hsplit
        switch_eq := hswitch
        before_trace := hbefore
        arrive_eq := harrive
        link_eq := hlink
        reach := hreach
        prefix_foreign := hprefixForeign
        prefix_preserves := hmiddleK
        state_case := hstate
      }

/-- In the productive occurrence branch, a tongue-quiet prefix makes the
post-occurrence state exactly the original arbitrary-start state. Thus the
supposed extra vector is already in the ordinary sharp history. -/
theorem original_vector_mem_sharp_history_of_quiet_entry_writer_flip
    {w : Wiring} {N g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (original : Tongues)
    (hbase : A.baseState = flipAt original k0)
    (O : InitialEntryWriterOccurrence w g e k0 A)
    (hquiet : O.middle = A.baseState)
    (hflip : O.next = flipAt O.middle k0) :
    List.Mem (VectorCount.restrict N original)
      (A.sharpConstructionHistory N) := by
  have hnext : O.next = original := by
    rw [hflip, hquiet, hbase, flipAt_flipAt]
  have hvector :
      restrictedTonguesAt w N (g, A.baseState) (O.before.length + 1) =
        VectorCount.restrict N original := by
    simp [restrictedTonguesAt, tonguesAt, O.reach, hnext]
  unfold ManufacturedReflector.sharpConstructionHistory
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact Exists.intro (O.before.length + 1)
    (And.intro (List.mem_range.mpr (by
      rw [O.split]; simp)) hvector)

/-- In the unchanged occurrence branch, the two consecutive construction
times around the k0 passage have the same restricted tongue vector. This
is the duplicate which replaces the reserved-switch saving of the absent
case. -/
theorem entry_writer_unchanged_gives_consecutive_duplicate
    {w : Wiring} {N g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (O : InitialEntryWriterOccurrence w g e k0 A)
    (hstay : O.next = O.middle) :
    restrictedTonguesAt w N (g, A.baseState) O.before.length =
      restrictedTonguesAt w N (g, A.baseState)
        (O.before.length + 1) := by
  simp [restrictedTonguesAt, tonguesAt,
    O.before_trace.sound, O.reach, hstay]

/-! ## A single N + 2 boundary-history certificate -/

/-- Remove the post-time of an unchanged k0 occurrence. Its immediately
preceding time carries the same vector, so this reduced history still covers
the complete construction while making room for the arbitrary initial
vector. -/
def InitialEntryWriterOccurrence.reducedBoundaryHistory
    {w : Wiring} {g e k0 : Nat}
    {A : ManufacturedReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0 A)
    (N : Nat) (original : Tongues) : List (List Bool) :=
  VectorCount.restrict N original ::
    ((List.range (A.exploration.length + 1)).erase
      (O.before.length + 1)).map
        (restrictedTonguesAt w N (g, A.baseState)) ++
      [VectorCount.restrict N A.activatedState]

theorem InitialEntryWriterOccurrence.reducedBoundaryHistory_length
    {w : Wiring} {N g e k0 : Nat}
    {A : ManufacturedReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0 A)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (original : Tongues) :
    (O.reducedBoundaryHistory N original).length <= N + 2 := by
  have hindex : List.Mem (O.before.length + 1)
      (List.range (A.exploration.length + 1)) := by
    apply List.mem_range.mpr
    rw [O.split]
    simp
  have herase :
      ((List.range (A.exploration.length + 1)).erase
        (O.before.length + 1)).length =
        (List.range (A.exploration.length + 1)).length - 1 :=
    List.length_erase_of_mem hindex
  have hexploration :
      A.exploration.length <= N :=
    A.exploration_trace.simple_length_le hN A.exploration_simple
  have heraseExact :
      ((List.range (A.exploration.length + 1)).erase
        (O.before.length + 1)).length = A.exploration.length := by
    rw [herase, List.length_range]
    omega
  unfold InitialEntryWriterOccurrence.reducedBoundaryHistory
  simp only [List.length_cons, List.length_append, List.length_map,
    List.length_nil, heraseExact]
  omega

/-- If the k0 occurrence is unchanged, every member of the ordinary sharp
history is represented in the reduced boundary history. -/
theorem InitialEntryWriterOccurrence.sharp_mem_reduced_of_stay
    {w : Wiring} {N g e k0 : Nat}
    {A : ManufacturedReflector w g e}
    (O : InitialEntryWriterOccurrence w g e k0 A)
    (original : Tongues)
    (hstay : O.next = O.middle) :
    forall v,
      List.Mem v (A.sharpConstructionHistory N) ->
      List.Mem v (O.reducedBoundaryHistory N original) := by
  intro v hv
  have hduplicate :=
    entry_writer_unchanged_gives_consecutive_duplicate
      (N := N) A O hstay
  unfold ManufacturedReflector.sharpConstructionHistory at hv
  rcases List.mem_append.mp hv with hv | hv
  case inl =>
    let data := List.mem_map.mp hv
    let time := Exists.choose data
    have htime : List.Mem time
        (List.range (A.exploration.length + 1)) :=
      (Exists.choose_spec data).1
    have hvector :
        restrictedTonguesAt w N (g, A.baseState) time = v :=
      (Exists.choose_spec data).2
    by_cases hEq : time = O.before.length + 1
    case pos =>
      have hbeforeRange : List.Mem O.before.length
          (List.range (A.exploration.length + 1)) := by
        apply List.mem_range.mpr
        rw [O.split]
        simp
        omega
      have hbeforeNe : Ne O.before.length (O.before.length + 1) := by
        omega
      have hbeforeErase : List.Mem O.before.length
          ((List.range (A.exploration.length + 1)).erase
            (O.before.length + 1)) :=
        (List.mem_erase_of_ne hbeforeNe).mpr hbeforeRange
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact Exists.intro O.before.length
        (And.intro hbeforeErase
          (hduplicate.trans
            (Eq.mp
              (congrArg (fun t =>
                restrictedTonguesAt w N (g, A.baseState) t = v) hEq)
              hvector)))
    case neg =>
      have htimeErase : List.Mem time
          ((List.range (A.exploration.length + 1)).erase
            (O.before.length + 1)) :=
        (List.mem_erase_of_ne hEq).mpr htime
      apply List.mem_cons_of_mem
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact Exists.intro time (And.intro htimeErase hvector)
  case inr =>
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    exact hv

/-- A bounded history which contains both the arbitrary initial vector and
every vector of the first complete manufactured journey. -/
structure InitialBoundaryHistory
    (w : Wiring) (N g e : Nat)
    (A : ManufacturedReflector w g e)
    (original : Tongues) where
  history : List (List Bool)
  length_le : history.length <= N + 2
  original_mem : List.Mem (VectorCount.restrict N original) history
  journey_mem : forall j,
    j <= A.exploration.length + A.runway.length + 1 ->
    List.Mem (restrictedTonguesAt w N (g, A.baseState) j) history

theorem boundary_history_of_entry_writer_absent
    {w : Wiring} {N g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hk0 : k0 < N)
    (habsent : Not (List.Mem k0
      (A.exploration.map passageSwitch)))
    (original : Tongues)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState) :
    Nonempty (InitialBoundaryHistory w N g e A original) := by
  let history :=
    VectorCount.restrict N original :: A.sharpConstructionHistory N
  exact Nonempty.intro {
    history := history
    length_le := by
      exact initial_boundary_history_length_le_of_entry_writer_absent
        A hN hk0 habsent original
    original_mem := List.mem_cons_self
    journey_mem := by
      intro j hj
      apply List.mem_cons_of_mem
      exact A.manufacturing_journey_mem_sharpHistory hpaths hj
  }

theorem boundary_history_of_entry_writer_stay
    {w : Wiring} {N g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (original : Tongues)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    (O : InitialEntryWriterOccurrence w g e k0 A)
    (hstay : O.next = O.middle) :
    Nonempty (InitialBoundaryHistory w N g e A original) := by
  let history := O.reducedBoundaryHistory N original
  exact Nonempty.intro {
    history := history
    length_le := by
      exact O.reducedBoundaryHistory_length hN original
    original_mem := List.mem_cons_self
    journey_mem := by
      intro j hj
      apply O.sharp_mem_reduced_of_stay original hstay
      exact A.manufacturing_journey_mem_sharpHistory hpaths hj
  }

theorem boundary_history_of_quiet_entry_writer_flip
    {w : Wiring} {N g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (original : Tongues)
    (hbase : A.baseState = flipAt original k0)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState)
    (O : InitialEntryWriterOccurrence w g e k0 A)
    (hquiet : O.middle = A.baseState)
    (hflip : O.next = flipAt O.middle k0) :
    Nonempty (InitialBoundaryHistory w N g e A original) := by
  exact Nonempty.intro {
    history := A.sharpConstructionHistory N
    length_le := A.sharpConstructionHistory_length hN
    original_mem :=
      original_vector_mem_sharp_history_of_quiet_entry_writer_flip
        A original hbase O hquiet hflip
    journey_mem := by
      intro j hj
      exact A.manufacturing_journey_mem_sharpHistory hpaths hj
  }

/-- Complete first-history split for a productive arbitrary initial passage.
All cases fit the original N + 2 budget except a productive return through k0
after a prefix which has already changed another tongue. This is the exact
remaining obstruction to deleting ArbitraryStartDirectLift's singleton by
first-history accounting alone. -/
theorem first_history_absorbed_or_productive_nonquiet_entry_return
    {w : Wiring} {N g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hk0 : k0 < N)
    (original : Tongues)
    (hbase : A.baseState = flipAt original k0)
    (hpaths : PathGrooves A.toSupported.paths A.activatedState) :
    Or (Nonempty (InitialBoundaryHistory w N g e A original))
      (Exists fun O : InitialEntryWriterOccurrence w g e k0 A =>
        And (O.next = flipAt O.middle k0)
          (Ne O.middle A.baseState)) := by
  by_cases hmem : List.Mem k0
      (A.exploration.map passageSwitch)
  case neg =>
    apply Or.inl
    exact boundary_history_of_entry_writer_absent
      A hN hk0 hmem original hpaths
  case pos =>
    let O := Classical.choice
      (first_entry_writer_occurrence_dichotomy A hmem)
    rcases O.state_case with hstay | hflip
    case inl =>
      apply Or.inl
      exact boundary_history_of_entry_writer_stay
        A hN original hpaths O hstay
    case inr =>
      by_cases hquiet : O.middle = A.baseState
      case pos =>
        apply Or.inl
        exact boundary_history_of_quiet_entry_writer_flip
          A hN original hbase hpaths O hquiet hflip
      case neg =>
        apply Or.inr
        exact Exists.intro O (And.intro hflip hquiet)


/-! ## The productive residual is an early simple cycle -/

/-- If the shifted first construction productively revisits the switch
written by the arbitrary initial move, it exits through the same stem.
That stem is wired back to the shifted start. The prefix through this
occurrence is therefore a switch-simple transient lap, and replaying the
installed grooves is a stable lap. -/
theorem productive_entry_writer_occurrence_is_simple_cycle
    {w : Wiring} {g e k0 : Nat}
    (A : ManufacturedReflector w g e)
    (he : e = 3 * k0)
    (O : InitialEntryWriterOccurrence w g e k0 A)
    (hflip : O.next = flipAt O.middle k0) :
    let cycle := O.before ++ [(O.p, O.x)]
    And (Ne cycle [])
      (And
        (PhysicalTrace w (g, A.baseState) cycle (g, O.next))
        (And
          (PhysicalTrace w (g, O.next) cycle (g, O.next))
          (SwitchSimple cycle))) := by
  have hpSwitch : O.p / 3 = k0 := by
    simpa [passageSwitch] using O.switch_eq
  have hchanged :
      Ne (O.next (O.p / 3)) (O.middle (O.p / 3)) := by
    rw [hflip, hpSwitch]
    simp [flipAt]
  have htrailing :=
    changed_arrival_is_trailing O.arrive_eq hchanged
  have hxe : O.x = e := by
    rw [htrailing.2.1, hpSwitch]
    exact he.symm
  have hlink : w.link e = some O.nextPort := by
    simpa [hxe] using O.link_eq
  have hnextPort : O.nextPort = g := by
    have hs : some O.nextPort = some g :=
      hlink.symm.trans A.entryEdge
    exact Option.some.inj hs
  have hone :
      PhysicalTrace w (O.p, O.middle) [(O.p, O.x)]
        (O.nextPort, O.next) :=
    PhysicalTrace.cons O.arrive_eq O.link_eq
      (PhysicalTrace.nil _)
  have htransient :
      PhysicalTrace w (g, A.baseState)
        (O.before ++ [(O.p, O.x)]) (g, O.next) := by
    have happended := O.before_trace.append hone
    simpa [hnextPort] using happended
  have hsplit :
      A.exploration =
        (O.before ++ [(O.p, O.x)]) ++ O.after := by
    rw [O.split]
    simp
  have hsimple :
      SwitchSimple (O.before ++ [(O.p, O.x)]) := by
    have hall := A.exploration_simple
    unfold SwitchSimple at hall
    rw [hsplit] at hall
    simp only [List.map_append] at hall
    unfold SwitchSimple
    simp only [List.map_append]
    exact (List.nodup_append.mp hall).1
  have hstable :
      PhysicalTrace w (g, O.next)
        (O.before ++ [(O.p, O.x)]) (g, O.next) := by
    have hgrooved :=
      htransient.grooved_of_switchSimple hsimple
    exact htransient.replay_grooved O.next hgrooved
  dsimp
  refine And.intro (by simp) ?_
  exact And.intro htransient (And.intro hstable hsimple)


/-! ## A cover-level boundary-tail abstraction -/

theorem ultra_nodup_map_filter
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    {f : Nat -> alpha} (p : Nat -> Bool) :
    forall {xs : List Nat},
      (xs.map f).Nodup ->
      ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          case left =>
            intro hm
            obtain data := List.mem_map.mp hm
            let y := Exists.choose data
            have hy := Exists.choose_spec data
            apply hnd.1
            apply List.mem_map.mpr
            exact Exists.intro y
              (And.intro (List.mem_filter.mp hy.1).1 hy.2)
          case right =>
            exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

/-- Cover-level form of boundary overlap. The boundary vector is already
historical, so a suffix with direct cap cap contributes at most cap-1 fresh
vectors. -/
theorem boundary_history_then_direct_tail_cover
    {w : Wiring} {N lead cap : Nat}
    {start endpoint : Prod Nat Tongues}
    (hreach : stepN w lead start = some endpoint)
    (prefixHistory : List (List Bool))
    (hprefixCover : forall d, d <= lead ->
      List.Mem (restrictedTonguesAt w N start d) prefixHistory)
    (hboundary :
      List.Mem (VectorCount.restrict N endpoint.2) prefixHistory)
    (htail : forall tailTimes : List Nat,
      (forall k, List.Mem k tailTimes ->
        (stepN w k endpoint).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N endpoint)).Nodup ->
      tailTimes.length <= cap)
    (hcapPos : 0 < cap)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    NoveltyCoverOn w N start times prefixHistory (cap - 1) := by
  let late := times.filter (fun k => decide (lead < k))
  let shifted := late.map (fun k => k - lead)
  let boundary := VectorCount.restrict N endpoint.2
  let other := shifted.filter (fun d =>
    decide (Ne (restrictedTonguesAt w N endpoint d) boundary))
  let otherVectors :=
    other.map (restrictedTonguesAt w N endpoint)
  have hlateVector : shifted.map
      (restrictedTonguesAt w N endpoint) =
      late.map (restrictedTonguesAt w N start) := by
    dsimp [shifted]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkTimes : List.Mem k times :=
      (List.mem_filter.mp hk).1
    have hkGt : lead < k :=
      of_decide_eq_true (List.mem_filter.mp hk).2
    have hkEq : k = lead + (k - lead) := by
      omega
    have hkLive := hlive k hkTimes
    cases htailRun :
        stepN w (k - lead) endpoint with
    | none =>
        have hglobalNone : stepN w k start = none := by
          rw [hkEq, stepN_add, hreach]
          simp [htailRun]
        rw [hglobalNone] at hkLive
        simp at hkLive
    | some finish =>
        have hshift := tonguesAt_add_of_reaches
          hreach (Exists.intro finish htailRun)
        have hstartEq :
            tonguesAt w start (lead + (k - lead)) =
              tonguesAt w start k :=
          congrArg (tonguesAt w start) hkEq.symm
        simp only [Function.comp_apply]
        unfold restrictedTonguesAt
        exact congrArg (VectorCount.restrict N)
          (hshift.symm.trans hstartEq)
  have hlateNodup :
      (late.map
        (restrictedTonguesAt w N start)).Nodup := by
    dsimp [late]
    exact ultra_nodup_map_filter _ hnd
  have hshiftedNodup :
      (shifted.map
        (restrictedTonguesAt w N endpoint)).Nodup := by
    rw [hlateVector]
    exact hlateNodup
  have hotherNodup : otherVectors.Nodup := by
    dsimp [otherVectors, other]
    exact ultra_nodup_map_filter _ hshiftedNodup
  have hzeroVector :
      restrictedTonguesAt w N endpoint 0 = boundary := by
    dsimp [boundary]
    simp [restrictedTonguesAt, tonguesAt, stepN]
  have hboundaryNotOther :
      Not (List.Mem boundary otherVectors) := by
    intro hm
    obtain data := List.mem_map.mp hm
    let d := Exists.choose data
    have hd := Exists.choose_spec data
    have hne :
        Ne (restrictedTonguesAt w N endpoint d) boundary :=
      of_decide_eq_true (List.mem_filter.mp hd.1).2
    exact hne hd.2
  have hzeroOtherNodup :
      ((0 :: other).map
        (restrictedTonguesAt w N endpoint)).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    constructor
    case left =>
      intro hm
      rw [hzeroVector] at hm
      exact hboundaryNotOther hm
    case right =>
      exact hotherNodup
  have hotherLive : forall d, List.Mem d other ->
      (stepN w d endpoint).isSome := by
    intro d hd
    have hdShifted := (List.mem_filter.mp hd).1
    obtain data := List.mem_map.mp hdShifted
    let k := Exists.choose data
    have hk := Exists.choose_spec data
    have hkd : k - lead = d := hk.2
    have hkTimes : List.Mem k times :=
      (List.mem_filter.mp hk.1).1
    have hkGt : lead < k :=
      of_decide_eq_true (List.mem_filter.mp hk.1).2
    have hkEq : k = lead + (k - lead) := by
      omega
    have hkLiveRaw := hlive k hkTimes
    rw [hkEq, stepN_add, hreach] at hkLiveRaw
    have hkLive :
        (stepN w (k - lead) endpoint).isSome := by
      simpa using hkLiveRaw
    exact Eq.mp
      (congrArg
        (fun z => (stepN w z endpoint).isSome = true) hkd)
      hkLive
  have hzeroOtherLive : forall d, List.Mem d (0 :: other) ->
      (stepN w d endpoint).isSome := by
    intro d hd
    rcases List.mem_cons.mp hd with hd | hd
    case inl =>
      subst d
      simp [stepN]
    case inr =>
      exact hotherLive d hd
  have htailBound : (0 :: other).length <= cap :=
    htail (0 :: other) hzeroOtherLive hzeroOtherNodup
  have hotherBound : other.length <= cap - 1 := by
    simp only [List.length_cons] at htailBound
    omega
  have hmem : forall k, List.Mem k times ->
      List.Mem (restrictedTonguesAt w N start k)
        (prefixHistory ++ otherVectors) := by
    intro k hk
    by_cases hpre : k <= lead
    case pos =>
      exact List.mem_append_left otherVectors
        (hprefixCover k hpre)
    case neg =>
      have hkGt : lead < k := by
        omega
      let d := k - lead
      have hkEq : k = lead + d := by
        dsimp [d]
        omega
      have hkLive := hlive k hk
      have htailLive : Exists fun finish =>
          stepN w d endpoint = some finish := by
        cases hd : stepN w d endpoint with
        | none =>
            have hnone : stepN w k start = none := by
              rw [hkEq, stepN_add, hreach]
              simp [hd]
            rw [hnone] at hkLive
            simp at hkLive
        | some finish =>
            exact Exists.intro finish rfl
      have hshift :=
        tonguesAt_add_of_reaches hreach htailLive
      have heq :
          restrictedTonguesAt w N start k =
            restrictedTonguesAt w N endpoint d := by
        unfold restrictedTonguesAt
        rw [hkEq]
        exact congrArg (VectorCount.restrict N) hshift
      by_cases hbd :
          restrictedTonguesAt w N endpoint d = boundary
      case pos =>
        rw [heq, hbd]
        have hb : List.Mem boundary prefixHistory := by
          dsimp [boundary]
          exact hboundary
        exact List.mem_append_left otherVectors hb
      case neg =>
        rw [heq]
        apply List.mem_append_right prefixHistory
        dsimp [otherVectors]
        apply List.mem_map.mpr
        refine Exists.intro d ?_
        constructor
        case left =>
          apply List.mem_filter.mpr
          constructor
          case left =>
            dsimp [shifted, late, d]
            apply List.mem_map.mpr
            refine Exists.intro k ?_
            constructor
            case left =>
              apply List.mem_filter.mpr
              exact And.intro hk (decide_eq_true hkGt)
            case right =>
              rfl
          case right =>
            exact decide_eq_true hbd
        case right =>
          rfl
  refine Exists.intro otherVectors ?_
  constructor
  case left =>
    simpa [otherVectors] using hotherBound
  case right =>
    intro k hk
    exact hmem k hk

private theorem ultra_nodup_subset_length
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall {xs cover : List alpha},
      xs.Nodup ->
      (forall x, List.Mem x xs -> List.Mem x cover) ->
      xs.length <= cover.length := by
  intro xs
  induction xs with
  | nil =>
      intro cover _ _
      exact Nat.zero_le _
  | cons x rest ih =>
      intro cover hnd hsub
      rw [List.nodup_cons] at hnd
      have hx : List.Mem x cover :=
        hsub x List.mem_cons_self
      have hrest : forall y, List.Mem y rest ->
          List.Mem y (cover.erase x) := by
        intro y hy
        have hyCover : List.Mem y cover :=
          hsub y (List.mem_cons_of_mem _ hy)
        have hyx : Ne y x := by
          intro heq
          apply hnd.1
          exact Eq.mp (congrArg (fun z => List.Mem z rest) heq) hy
        exact (List.mem_erase_of_ne hyx).mpr hyCover
      have hle := ih hnd.2 hrest
      have herase :
          (cover.erase x).length = cover.length - 1 :=
        List.length_erase_of_mem hx
      have hpositive : 0 < cover.length := by
        cases cover with
        | nil =>
            cases hx
        | cons _ _ =>
            simp
      simp only [List.length_cons]
      omega

/-- One vector already in history may be counted together with all sampled
vectors without increasing the novelty budget. -/
theorem novelty_cover_count_with_historical_extra
    {w : Wiring} {N budget : Nat}
    {start : Prod Nat Tongues}
    {times : List Nat}
    {history : List (List Bool)}
    (extra : List Bool)
    (hcover : NoveltyCoverOn w N start times history budget)
    (hextra : List.Mem extra history)
    (hnd : (extra ::
      times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length + 1 <= history.length + budget := by
  let fresh := Exists.choose hcover
  have hfresh := Exists.choose_spec hcover
  have hsubset : forall x,
      List.Mem x (extra ::
        times.map (restrictedTonguesAt w N start)) ->
      List.Mem x (history ++ fresh) := by
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    case inl =>
      rw [hx]
      exact List.mem_append_left fresh hextra
    case inr =>
      obtain hm := List.mem_map.mp hx
      let k := Exists.choose hm
      have hk := Exists.choose_spec hm
      exact Eq.mp
        (congrArg
          (fun z => List.Mem z (history ++ fresh)) hk.2)
        (hfresh.2 k hk.1)
  have hcount :=
    ultra_nodup_subset_length hnd hsubset
  simp only [List.length_cons, List.length_map,
    List.length_append] at hcount
  have hfreshLength : fresh.length <= budget := by
    simpa [fresh] using hfresh.1
  omega


/-! ## Two journeys with an arbitrary first-history cover -/

/-- Replace the canonical first construction history by any N+2 history
which covers that journey and already contains an additional initial vector.
The second activation boundary is erased once, and the direct tail shares its
time-zero boundary. -/
theorem two_journeys_with_initial_history_then_tail
    {w : Wiring} {N e tailCap : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (A : ManufacturedReflector w start.1 e)
    (B : ManufacturedReflector w e start.1)
    (original stateA stateB : Tongues)
    (H : InitialBoundaryHistory
      w N start.1 e A original)
    (hbaseA : A.baseState = start.2)
    (_hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hbaseB : B.baseState = stateA)
    (hactivatedB : stateB = B.activatedState)
    (hreachB : stepN w
      (B.exploration.length + B.runway.length + 1)
        (e, stateA) =
        some (start.1, stateB))
    (hgroovesB :
      PathGrooves B.toSupported.paths stateB)
    (htail : forall tailTimes : List Nat,
      (forall k, List.Mem k tailTimes ->
        (stepN w k (start.1, stateB)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N
          (start.1, stateB))).Nodup ->
      tailTimes.length <= tailCap)
    (htailPos : 0 < tailCap)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k start).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N start)).Nodup) :
    times.length + 1 <= 2 * N + tailCap + 2 := by
  let firstTravel :=
    A.exploration.length + A.runway.length + 1
  let secondTravel :=
    B.exploration.length + B.runway.length + 1
  let totalTravel := firstTravel + secondTravel
  let firstHistory := H.history
  let secondHistory := B.sharpConstructionHistory N
  let aBoundary := VectorCount.restrict N stateA
  let bBoundary := VectorCount.restrict N stateB
  let secondReduced := secondHistory.erase aBoundary
  let prefixHistory := firstHistory ++ secondReduced
  have hgroovesBActivated :
      PathGrooves B.toSupported.paths B.activatedState := by
    exact Eq.mp
      (congrArg (fun state =>
        PathGrooves B.toSupported.paths state) hactivatedB) hgroovesB
  have hreachTotal :
      stepN w totalTravel start =
        some (start.1, stateB) := by
    dsimp [totalTravel]
    rw [stepN_add, hreachA]
    exact hreachB
  have hAFirst : List.Mem aBoundary firstHistory := by
    have hm := H.journey_mem firstTravel (by
      dsimp [firstTravel]
      omega)
    have hrun :
        stepN w firstTravel
          (start.1, A.baseState) =
          some (e, stateA) := by
      simpa [firstTravel, hbaseA] using hreachA
    have hvec :
        restrictedTonguesAt w N
          (start.1, A.baseState) firstTravel =
          aBoundary := by
      simp [restrictedTonguesAt, tonguesAt,
        hrun, aBoundary]
    dsimp [firstHistory]
    exact Eq.mp
      (congrArg
        (fun z => List.Mem z H.history) hvec)
      hm
  have hASecond :
      List.Mem aBoundary secondHistory := by
    dsimp [aBoundary, secondHistory]
    unfold ManufacturedReflector.sharpConstructionHistory
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine Exists.intro 0 ?_
    constructor
    case left =>
      apply List.mem_range.mpr
      omega
    case right =>
      simp [restrictedTonguesAt, tonguesAt,
        stepN, hbaseB]
  have hBSecond :
      List.Mem bBoundary secondHistory := by
    dsimp [bBoundary, secondHistory]
    unfold ManufacturedReflector.sharpConstructionHistory
    apply List.mem_append_right
    apply List.mem_singleton.mpr
    exact congrArg (VectorCount.restrict N) hactivatedB
  have hBPrefix :
      List.Mem bBoundary prefixHistory := by
    by_cases hBA : bBoundary = aBoundary
    case pos =>
      rw [hBA]
      exact List.mem_append_left secondReduced hAFirst
    case neg =>
      apply List.mem_append_right firstHistory
      exact (List.mem_erase_of_ne hBA).mpr hBSecond
  have hprefixCover : forall d, d <= totalTravel ->
      List.Mem (restrictedTonguesAt w N start d)
        prefixHistory := by
    intro d hd
    by_cases hfirst : d <= firstTravel
    case pos =>
      apply List.mem_append_left secondReduced
      have hm := H.journey_mem d (by
        dsimp [firstTravel] at hfirst
        exact hfirst)
      have hstartEq :
          (start.1, A.baseState) = start :=
        Prod.ext rfl hbaseA
      have hvecEq :=
        congrArg
          (fun c => restrictedTonguesAt w N c d) hstartEq
      dsimp [firstHistory]
      exact Eq.mp (congrArg (fun z => List.Mem z H.history) hvecEq) hm
    case neg =>
      let q := d - firstTravel
      have hdEq : d = firstTravel + q := by
        dsimp [q]
        omega
      have hqLe : q <= secondTravel := by
        dsimp [totalTravel] at hd
        dsimp [q]
        omega
      have hliveQ :=
        stepN_prefix_some hqLe hreachB
      have hshift :=
        tonguesAt_add_of_reaches hreachA hliveQ
      have hm :=
        B.manufacturing_journey_mem_sharpHistory
          (N := N) hgroovesBActivated (j := q)
          (by
            dsimp [secondTravel] at hqLe
            exact hqLe)
      have hmSecond :
          List.Mem
            (restrictedTonguesAt w N
              (e, stateA) q) secondHistory := by
        have hstartEq :
            (e, B.baseState) = (e, stateA) :=
          Prod.ext rfl hbaseB
        have hvecEq :=
          congrArg
            (fun c => restrictedTonguesAt w N c q) hstartEq
        dsimp [secondHistory]
        exact Eq.mp
          (congrArg (fun z =>
            List.Mem z (B.sharpConstructionHistory N)) hvecEq) hm
      have heq :
          restrictedTonguesAt w N start d =
            restrictedTonguesAt w N
              (e, stateA) q := by
        unfold restrictedTonguesAt
        rw [hdEq]
        exact congrArg (VectorCount.restrict N) hshift
      rw [heq]
      by_cases ha :
          restrictedTonguesAt w N
            (e, stateA) q = aBoundary
      case pos =>
        rw [ha]
        exact List.mem_append_left secondReduced hAFirst
      case neg =>
        apply List.mem_append_right firstHistory
        exact (List.mem_erase_of_ne ha).mpr hmSecond
  have hboundary :
      List.Mem
        (VectorCount.restrict N (start.1, stateB).2)
        prefixHistory := by
    simpa [bBoundary] using hBPrefix
  have hcover :=
    boundary_history_then_direct_tail_cover
      hreachTotal prefixHistory hprefixCover hboundary
      htail htailPos times hlive (List.nodup_cons.mp hnd).2
  have hextra :
      List.Mem (VectorCount.restrict N original)
        prefixHistory :=
    List.mem_append_left secondReduced H.original_mem
  have hcount :=
    novelty_cover_count_with_historical_extra
      (VectorCount.restrict N original)
      hcover hextra hnd
  have hfirstLen : firstHistory.length <= N + 2 := by
    dsimp [firstHistory]
    exact H.length_le
  have hsecondLen : secondHistory.length <= N + 2 := by
    dsimp [secondHistory]
    exact B.sharpConstructionHistory_length hN
  have hsecondReducedLen :
      secondReduced.length = secondHistory.length - 1 := by
    dsimp [secondReduced]
    exact List.length_erase_of_mem hASecond
  have hprefixLen :
      prefixHistory.length <= 2 * N + 3 := by
    dsimp [prefixHistory]
    simp only [List.length_append]
    omega
  omega


/-! ## Known-edge assembly carrying the arbitrary initial vector -/

theorem ultra_nodup_of_map_nodup
    {alpha beta : Type}
    [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta) :
    forall {xs : List alpha},
      (xs.map f).Nodup -> xs.Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      case left =>
        intro hx
        apply hnd.1
        apply List.mem_map.mpr
        exact Exists.intro x (And.intro hx rfl)
      case right =>
        exact ih hnd.2

private theorem ultra_live_distinct_le_of_stepN_none
    {w : Wiring} {N L : Nat}
    {start : Prod Nat Tongues}
    {times : List Nat}
    (hnone : stepN w L start = none)
    (hlive : forall k, List.Mem k times ->
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= L := by
  have htimesNodup : times.Nodup :=
    ultra_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  apply nodup_nat_lt_length htimesNodup
  intro k hk
  by_cases hlt : k < L
  case pos =>
    exact hlt
  case neg =>
    have hkEq : k = L + (k - L) := by
      omega
    have hnoneK : stepN w k start = none := by
      rw [hkEq, stepN_add, hnone]
      simp
    have hkLive := hlive k hk
    rw [hnoneK] at hkLive
    simp at hkLive

/-- A known-edge run whose initial state is the result of one productive
arbitrary-start passage can count the pre-step tongue vector inside its first
history. The only apparent failure of that history construction is itself an
early stable simple cycle. -/
theorem known_edge_with_productive_initial_distinct_le_two_mul_add_six
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hentry : w.link e = some g)
    (he : e = 3 * k0)
    (hk0 : k0 < N)
    (original base : Tongues)
    (hbaseShift : base = flipAt original k0)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k (g, base)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map
        (restrictedTonguesAt w N (g, base))).Nodup) :
    times.length + 1 <= 2 * N + 6 := by
  have hlocalNodup :
      (times.map
        (restrictedTonguesAt w N (g, base))).Nodup :=
    (List.nodup_cons.mp hnd).2
  cases hfirst :
      stepN w (N + 1) (g, base) with
  | none =>
      have hc :=
        ultra_live_distinct_le_of_stepN_none
          (N := N) hfirst hlive hlocalNodup
      omega
  | some firstFinish =>
      rcases first_activated_count_outcome_sharp
          hN hfirst hentry with hcycleA | hreflectorA
      case inl =>
        have hc := hcycleA times hlocalNodup
        omega
      case inr =>
        let A := Exists.choose hreflectorA
        have hreflectorAState :=
          Exists.choose_spec hreflectorA
        let stateA := Exists.choose hreflectorAState
        have hdataA :=
          Exists.choose_spec hreflectorAState
        have hgroovesA :
            PathGrooves A.toSupported.paths stateA :=
          hdataA.2.1
        have hbaseA : A.baseState = base :=
          hdataA.2.2.1
        have hactivatedA : stateA = A.activatedState :=
          hdataA.2.2.2.1
        have hreachA :
            stepN w
              (A.exploration.length +
                A.runway.length + 1)
              (g, base) = some (e, stateA) :=
          hdataA.2.2.2.2.1
        have hgroovesAActivated :
            PathGrooves A.toSupported.paths A.activatedState :=
          Eq.mp
            (congrArg
              (fun state =>
                PathGrooves A.toSupported.paths state)
              hactivatedA)
            hgroovesA
        have hbaseOriginal :
            A.baseState = flipAt original k0 :=
          hbaseA.trans hbaseShift
        have hfirstSplit :=
          first_history_absorbed_or_productive_nonquiet_entry_return
            A hN hk0 original hbaseOriginal
              hgroovesAActivated
        rcases hfirstSplit with hhistory | hresidual
        case inr =>
          let O := Exists.choose hresidual
          have hO := Exists.choose_spec hresidual
          let cycle := O.before ++ [(O.p, O.x)]
          have hcycle :=
            productive_entry_writer_occurrence_is_simple_cycle
              A he O hO.1
          have hcycleNonempty : Ne cycle [] := by
            exact hcycle.1
          have htransient :
              PhysicalTrace w (g, A.baseState)
                cycle (g, O.next) :=
            hcycle.2.1
          have hstable :
              PhysicalTrace w (g, O.next)
                cycle (g, O.next) :=
            hcycle.2.2.1
          have hsimple : SwitchSimple cycle :=
            hcycle.2.2.2
          have hstartEq :
              (g, A.baseState) = (g, base) :=
            Prod.ext rfl hbaseA
          have htransientBase :
              PhysicalTrace w (g, base)
                cycle (g, O.next) := by
            exact Eq.mp
              (congrArg
                (fun c => PhysicalTrace w c
                  cycle (g, O.next)) hstartEq)
              htransient
          have hcycleCount :=
            prefix_then_stable_simple_cycle_distinct_le_two_mul_succ
              hN
              (L := 0)
              (start := (g, base))
              (atRepeat := (g, base))
              (cycle := cycle)
              (settled := O.next)
              (by simp [stepN])
              (by omega)
              hcycleNonempty
              htransientBase hstable hsimple
              times hlocalNodup
          omega
        case inl =>
          let H := Classical.choice hhistory
          have hentryB : w.link g = some e :=
            w.symm _ _ hentry
          cases hsecond :
              stepN w (N + 1) (e, stateA) with
          | none =>
              have htailDead : forall tailTimes : List Nat,
                  (forall k, List.Mem k tailTimes ->
                    (stepN w k (e, stateA)).isSome) ->
                  (tailTimes.map
                    (restrictedTonguesAt w N
                      (e, stateA))).Nodup ->
                  tailTimes.length <= N + 1 := by
                intro tailTimes htailLive htailNodup
                exact ultra_live_distinct_le_of_stepN_none
                  (N := N) hsecond htailLive htailNodup
              have hc :=
                one_manufacturing_journey_then_direct_tail_distinct_le
                  hN A stateA hbaseA hactivatedA
                  hreachA hgroovesA htailDead
                  times hlive hlocalNodup
              omega
          | some secondFinish =>
              rcases first_activated_count_outcome_sharp
                  (w := w) (N := N) (e := g)
                  hN hsecond hentryB with
                hcycleB | hreflectorB
              case inl =>
                have htail : forall tailTimes : List Nat,
                    (forall k, List.Mem k tailTimes ->
                      (stepN w k (e, stateA)).isSome) ->
                    (tailTimes.map
                      (restrictedTonguesAt w N
                        (e, stateA))).Nodup ->
                    tailTimes.length <= N + 2 := by
                  intro tailTimes _ htailNodup
                  exact hcycleB tailTimes htailNodup
                have hc :=
                  one_manufacturing_journey_then_direct_tail_distinct_le
                    hN A stateA hbaseA hactivatedA
                    hreachA hgroovesA htail
                    times hlive hlocalNodup
                omega
              case inr =>
                let B := Exists.choose hreflectorB
                have hreflectorBState :=
                  Exists.choose_spec hreflectorB
                let stateB := Exists.choose hreflectorBState
                have hdataB :=
                  Exists.choose_spec hreflectorBState
                have hgroovesB :
                    PathGrooves B.toSupported.paths stateB :=
                  hdataB.2.1
                have hbaseB : B.baseState = stateA :=
                  hdataB.2.2.1
                have hactivatedB :
                    stateB = B.activatedState :=
                  hdataB.2.2.2.1
                have hreachB :
                    stepN w
                      (B.exploration.length +
                        B.runway.length + 1)
                      (e, stateA) =
                        some (g, stateB) :=
                  hdataB.2.2.2.2.1
                have hAatBase :
                    PathGrooves A.toSupported.paths
                      B.baseState := by
                  exact Eq.mp
                    (congrArg
                      (fun state =>
                        PathGrooves A.toSupported.paths state)
                      hbaseB.symm)
                    hgroovesA
                have hBatActivated :
                    PathGrooves B.toSupported.paths
                      B.activatedState :=
                  Eq.mp
                    (congrArg
                      (fun state =>
                        PathGrooves B.toSupported.paths state)
                      hactivatedB)
                    hgroovesB
                have htail : forall tailTimes : List Nat,
                    (forall k, List.Mem k tailTimes ->
                      (stepN w k (g, stateB)).isSome) ->
                    (tailTimes.map
                      (restrictedTonguesAt w N
                        (g, stateB))).Nodup ->
                    tailTimes.length <= 4 := by
                  intro tailTimes htailLive htailNodup
                  have htailLiveActivated :
                      forall k, List.Mem k tailTimes ->
                        (stepN w k
                          (g, B.activatedState)).isSome := by
                    intro k hk
                    have h := htailLive k hk
                    exact Eq.mp
                      (congrArg
                        (fun state =>
                          (stepN w k (g, state)).isSome = true)
                        hactivatedB)
                      h
                  have htailNodupActivated :
                      (tailTimes.map
                        (restrictedTonguesAt w N
                          (g, B.activatedState))).Nodup := by
                    have hmap :
                        tailTimes.map
                          (restrictedTonguesAt w N
                            (g, stateB)) =
                        tailTimes.map
                          (restrictedTonguesAt w N
                            (g, B.activatedState)) := by
                      apply List.map_congr_left
                      intro k _
                      exact congrArg
                        (fun state =>
                          restrictedTonguesAt w N
                            (g, state) k)
                        hactivatedB
                    exact Eq.mp
                      (congrArg List.Nodup hmap)
                      htailNodup
                  exact
                    manufactured_pair_protected_repair_distinct_le_four
                      A B hAatBase hBatActivated
                      tailTimes htailLiveActivated
                        htailNodupActivated
                exact
                  two_journeys_with_initial_history_then_tail
                    hN A B original stateA stateB H
                    hbaseA hactivatedA hreachA
                    hbaseB hactivatedB hreachB hgroovesB
                    htail (by omega)
                    times hlive hnd


/-! ## Exact arbitrary-start theorem -/

private theorem ultra_nodup_map_eq_of_mem
    {alpha beta : Type}
    [BEq alpha] [LawfulBEq alpha]
    [BEq beta] [LawfulBEq beta]
    (f : alpha -> beta)
    {xs : List alpha}
    (hnd : (xs.map f).Nodup)
    {a b : alpha}
    (ha : List.Mem a xs)
    (hb : List.Mem b xs)
    (heq : f a = f b) :
    a = b := by
  induction xs generalizing a b with
  | nil =>
      cases ha
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp ha with ha | ha
      case inl =>
        rcases List.mem_cons.mp hb with hb | hb
        case inl =>
          subst a
          subst b
          rfl
        case inr =>
          subst a
          exfalso
          apply hnd.1
          apply List.mem_map.mpr
          exact Exists.intro b
            (And.intro hb heq.symm)
      case inr =>
        rcases List.mem_cons.mp hb with hb | hb
        case inl =>
          subst b
          exfalso
          apply hnd.1
          apply List.mem_map.mpr
          exact Exists.intro a
            (And.intro ha heq)
        case inr =>
          exact ih hnd.2 ha hb heq

theorem ultra_nodup_filter_nat
    (p : Nat -> Bool) :
    forall {xs : List Nat},
      xs.Nodup -> (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true,
            List.nodup_cons]
          constructor
          case left =>
            intro hm
            apply hnd.1
            exact (List.mem_filter.mp hm).1
          case right =>
            exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

theorem ultra_zero_positive_partition :
    forall xs : List Nat,
      (xs.filter
        (fun k => decide (k = 0))).length +
      (xs.filter
        (fun k => decide (0 < k))).length =
      xs.length := by
  intro xs
  induction xs with
  | nil =>
      simp
  | cons k rest ih =>
      by_cases hk : k = 0
      case pos =>
        subst k
        simp
        omega
      case neg =>
        have hkPos : 0 < k := by
          omega
        simp [hk, hkPos]
        omega

theorem ultra_zero_filter_length_le_one
    {xs : List Nat}
    (hnd : xs.Nodup) :
    (xs.filter
      (fun k => decide (k = 0))).length <= 1 := by
  have hfilterNodup :
      (xs.filter
        (fun k => decide (k = 0))).Nodup :=
    ultra_nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

private theorem ultra_known_edge_distinct_le_two_mul_add_six
    {w : Wiring} {N e : Nat}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    {start : Prod Nat Tongues}
    (hentry : w.link e = some start.1)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= 2 * N + 6 := by
  have hc :=
    known_edge_all_run_distinct_le_of_protected_cap
      hN
      (tailCap := 4)
      (by omega)
      (fun A B hA hB tailTimes
          htailLive htailNodup =>
        manufactured_pair_protected_repair_distinct_le_four
          A B hA hB tailTimes
            htailLive htailNodup)
      hentry times hlive hnd
  omega

/-- **Unconditional raw 2*N+6 theorem.**

For any N-switch lazy-point wiring, arbitrary starting port and tongue vector,
and any list of live sample times carrying pairwise-distinct restricted tongue
vectors, at most 2*N+6 samples are possible. -/
theorem state_law_linear_two_add_six_ultra
    (w : Wiring) (N : Nat)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (start : Prod Nat Tongues)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length <= 2 * N + 6 := by
  cases start with
  | mk startPort startState =>
      have htimesNodup : times.Nodup :=
        ultra_nodup_of_map_nodup
          (restrictedTonguesAt w N
            (startPort, startState)) hnd
      cases hone :
          stepN w 1 (startPort, startState) with
      | none =>
          have hc :=
            ultra_live_distinct_le_of_stepN_none
              (N := N) hone hlive hnd
          omega
      | some middle =>
          simp only [stepN, step] at hone
          let localStep := arrive startState startPort
          cases hlink : w.link localStep.1 with
          | none =>
              simp [localStep, hlink] at hone
          | some entry =>
              have hmiddle :
                  middle = (entry, localStep.2) := by
                simpa [localStep, hlink] using hone.symm
              subst middle
              have honeStep :
                  stepN w 1 (startPort, startState) =
                    some (entry, localStep.2) := by
                simp [stepN, step, localStep, hlink]
              let positive :=
                times.filter (fun k => decide (0 < k))
              let shifted :=
                positive.map (fun k => k - 1)
              let zeroTimes :=
                times.filter (fun k => decide (k = 0))
              have hshiftVector :
                  shifted.map
                    (restrictedTonguesAt w N
                      (entry, localStep.2)) =
                  positive.map
                    (restrictedTonguesAt w N
                      (startPort, startState)) := by
                dsimp [shifted]
                rw [List.map_map]
                apply List.map_congr_left
                intro k hk
                have hkPos : 0 < k :=
                  of_decide_eq_true
                    (List.mem_filter.mp hk).2
                have hkTimes : List.Mem k times :=
                  (List.mem_filter.mp hk).1
                have hkEq : k = 1 + (k - 1) := by
                  omega
                have hkLive := hlive k hkTimes
                have hrun :
                    stepN w k
                      (startPort, startState) =
                    stepN w (k - 1)
                      (entry, localStep.2) := by
                  rw [hkEq, stepN_add, honeStep]
                  simp
                cases htail :
                    stepN w (k - 1)
                      (entry, localStep.2) with
                | none =>
                    rw [hrun, htail] at hkLive
                    simp at hkLive
                | some localFinish =>
                    have hglobal :
                        stepN w k
                          (startPort, startState) =
                          some localFinish := by
                      rw [hrun, htail]
                    simp [Function.comp_apply,
                      restrictedTonguesAt, tonguesAt,
                      hglobal, htail]
              have hpositiveNodup :
                  (positive.map
                    (restrictedTonguesAt w N
                      (startPort, startState))).Nodup := by
                dsimp [positive]
                exact ultra_nodup_map_filter _ hnd
              have hshiftedNodup :
                  (shifted.map
                    (restrictedTonguesAt w N
                      (entry, localStep.2))).Nodup := by
                rw [hshiftVector]
                exact hpositiveNodup
              have hshiftedLive :
                  forall d, List.Mem d shifted ->
                    (stepN w d
                      (entry, localStep.2)).isSome := by
                intro d hd
                obtain data := List.mem_map.mp hd
                let k := Exists.choose data
                have hk := Exists.choose_spec data
                have hkd : k - 1 = d := hk.2
                have hkTimes : List.Mem k times :=
                  (List.mem_filter.mp hk.1).1
                have hkPos : 0 < k :=
                  of_decide_eq_true
                    (List.mem_filter.mp hk.1).2
                have hkEq : k = 1 + (k - 1) := by
                  omega
                have hkLiveRaw := hlive k hkTimes
                rw [hkEq, stepN_add, honeStep] at hkLiveRaw
                have hkLive :
                    (stepN w (k - 1)
                      (entry, localStep.2)).isSome := by
                  simpa using hkLiveRaw
                exact Eq.mp
                  (congrArg
                    (fun z =>
                      (stepN w z
                        (entry, localStep.2)).isSome = true)
                    hkd)
                  hkLive
              have hpositiveLength :
                  positive.length = shifted.length := by
                simp [shifted]
              have hzeroBound :
                  zeroTimes.length <= 1 := by
                dsimp [zeroTimes]
                exact ultra_zero_filter_length_le_one
                  htimesNodup
              have hpartition :
                  zeroTimes.length + positive.length =
                    times.length := by
                simpa [zeroTimes, positive] using
                  ultra_zero_positive_partition times
              by_cases hzero : List.Mem 0 times
              case neg =>
                have hzeroLength :
                    zeroTimes.length = 0 := by
                  cases hz : zeroTimes with
                  | nil =>
                      simp
                  | cons z rest =>
                      have hzmem :
                          List.Mem z zeroTimes := by
                        rw [hz]
                        exact List.mem_cons_self
                      have hzdata :=
                        List.mem_filter.mp hzmem
                      have hz0 : z = 0 :=
                        of_decide_eq_true hzdata.2
                      subst z
                      exact (hzero hzdata.1).elim
                have hshiftedBound :=
                  ultra_known_edge_distinct_le_two_mul_add_six
                    hN hlink shifted
                      hshiftedLive hshiftedNodup
                omega
              case pos =>
                have hzeroMem :
                    List.Mem 0 zeroTimes := by
                  dsimp [zeroTimes]
                  apply List.mem_filter.mpr
                  exact And.intro hzero
                    (decide_eq_true rfl)
                have hzeroLengthNe :
                    Ne zeroTimes.length 0 := by
                  intro hlen
                  cases hz : zeroTimes with
                  | nil =>
                      rw [hz] at hzeroMem
                      cases hzeroMem
                  | cons z rest =>
                      simp [hz] at hlen
                have hzeroLength :
                    zeroTimes.length = 1 := by
                  omega
                have hzeroVector :
                    restrictedTonguesAt w N
                      (startPort, startState) 0 =
                      VectorCount.restrict N startState := by
                  simp [restrictedTonguesAt,
                    tonguesAt, stepN]
                have haugmentedNodup :
                    (VectorCount.restrict N startState ::
                      shifted.map
                        (restrictedTonguesAt w N
                          (entry, localStep.2))).Nodup := by
                  rw [List.nodup_cons]
                  constructor
                  case left =>
                    intro hm
                    rw [hshiftVector] at hm
                    obtain data := List.mem_map.mp hm
                    let k := Exists.choose data
                    have hk := Exists.choose_spec data
                    have hkTimes : List.Mem k times :=
                      (List.mem_filter.mp hk.1).1
                    have hkPos : 0 < k :=
                      of_decide_eq_true
                        (List.mem_filter.mp hk.1).2
                    have heq :
                        restrictedTonguesAt w N
                          (startPort, startState) 0 =
                        restrictedTonguesAt w N
                          (startPort, startState) k :=
                      hzeroVector.trans hk.2.symm
                    have htimeEq :=
                      ultra_nodup_map_eq_of_mem
                        (restrictedTonguesAt w N
                          (startPort, startState))
                        hnd hzero hkTimes heq
                    omega
                  case right =>
                    exact hshiftedNodup
                by_cases hsame :
                    localStep.2 = startState
                case pos =>
                  let augmented := 0 :: shifted
                  have haugmentedLive :
                      forall d, List.Mem d augmented ->
                        (stepN w d
                          (entry, localStep.2)).isSome := by
                    intro d hd
                    rcases List.mem_cons.mp hd with hd | hd
                    case inl =>
                      subst d
                      simp [stepN]
                    case inr =>
                      exact hshiftedLive d hd
                  have hlocalZero :
                      restrictedTonguesAt w N
                        (entry, localStep.2) 0 =
                        VectorCount.restrict N startState := by
                    simp [restrictedTonguesAt,
                      tonguesAt, stepN, hsame]
                  have haugmentedLocalNodup :
                      (augmented.map
                        (restrictedTonguesAt w N
                          (entry, localStep.2))).Nodup := by
                    dsimp [augmented]
                    try simp only [List.map_cons]
                    rw [hlocalZero]
                    exact haugmentedNodup
                  have haugmentedBound :=
                    ultra_known_edge_distinct_le_two_mul_add_six
                      hN hlink augmented
                        haugmentedLive
                        haugmentedLocalNodup
                  have haugmentedLength :
                      augmented.length =
                        shifted.length + 1 := by
                    simp [augmented]
                  omega
                case neg =>
                  let k0 := startPort / 3
                  have harrive :
                      arrive startState startPort =
                        (localStep.1, localStep.2) := by
                    simp [localStep]
                  have hchanged :
                      Ne (localStep.2 k0)
                        (startState k0) := by
                    intro heq
                    apply hsame
                    funext j
                    by_cases hj : j = k0
                    case pos =>
                      subst j
                      exact heq
                    case neg =>
                      exact arrive_preserves_other
                        harrive hj
                  have htrailing :=
                    changed_arrival_is_trailing
                      harrive hchanged
                  have he :
                      localStep.1 = 3 * k0 := by
                    exact htrailing.2.1
                  have hk0 : k0 < N := by
                    have hportBound :=
                      (hN localStep.1 entry hlink).1
                    dsimp [k0] at he
                    omega
                  have hbaseShift :
                      localStep.2 =
                        flipAt startState k0 := by
                    exact changed_arrival_eq_flipAt
                      harrive hchanged
                  have hbound :=
                    known_edge_with_productive_initial_distinct_le_two_mul_add_six
                      hN hlink he hk0
                      startState localStep.2 hbaseShift
                      shifted hshiftedLive
                        haugmentedNodup
                  omega

end GeneralN
