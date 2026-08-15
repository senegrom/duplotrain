import KnownEdgeLift
import SingleCoordinateFlip
import RunwayHistoricalOne
import CompleteRepairFour

/-!
# The arbitrary-start boundary charge

This file isolates the first-history case split needed to remove the final
singleton in state_law_linear_two_sharper. It intentionally imports the
shared proof chain without modifying it.
-/

namespace GeneralN

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
    nodup_subset_length_nat hnd hsubset
  simp only [List.length_cons, List.length_map,
    List.length_append] at hcount
  have hfreshLength : fresh.length <= budget := by
    simpa [fresh] using hfresh.1
  omega


/-! ## Two journeys with an arbitrary first-history cover -/


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


