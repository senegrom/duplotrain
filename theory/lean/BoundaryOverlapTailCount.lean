import TwoJourneyTailCountSharp

/-!
# Boundary-aware direct-tail counting

A directly counted suffix starts at a vector already present at the end of the
prefix.  Filter later suffix samples equal to that boundary; for all remaining
samples, adjoin suffix time zero and invoke the tail cap.  This saves one
vector exactly compared with naïvely adding the two cardinality bounds.
-/

namespace GeneralN

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
    exact tailsharp_nodup_map_filter _ hnd
  have hshiftedNodup :
      (shifted.map
        (restrictedTonguesAt w N endpoint)).Nodup := by
    rw [hlateVector]
    exact hlateNodup
  have hotherNodup : otherVectors.Nodup := by
    dsimp [otherVectors, other]
    exact tailsharp_nodup_map_filter _ hshiftedNodup
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

/-- Generic boundary-overlap theorem.  `prefixHistory` covers every time up to
and including `lead`; the suffix begins at `endpoint`, whose vector is already
in that history.  A direct suffix cap `cap` then contributes only `cap-1`
additional vectors. -/
theorem boundary_history_then_direct_tail_distinct_le
    {w : Wiring} {N lead cap : Nat}
    {start endpoint : Nat × Tongues}
    (hreach : stepN w lead start = some endpoint)
    (prefixHistory : List (List Bool))
    (hprefixCover : ∀ d, d ≤ lead →
      restrictedTonguesAt w N start d ∈ prefixHistory)
    (hboundary : VectorCount.restrict N endpoint.2 ∈ prefixHistory)
    (htail : ∀ (tailTimes : List Nat),
      (∀ k ∈ tailTimes, (stepN w k endpoint).isSome) →
      (tailTimes.map (restrictedTonguesAt w N endpoint)).Nodup →
      tailTimes.length ≤ cap)
    (hcapPos : 0 < cap)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ prefixHistory.length + cap - 1 := by
  have hcover := boundary_history_then_direct_tail_cover
    hreach prefixHistory hprefixCover hboundary htail hcapPos
      times hlive hnd
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  omega

end GeneralN
