import KnownEdgeLift

/-!
# Arbitrary-start lift without a long-run hypothesis

A successful first step exposes the physical edge just crossed.  Therefore an
all-runs bound for starts with a known incoming edge applies immediately to all
positive sample times after shifting them down by one.  Time zero contributes
at most one additional restricted tongue vector.

Unlike `arbitrary_start_distinct_le_succ_of_known_edge`, this lift has no
`3 * N + 3` survival split and no arithmetic side condition: its known-edge
hypothesis already covers runs of every length.
-/

namespace GeneralN

private theorem asdl_nodup_of_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

private theorem asdl_nodup_map_filter
    {α : Type} [BEq α] [LawfulBEq α]
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            apply hnd.1
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem asdl_nodup_filter_nat (p : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hm => hnd.1 (List.mem_filter.mp hm).1, ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem asdl_zero_positive_partition :
    ∀ xs : List Nat,
      (xs.filter (fun k => decide (k = 0))).length +
        (xs.filter (fun k => decide (0 < k))).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons k rest ih =>
      by_cases hk : k = 0
      · subst k
        simp
        omega
      · have hkPos : 0 < k := by omega
        simp [hk, hkPos]
        omega

private theorem asdl_zero_filter_length_le_one
    {xs : List Nat} (hnd : xs.Nodup) :
    (xs.filter (fun k => decide (k = 0))).length ≤ 1 := by
  have hfilterNodup :
      (xs.filter (fun k => decide (k = 0))).Nodup :=
    asdl_nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

/-- If every run whose starting entry has a known incoming physical edge has
at most `cap` distinct restricted tongue vectors, then a run starting at an
arbitrary entry has at most `cap + 1`.  No long-run or short-run hypothesis is
needed: after one successful step the edge just traversed witnesses the
known-edge premise, and only the time-zero vector lies outside the shifted
tail. -/
theorem arbitrary_start_distinct_le_succ_of_all_known_edge
    {w : Wiring} {N cap : Nat}
    (hknown : ∀ {e : Nat} {localStart : Nat × Tongues},
      w.link e = some localStart.1 →
      ∀ localTimes : List Nat,
        (∀ k ∈ localTimes, (stepN w k localStart).isSome) →
        (localTimes.map
          (restrictedTonguesAt w N localStart)).Nodup →
        localTimes.length ≤ cap)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ cap + 1 := by
  have htimesNodup : times.Nodup :=
    asdl_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  cases hone : stepN w 1 start with
  | none =>
      have hzero : ∀ k ∈ times, k = 0 := by
        intro k hk
        by_cases hk0 : k = 0
        · exact hk0
        · have hkPos : 0 < k := by omega
          have hkEq : k = 1 + (k - 1) := by omega
          have hnone : stepN w k start = none := by
            rw [hkEq, stepN_add, hone]
            simp
          have hkLive := hlive k hk
          simp [hnone] at hkLive
      have hlen : times.length ≤ 1 :=
        nodup_nat_lt_length htimesNodup (by
          intro k hk
          have := hzero k hk
          omega)
      omega
  | some middle =>
      rcases start with ⟨startPort, startState⟩
      have honeStep : stepN w 1 (startPort, startState) =
          some middle := hone
      simp only [stepN, step] at hone
      let localStep := arrive startState startPort
      cases hlink : w.link localStep.1 with
      | none =>
          simp [localStep, hlink] at hone
      | some entry =>
          have hmiddle : middle = (entry, localStep.2) := by
            simpa [localStep, hlink] using hone.symm
          subst middle
          let positive := times.filter (fun k => decide (0 < k))
          let shifted := positive.map (fun k => k - 1)
          have hshiftVector : shifted.map
              (restrictedTonguesAt w N (entry, localStep.2)) =
              positive.map
                (restrictedTonguesAt w N (startPort, startState)) := by
            dsimp [shifted]
            rw [List.map_map]
            apply List.map_congr_left
            intro k hk
            have hkPos : 0 < k :=
              of_decide_eq_true (List.mem_filter.mp hk).2
            have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
            have hkEq : k = 1 + (k - 1) := by omega
            have hrun : stepN w k (startPort, startState) =
                stepN w (k - 1) (entry, localStep.2) := by
              rw [hkEq, stepN_add, honeStep]
              simp
            have hkLive := hlive k hkTimes
            cases htail : stepN w (k - 1) (entry, localStep.2) with
            | none =>
                rw [hrun, htail] at hkLive
                simp at hkLive
            | some localFinish =>
                have hglobal : stepN w k (startPort, startState) =
                    some localFinish := by rw [hrun, htail]
                simp [Function.comp_apply, restrictedTonguesAt,
                  tonguesAt, hglobal, htail]
          have hpositiveNodup :
              (positive.map (restrictedTonguesAt w N
                (startPort, startState))).Nodup := by
            dsimp [positive]
            exact asdl_nodup_map_filter _ hnd
          have hshiftedNodup :
              (shifted.map (restrictedTonguesAt w N
                (entry, localStep.2))).Nodup := by
            rw [hshiftVector]
            exact hpositiveNodup
          have hshiftedLive : ∀ d ∈ shifted,
              (stepN w d (entry, localStep.2)).isSome := by
            intro d hd
            obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
            have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
            have hkPos : 0 < k :=
              of_decide_eq_true (List.mem_filter.mp hk).2
            have hkEq : k = 1 + (k - 1) := by omega
            have hkLive := hlive k hkTimes
            rw [hkEq, stepN_add, honeStep] at hkLive
            exact hkLive
          have hshiftedBound : shifted.length ≤ cap :=
            hknown hlink shifted hshiftedLive hshiftedNodup
          have hpositiveLength : positive.length = shifted.length := by
            simp [shifted]
          have hzeroBound :
              (times.filter (fun k => decide (k = 0))).length ≤ 1 :=
            asdl_zero_filter_length_le_one htimesNodup
          have hpartition := asdl_zero_positive_partition times
          dsimp [positive] at hpositiveLength
          omega

end GeneralN
