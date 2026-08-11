import KnownEdgeTwoAll

/-!
# Horizon-free lift from a known incoming edge

A successful first step exposes the physical edge just crossed.  Positive
sample times are shifted by one and handed directly to an all-run known-edge
bound; time zero contributes at most one further vector.  Unlike the older
`KnownEdgeLift`, no coarse short-run time cap is required.
-/

namespace GeneralN

private theorem keal_nodup_of_map_nodup
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

private theorem keal_nodup_map_filter
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

private theorem keal_nodup_filter_nat (p : Nat → Bool) :
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

private theorem keal_zero_positive_partition :
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

private theorem keal_zero_filter_length_le_one
    {xs : List Nat} (hnd : xs.Nodup) :
    (xs.filter (fun k => decide (k = 0))).length ≤ 1 := by
  have hfilterNodup :
      (xs.filter (fun k => decide (k = 0))).Nodup :=
    keal_nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

/-- Lift any all-run known-edge cap `cap` to an arbitrary-start cap `cap+1`.
No long-run or short-run arithmetic hypothesis is needed. -/
theorem arbitrary_start_distinct_le_succ_of_known_edge_all
    {w : Wiring} {N cap : Nat}
    (hknown : ∀ {e : Nat} {localStart : Nat × Tongues},
      w.link e = some localStart.1 →
      ∀ localTimes : List Nat,
        (∀ k ∈ localTimes,
          (stepN w k localStart).isSome) →
        (localTimes.map
          (restrictedTonguesAt w N localStart)).Nodup →
        localTimes.length ≤ cap)
    (start : Nat × Tongues) (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ cap + 1 := by
  have htimesNodup : times.Nodup :=
    keal_nodup_of_map_nodup
      (restrictedTonguesAt w N start) hnd
  cases hstep : step w start with
  | none =>
      have hlt : ∀ k ∈ times, k < 1 := by
        intro k hk
        cases k with
        | zero => omega
        | succ k =>
            have hkLive := hlive (k + 1) hk
            simp [stepN, hstep] at hkLive
      have hsmall := nodup_nat_lt_length htimesNodup hlt
      omega
  | some next =>
      have hstepOne : stepN w 1 start = some next := by
        simpa [stepN] using hstep
      let positive := times.filter (fun k => decide (0 < k))
      let shifted := positive.map (fun k => k - 1)
      have hshiftVector : shifted.map
          (restrictedTonguesAt w N next) =
          positive.map (restrictedTonguesAt w N start) := by
        dsimp [shifted]
        rw [List.map_map]
        apply List.map_congr_left
        intro k hk
        have hkPos : 0 < k :=
          of_decide_eq_true (List.mem_filter.mp hk).2
        have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
        have hkEq : k = 1 + (k - 1) := by omega
        have hrun : stepN w k start =
            stepN w (k - 1) next := by
          rw [hkEq, stepN_add, hstepOne]
          simp
        have hkLive := hlive k hkTimes
        cases htail : stepN w (k - 1) next with
        | none =>
            rw [hrun, htail] at hkLive
            simp at hkLive
        | some finish =>
            have hglobal : stepN w k start = some finish := by
              rw [hrun, htail]
            simp [Function.comp_apply, restrictedTonguesAt, tonguesAt,
              hglobal, htail]
      have hpositiveNodup :
          (positive.map (restrictedTonguesAt w N start)).Nodup := by
        dsimp [positive]
        exact keal_nodup_map_filter _ hnd
      have hshiftedNodup :
          (shifted.map
            (restrictedTonguesAt w N next)).Nodup := by
        rw [hshiftVector]
        exact hpositiveNodup
      have hshiftedLive : ∀ d ∈ shifted,
          (stepN w d next).isSome := by
        intro d hd
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hd
        have hkTimes : k ∈ times := (List.mem_filter.mp hk).1
        have hkPos : 0 < k :=
          of_decide_eq_true (List.mem_filter.mp hk).2
        have hkEq : k = 1 + (k - 1) := by omega
        have hkLive := hlive k hkTimes
        rw [hkEq, stepN_add, hstepOne] at hkLive
        exact hkLive
      have hentry : w.link (exitPort start) = some next.1 :=
        (step_some_parts hstep).1
      have hshiftedBound : shifted.length ≤ cap :=
        hknown hentry shifted hshiftedLive hshiftedNodup
      have hpositiveLength : positive.length = shifted.length := by
        simp [shifted]
      have hzeroBound :
          (times.filter (fun k => decide (k = 0))).length ≤ 1 :=
        keal_zero_filter_length_le_one htimesNodup
      have hpartition := keal_zero_positive_partition times
      dsimp [positive] at hpositiveLength
      omega

end GeneralN
