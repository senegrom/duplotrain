import ChangedContactNAddFour

/-!
# The protected-pair `N+4` bound

The two manufacturing journeys share one coordinate budget and one canonical
history. A stay reflector adds no new tail vectors. For a flip reflector,
either its action coordinate is reserved, giving `N+2`, or
its occurrence in the second construction recovers a historical Gray corner.
Starting the pair at the protected pre-return state covers the actual
continuation by four action corners. Two corners are historical, and an
action writer recovers a third: `(N+2)+2 = (N+3)+1 = N+4`.

No repair-route classification is needed; the actual boundary is reached by
one traversal of the already grooved second reflector.
-/

namespace GeneralN

section
variable {w : Wiring} {N g e : Nat}
include w N g e

/-- The protected pair needs only a coordinate-usage split, not a writer-order
split. If the old flip action is absent from the second writer list, reserve
that coordinate and pay `(N+2)+2`. If present, its last-write history recovers
one tail corner and we pay `(N+3)+1`. A stay reflector has no fresh tail corner.
The same canonical history is used in every case; no second erasure is needed. -/
theorem ManufacturedReflector.preReturn_grooved_protected_pair_all_run_distinct_le_N_add_four
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 4 := by
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  let history := A.continuationHistory N (e, B.baseState) B.exploration.length ++
    [VectorCount.restrict N B.activatedState]
  have hhistory : ∀ x, x ∈ A.sharpConstructionHistory N ∨
      x ∈ B.sharpConstructionHistory N → x ∈ history := by
    intro x hx
    rcases hx with hx | hx
    · exact List.mem_append_left _ (List.mem_append_left _ (A.mem_sharpHistoryCore_of_mem hx))
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        exact List.mem_append_left _ (A.mem_continuationHistory B.exploration_trace (by have := List.mem_range.mp hj; omega))
      · exact List.mem_append_right _ hx
  have hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history :=
    hhistory (VectorCount.restrict N B.preReturn.2) (Or.inr (List.mem_append_left _
      (List.mem_map.mpr ⟨B.exploration.length, List.mem_range.mpr (by omega),
        by simp [restrictedTonguesAt, tonguesAt, B.exploration_trace.sound]⟩)))
  have hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history :=
    hhistory _ (Or.inr B.activated_mem_sharpHistory)
  have hcount (fresh : List (List Bool))
      (hpreCorner : VectorCount.restrict N (A.toSupported.action.apply B.preReturn.2) ∈ history ++ fresh)
      (hactivatedCorner : VectorCount.restrict N (A.toSupported.action.apply B.activatedState) ∈ history ++ fresh) :
      times.length ≤ history.length + fresh.length := by
    apply noveltyCoverOn_distinct_count (hnd := hnd)
    refine ⟨fresh, Nat.le_refl _, fun k hk => ?_⟩
    apply A.journey_then_live_cover hApaths (history ++ fresh)
      (fun x hx => List.mem_append_left _ (hhistory x (Or.inl hx))) ?_ (hlive k hk)
    intro j hj
    rw [← hbase] at hj ⊢
    apply B.journey_then_live_cover hBpaths (history ++ fresh)
      (fun x hx => List.mem_append_left _ (hhistory x (Or.inr hx))) ?_ hj
    intro d hd
    have hp := A.preReturn_pair_corners B hBpaths hpre hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp | hp | hp <;>
      simp only [restrictedTonguesAt, hp] <;>
      first | exact List.mem_append_left _ hpreHistorical
            | exact List.mem_append_left _ hinitialHistorical
            | exact hpreCorner | exact hactivatedCorner
  have hlen : history.length ≤ N + 3 := by
    have h := A.continuationHistory_length_le hN hbase B.exploration_trace
      B.exploration_simple hAatBase hpre
    simpa [history] using Nat.add_le_add_right h 1
  cases A with
  | stay R =>
      change ∀ fresh, VectorCount.restrict N B.preReturn.2 ∈ history ++ fresh →
        VectorCount.restrict N B.activatedState ∈ history ++ fresh →
        times.length ≤ history.length + fresh.length at hcount
      have h := hcount [] (by simpa using hpreHistorical) (by simpa using hinitialHistorical)
      simp only [List.length_nil] at h
      omega
  | flip R =>
      change ∀ fresh, VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) ∈ history ++ fresh →
        VectorCount.restrict N (flipAt B.activatedState R.actionSwitch) ∈ history ++ fresh →
        times.length ≤ history.length + fresh.length at hcount
      by_cases haction : R.actionSwitch ∈ B.constructionWriterSwitches N
      · obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp haction
        have hcorner : VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch) ∈ history := by
          rw [R.action_writer_recovers B.exploration_trace B.exploration_simple hAatBase hpre ht hwriter]
          exact hhistory _ (Or.inr (List.mem_append_left _ (List.mem_map.mpr
            ⟨t, List.mem_range.mpr (Nat.lt_succ_of_lt (mem_rawProductiveTimes_iff.mp ht).1), rfl⟩)))
        have h := hcount [VectorCount.restrict N (flipAt B.activatedState R.actionSwitch)]
          (by simp [hcorner]) (by simp)
        simp only [List.length_singleton] at h
        omega
      · have hreserved : history.length ≤ N + 2 := by
          have h := (ManufacturedReflector.flip R).continuationHistory_length_le hN hbase
            B.exploration_trace B.exploration_simple hAatBase hpre [R.actionSwitch]
            (by simp) (by simpa using R.action_lt hN)
            (by simpa using R.action_not_mem_reusable) (by simpa only [List.mem_singleton, forall_eq, ManufacturedReflector.constructionWriterSwitches] using haction)
          simpa [history] using h
        have h := hcount [VectorCount.restrict N (flipAt B.preReturn.2 R.actionSwitch),
          VectorCount.restrict N (flipAt B.activatedState R.actionSwitch)] (by simp) (by simp)
        simp only [List.length_cons, List.length_nil] at h
        omega

end

end GeneralN
