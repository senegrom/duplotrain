import BoundaryResidualNovelty

/-!
# The absent initial coordinate across a fully protected pair

If the productive boundary switch is absent from the first manufactured
exploration, it is a genuinely unused coordinate of the first support.  If
it is also absent from the productive first writers of the second
construction, that reserved coordinate pays for adjoining the arbitrary
pre-passage vector.  A flip reflector has a second reserved coordinate when
its facing action is absent from the second first writers; when the action
is present, the protected repair costs only one new vector.

Everything here is uniform in `N`.
-/

namespace GeneralN

/-- Every reusable support coordinate occurs in the full manufactured
exploration. -/
theorem ManufacturedReflector.mem_exploration_of_mem_reusable
    {w : Wiring} {g e k : Nat}
    (A : ManufacturedReflector w g e)
    (hk : List.Mem k A.reusableSwitches) :
    List.Mem k (A.exploration.map passageSwitch) := by
  cases A with
  | stay R =>
      simpa [ManufacturedReflector.reusableSwitches,
        ManufacturedReflector.exploration] using hk
  | flip R =>
      change k ∈ (R.runway ++ R.candy).map passageSwitch at hk
      change k ∈
        (R.runway ++ (R.mouth, R.firstArm) :: R.candy).map passageSwitch
      rw [List.map_append] at hk ⊢
      rcases List.mem_append.mp hk with hrunway | hcandy
      · exact List.mem_append_left _ hrunway
      · apply List.mem_append_right
        simpa only [List.map_cons] using List.mem_cons_of_mem
          (passageSwitch (R.mouth, R.firstArm)) hcandy

/-- A coordinate absent from the full exploration is absent from the
reusable support. -/
theorem ManufacturedReflector.not_mem_reusable_of_not_mem_exploration
    {w : Wiring} {g e k : Nat}
    (A : ManufacturedReflector w g e)
    (hk : Not (List.Mem k (A.exploration.map passageSwitch))) :
    Not (List.Mem k A.reusableSwitches) := by grind [
      ManufacturedReflector.mem_exploration_of_mem_reusable]

/-- For a stay reflector, one reserved coordinate lowers the complete
two-construction history core to `N+1`: unlike a flip reflector, a stay
reflector has no omitted facing-mouth surcharge. -/
theorem ManufacturedStayReflector.protectedHistory_length_le_N_add_one_of_reserved
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState =
      (ManufacturedReflector.stay R).activatedState)
    (hbaseGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.baseState)
    (hpreGrooves : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentA : Not (List.Mem k0
      (ManufacturedReflector.stay R).reusableSwitches))
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N))) :
    ((ManufacturedReflector.stay R).preservedTwoHistoryCore B N).length ≤
      N + 1 := by
  let A : ManufacturedReflector w g e := .stay R
  have hboundary : VectorCount.restrict N A.activatedState ∈
      B.writerConstructionHistory N := by
    dsimp [A]
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase]
  have hcharge := A.reusable_add_second_first_writers_add_reserved_le
    hN B hbaseGrooves hpreGrooves hk0
      (by simpa [A] using habsentA) habsentB
  have heq : A.exploration.length = A.reusableSwitches.length := by
    simp [A, ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length, B.writerConstructionHistory_length]
  omega

/-- Assemble a two-journey historical cover with one already historical
boundary vector. -/
private theorem two_journeys_history_count_with_extra
    {w : Wiring} {N g e budget : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (history : List (List Bool))
    (hhistory : forall x,
      x ∈ A.sharpConstructionHistory N \/
        x ∈ B.sharpConstructionHistory N -> x ∈ history)
    (hcap : history.length + budget ≤ N + 4)
    (htail : forall tailTimes : List Nat,
      (forall k, k ∈ tailTimes ->
        (stepN w k (g, B.activatedState)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup ->
      NoveltyCoverOn w N (g, B.activatedState) tailTimes
        history budget)
    (extra : List Bool)
    (hextra : extra ∈ history)
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (extra :: times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length + 1 ≤ N + 4 := by
  have hcover := A.two_journeys_then_shared_history_novelty_cover
    B hbase hApaths hBpaths history hhistory budget htail
      times hlive (List.nodup_cons.mp hnd).2
  have hcount := noveltyCoverOn_distinct_count_with_extra
    hcover hextra hnd
  omega

/-- Exact `N+4` bound for an absent productive boundary followed by a stay
reflector and a fully protected opposite reflector, provided the reserved
boundary coordinate is not a productive first writer of the second
construction. -/
theorem ManufacturedStayReflector.absent_initial_protected_pair_all_run_distinct_le_N_add_four
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hbase : B.baseState =
      (ManufacturedReflector.stay R).activatedState)
    (hApaths : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths
        (ManufacturedReflector.stay R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.stay R).toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentA : Not (List.Mem k0
      ((ManufacturedReflector.stay R).exploration.map passageSwitch)))
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N)))
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.stay R).baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map (restrictedTonguesAt w N
        (g, (ManufacturedReflector.stay R).baseState))).Nodup) :
    times.length + 1 ≤ N + 4 := by
  let A : ManufacturedReflector w g e := .stay R
  let history := VectorCount.restrict N original ::
    A.preservedTwoHistoryCore B N
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have habsentReusable : Not (List.Mem k0 A.reusableSwitches) := by
    apply A.not_mem_reusable_of_not_mem_exploration
    simpa [A] using habsentA
  have hcore := R.protectedHistory_length_le_N_add_one_of_reserved
    hN B hbase hAatBase hpre hk0
      (by simpa [A] using habsentReusable) habsentB
  have hhistory : forall x,
      x ∈ A.sharpConstructionHistory N \/
        x ∈ B.sharpConstructionHistory N -> x ∈ history := by
    intro x hx
    apply List.mem_cons_of_mem
    exact A.mem_preservedTwoHistoryCore B hx
  have htail : forall tailTimes : List Nat,
      (forall k, k ∈ tailTimes ->
        (stepN w k (g, B.activatedState)).isSome) ->
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup ->
      NoveltyCoverOn w N (g, B.activatedState) tailTimes history 2 := by
    intro tailTimes htailLive htailNodup
    exact A.protected_repair_two_novelty_over_history
      hN B hAatBase hBpaths hpre history hhistory
        tailTimes htailLive htailNodup
  have hcap : history.length + 2 ≤ N + 4 := by
    dsimp [history]
    simpa [A] using (show
      ((ManufacturedReflector.stay R).preservedTwoHistoryCore B N).length +
          1 + 2 ≤ N + 4 by omega)
  apply two_journeys_history_count_with_extra
    A B hbase hApaths hBpaths history hhistory hcap htail
      (VectorCount.restrict N original)
  · simp [history]
  · simpa [A] using hlive
  · simpa [A] using hnd

/-- Exact `N+4` bound for the corresponding flip-reflector case.  The old
action writer splits the proof: present costs one tail vector; absent gives
a second reserved coordinate and costs two. -/
theorem ManufacturedFlipReflector.absent_initial_protected_pair_all_run_distinct_le_N_add_four
    {w : Wiring} {N g e k0 : Nat}
    (hN : forall p q, w.link p = some q ->
      p < 3 * N /\ q < 3 * N)
    (R : ManufacturedFlipReflector w g e)
    (B : ManufacturedReflector w e g)
    (original : Tongues)
    (hbase : B.baseState =
      (ManufacturedReflector.flip R).activatedState)
    (hApaths : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths
        (ManufacturedReflector.flip R).activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves
      (ManufacturedReflector.flip R).toSupported.paths B.preReturn.2)
    (hk0 : k0 < N)
    (habsentA : Not (List.Mem k0
      ((ManufacturedReflector.flip R).exploration.map passageSwitch)))
    (habsentB : Not (List.Mem k0
      (B.constructionFirstWriterSwitches N)))
    (times : List Nat)
    (hlive : forall k, k ∈ times ->
      (stepN w k
        (g, (ManufacturedReflector.flip R).baseState)).isSome)
    (hnd : (VectorCount.restrict N original ::
      times.map (restrictedTonguesAt w N
        (g, (ManufacturedReflector.flip R).baseState))).Nodup) :
    times.length + 1 ≤ N + 4 := by
  let A : ManufacturedReflector w g e := .flip R
  let history := VectorCount.restrict N original ::
    A.preservedTwoHistoryCore B N
  have hAatBase : PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have habsentReusable : Not (List.Mem k0 A.reusableSwitches) := by
    apply A.not_mem_reusable_of_not_mem_exploration
    simpa [A] using habsentA
  have hhistory : forall x,
      x ∈ A.sharpConstructionHistory N \/
        x ∈ B.sharpConstructionHistory N -> x ∈ history := by
    intro x hx
    apply List.mem_cons_of_mem
    exact A.mem_preservedTwoHistoryCore B hx
  by_cases haction : List.Mem R.actionSwitch
      (B.constructionFirstWriterSwitches N)
  · unfold ManufacturedReflector.constructionFirstWriterSwitches at haction
    obtain ⟨t, ht, hwriter⟩ := List.mem_map.mp haction
    have hcore := A.preservedTwoHistoryCore_length_le_N_add_two_of_reserved
      hN B hbase hAatBase hpre hk0 habsentReusable habsentB
    have htail : forall tailTimes : List Nat,
        (forall k, k ∈ tailTimes ->
          (stepN w k (g, B.activatedState)).isSome) ->
        (tailTimes.map
          (restrictedTonguesAt w N (g, B.activatedState))).Nodup ->
        NoveltyCoverOn w N (g, B.activatedState) tailTimes history 1 := by
      intro tailTimes htailLive htailNodup
      exact R.protected_repair_one_novelty_over_history_of_action_writer
        hN B hAatBase hBpaths hpre history hhistory
          ht hwriter tailTimes htailLive htailNodup
    have hcap : history.length + 1 ≤ N + 4 := by
      dsimp [history]
      omega
    apply two_journeys_history_count_with_extra
      A B hbase hApaths hBpaths history hhistory hcap htail
        (VectorCount.restrict N original)
    · simp [history]
    · simpa [A] using hlive
    · simpa [A] using hnd
  · have hne : k0 ≠ R.actionSwitch := by
      intro heq
      apply habsentA
      rw [heq]
      change List.Mem R.actionSwitch
        ((R.runway ++ (R.mouth, R.firstArm) :: R.candy).map passageSwitch)
      rw [List.map_append]
      apply List.mem_append_right
      simp [ManufacturedFlipReflector.actionSwitch, passageSwitch]
    have hcore := A.preservedTwoHistoryCore_length_le_N_add_one_of_two_reserved
      hN B hbase hAatBase hpre hk0 (R.action_lt hN) hne
        habsentReusable habsentB R.action_not_mem_reusable haction
    have htail : forall tailTimes : List Nat,
        (forall k, k ∈ tailTimes ->
          (stepN w k (g, B.activatedState)).isSome) ->
        (tailTimes.map
          (restrictedTonguesAt w N (g, B.activatedState))).Nodup ->
        NoveltyCoverOn w N (g, B.activatedState) tailTimes history 2 := by
      intro tailTimes htailLive htailNodup
      exact A.protected_repair_two_novelty_over_history
        hN B hAatBase hBpaths hpre history hhistory
          tailTimes htailLive htailNodup
    have hcap : history.length + 2 ≤ N + 4 := by
      dsimp [history]
      omega
    apply two_journeys_history_count_with_extra
      A B hbase hApaths hBpaths history hhistory hcap htail
        (VectorCount.restrict N original)
    · simp [history]
    · simpa [A] using hlive
    · simpa [A] using hnd

end GeneralN
