import MellitDynamicResidual
import NoveltyChargeBound
import TwoHistoryUnionCharge
import BoundaryOverlapTailCount
import ProtectedRepairFour

/-!
# Five-novelty assembly from the verified dynamic residual

This file is deliberately a thin assembly layer.  It consumes the exact
dynamic-residual trichotomy from `MellitDynamicResidual` and the sharp
compatible-pair charge from `NoveltyChargeBound`; it does not repeat the
cycle extraction.

The two non-old-contact outcomes are closed:

* the reached-cycle outcome has all-horizon repeated-writer novelty at most
  two from the first reflector's base configuration;
* the compatible-pair outcome has all-horizon repeated-writer novelty at most
  four from its activated entry configuration (and the same four bound after
  any certified first-turnaround journey into the pair).

The direct `UnionOldTrackedShrink` trichotomy still has no recursive selector.
The final section avoids that residue: for two successive manufactured
reflectors it splits directly on preservation of the first support at the
second pre-return.  A preserved support gives the coefficient-one history
plus the four-state protected tail (`N+6`); a damaged support stops at its
first changing passage and gives the sharper charged-history bound (`N+5`).
Thus the exact two-reflector all-times assembly is unconditional and contains
no residual selector or old-contact recursion.

`GeneralN.StateLaw` remains open: a separate global reduction still has to
connect every arbitrary raw run, including early terminating branches, to
this exact two-reflector assembly.
-/

namespace GeneralN

/-! ## Compatible-pair charge -/

/-- A canonical compatible pair inherits the verified four-novelty theorem
after any certified first-turnaround journey into the pair state. -/
theorem UnionFreshCompatiblePair.first_turnaround_repeatedWriterNovelty_le_four
    {w : Wiring} {h g e N : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage}
    (C : UnionFreshCompatiblePair A fresh)
    (P : ManufacturedReflector w h g)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hPpaths :
      PathGrooves P.toSupported.paths P.activatedState)
    (hJourney : stepN w
      (P.exploration.length + P.runway.length + 1)
      (h, P.baseState) = some (g, C.result.state)) :
    forall H,
      (rawRepeatedWriterNovelTimes w N
        (h, P.baseState) H).length <= 4 := by
  exact
    first_turnaround_then_compatible_pair_repeatedWriterNovelty_le_four
      P A C.result.reflector C.result.state hN hPpaths
      C.oldPaths C.result.paths C.compatible.1 C.compatible.2 hJourney

/-- In particular, taking the newly manufactured reflector as the certified
turnaround gives an unconditional four-novelty bound from the old reflector's
activated entry configuration. -/
theorem UnionFreshCompatiblePair.activated_repeatedWriterNovelty_le_four
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage}
    (C : UnionFreshCompatiblePair A fresh)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N)) :
    forall H,
      (rawRepeatedWriterNovelTimes w N
        (e, A.activatedState) H).length <= 4 := by
  have hBpathsActivated :
      PathGrooves
        C.result.reflector.toSupported.paths
        C.result.reflector.activatedState := by
    simpa only [C.result.activated] using C.result.paths
  have hcanonical :=
    C.result.reflector.manufacturing_journey_reaches_activated
      hBpathsActivated
  have hreach :
      stepN w
        (C.result.reflector.exploration.length +
          C.result.reflector.runway.length + 1)
        (e, C.result.reflector.baseState) =
          some (g, C.result.state) := by
    rw [C.result.activated]
    exact hcanonical
  have hfour :=
    C.first_turnaround_repeatedWriterNovelty_le_four
      C.result.reflector hN hBpathsActivated hreach
  intro H
  have hbound := hfour H
  simpa only [C.result.base] using hbound

/-! ## Direct bounded non-old-contact assembly -/

/-- The verified dynamic trichotomy with both non-old-contact branches
discharged quantitatively.  The cycle bound is global from the first
reflector's base; the compatible bound is from its activated entry.  These
origins are stated explicitly and are not silently identified. -/
theorem ManufacturedReflector.union_first_contact_old_or_cycle_le_two_or_compatible_le_four
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage}
    {finish : Prod Nat Tongues}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hApaths :
      PathGrooves A.toSupported.paths A.activatedState)
    (htrace :
      PhysicalTrace w (e, A.activatedState) fresh finish)
    (hnonsimple :
      Not (SwitchSimple (A.exploration ++ fresh))) :
    Or
      (Nonempty (UnionOldTrackedShrink w N A fresh finish))
      (Or
        (forall H,
          (rawRepeatedWriterNovelTimes w N
            (g, A.baseState) H).length <= 2)
        (forall H,
          (rawRepeatedWriterNovelTimes w N
            (e, A.activatedState) H).length <= 4)) := by
  have outcome :=
    A.union_first_contact_shrinks_or_cycle_le_two_or_compatible
      hN hApaths htrace hnonsimple
  rcases outcome with hold | hcycle | hpair
  case inl =>
    exact Or.inl hold
  case inr.inl =>
    exact Or.inr (Or.inl hcycle)
  case inr.inr =>
    cases hpair with
    | intro C =>
        exact Or.inr
          (Or.inr (C.activated_repeatedWriterNovelty_le_four A hN))

/-- Five-budget facade for the endpoint target.  It is weaker than the exact
two/four theorem above, but makes explicit that every non-old-contact branch
is already below five. -/
theorem ManufacturedReflector.union_first_contact_old_or_nonold_le_five
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage}
    {finish : Prod Nat Tongues}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hApaths :
      PathGrooves A.toSupported.paths A.activatedState)
    (htrace :
      PhysicalTrace w (e, A.activatedState) fresh finish)
    (hnonsimple :
      Not (SwitchSimple (A.exploration ++ fresh))) :
    Or
      (Nonempty (UnionOldTrackedShrink w N A fresh finish))
      (Or
        (forall H,
          (rawRepeatedWriterNovelTimes w N
            (g, A.baseState) H).length <= 5)
        (forall H,
          (rawRepeatedWriterNovelTimes w N
            (e, A.activatedState) H).length <= 5)) := by
  have outcome :=
    A.union_first_contact_old_or_cycle_le_two_or_compatible_le_four
      hN hApaths htrace hnonsimple
  rcases outcome with hold | hcycle | hpair
  case inl =>
    exact Or.inl hold
  case inr.inl =>
    apply Or.inr
    apply Or.inl
    intro H
    have hbound := hcycle H
    omega
  case inr.inr =>
    apply Or.inr
    apply Or.inr
    intro H
    have hbound := hpair H
    omega

/- The endpoint-groove bridge and charged-history machinery now live in
`TwoHistoryUnionCharge`; keep this superseded local draft out of the
environment while rebasing the assembly onto those verified APIs.

/-! ## Endpoint groove preservation certifies quiet overlaps -/

/-- In a switch-simple physical trace, a local change made by the unique
passage through a writer survives to the endpoint. The prefix and suffix
cannot touch that writer, so both preserve its bit. -/
theorem PhysicalTrace.simple_changed_passage_survives
    {w : Wiring} {start finish : Nat × Tongues}
    {passages before after : List Passage}
    {p x : Nat} {u v : Tongues}
    (htrace : PhysicalTrace w start passages finish)
    (hsimple : SwitchSimple passages)
    (hsplit : passages = before ++ (p, x) :: after)
    (hprefix : PhysicalTrace w start before (p, u))
    (harrive : arrive u p = (x, v))
    (hchanged :
      v (passageSwitch (p, x)) ≠
        u (passageSwitch (p, x))) :
    finish.2 (passageSwitch (p, x)) ≠
      start.2 (passageSwitch (p, x)) := by
  have htrace' := htrace
  have hsimple' := hsimple
  rw [hsplit] at htrace' hsimple'
  obtain ⟨middle, hbefore, hrest⟩ := htrace'.split_append
  have hmiddle : middle = (p, u) := by
    have h₁ := hbefore.sound
    have h₂ := hprefix.sound
    rw [h₂] at h₁
    exact (Option.some.inj h₁).symm
  subst middle
  cases hrest with
  | @cons _ _ q _ v' _ _ harrive' _hlink hafter =>
      have hv' : v' = v := by
        rw [harrive] at harrive'
        exact (Prod.mk.inj harrive').2.symm
      subst v'
      have hparts : (before.map passageSwitch ++
          passageSwitch (p, x) :: after.map passageSwitch).Nodup := by
        simpa only [SwitchSimple, List.map_append,
          List.map_cons] using hsimple'
      have hsplitParts := List.nodup_append.mp hparts
      have hprefixForeign : ∀ prior ∈ before,
          passageSwitch prior ≠ passageSwitch (p, x) := by
        intro prior hprior hEq
        exact hsplitParts.2.2
          (passageSwitch prior)
          (List.mem_map.mpr ⟨prior, hprior, rfl⟩)
          (passageSwitch (p, x)) (by simp) hEq
      have hsuffixForeign : ∀ later ∈ after,
          passageSwitch later ≠ passageSwitch (p, x) := by
        have hheadTail := hsplitParts.2.1
        rw [List.nodup_cons] at hheadTail
        intro later hlater hEq
        apply hheadTail.1
        exact List.mem_map.mpr ⟨later, hlater, hEq⟩
      have hu :
          u (passageSwitch (p, x)) =
            start.2 (passageSwitch (p, x)) :=
        hprefix.preserves _ hprefixForeign
      have hv :
          finish.2 (passageSwitch (p, x)) =
            v (passageSwitch (p, x)) :=
        hafter.preserves _ hsuffixForeign
      intro hendpoint
      apply hchanged
      calc
        v (passageSwitch (p, x)) =
            finish.2 (passageSwitch (p, x)) := hv.symm
        _ = start.2 (passageSwitch (p, x)) := hendpoint
        _ = u (passageSwitch (p, x)) := hu.symm
/-- If an arrival does not change its writer bit, it does not change the
tongue vector at all. -/
theorem arrive_state_eq_of_writer_eq
    {u v : Tongues} {p x : Nat}
    (harrive : arrive u p = (x, v))
    (hbit : v (p / 3) = u (p / 3)) :
    v = u := by
  unfold arrive at harrive
  by_cases hp : p % 3 = 0
  · rw [if_pos hp] at harrive
    exact (congrArg Prod.snd harrive).symm
  · rw [if_neg hp] at harrive
    have hv : v = pin u p :=
      (congrArg Prod.snd harrive).symm
    rw [hv] at hbit ⊢
    apply pin_of_agrees
    simpa [pin] using hbit.symm

/-- If the old reusable grooves hold both before and after the second
switch-simple exploration, every passage of that exploration whose writer is
in the old reusable support is completely unproductive. A local change would
survive by simple_changed_passage_survives, while the same old groove at both
endpoints fixes that writer bit. -/
theorem ManufacturedReflector.exploration_reusable_passage_unproductive
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState)
    (hpreReturnGrooves :
      PathGrooves A.toSupported.paths B.preReturn.2)
    {before after : List Passage}
    {p x : Nat} {u v : Tongues}
    (hsplit :
      B.exploration = before ++ (p, x) :: after)
    (hprefix :
      PhysicalTrace w (e, B.baseState) before (p, u))
    (harrive : arrive u p = (x, v))
    (hreusable :
      passageSwitch (p, x) ∈ A.reusableSwitches) :
    v = u := by
  have hbit :
      v (passageSwitch (p, x)) =
        u (passageSwitch (p, x)) := by
    apply Classical.byContradiction
    intro hchanged
    have hsurvives :=
      B.exploration_trace.simple_changed_passage_survives
        B.exploration_simple hsplit hprefix harrive hchanged
    obtain ⟨path, hpath, old, hold, holdSwitch⟩ :=
      A.mem_reusableSwitches hreusable
    have hfixed := same_groove_same_tongue
      (hbaseGrooves path hpath old hold)
      (hpreReturnGrooves path hpath old hold)
    apply hsurvives
    rw [← holdSwitch]
    exact hfixed.symm
  apply arrive_state_eq_of_writer_eq harrive
  simpa [passageSwitch] using hbit
-/

/-- A finite physical trace can be compressed to its initial vector plus one
vector for each passage satisfying a supplied charge predicate, provided every
actual state change is charged. This theorem counts complete tongue vectors;
it does not appeal to a finite-N state-space argument. -/
theorem PhysicalTrace.exists_charged_history
    {w : Wiring} {N : Nat}
    {start finish : Nat × Tongues}
    {passages : List Passage}
    (charge : Passage → Bool)
    (htrace : PhysicalTrace w start passages finish)
    (hcharged : ∀ before p x after u v,
      passages = before ++ (p, x) :: after →
      PhysicalTrace w start before (p, u) →
      arrive u p = (x, v) →
      v ≠ u →
      charge (p, x) = true) :
    ∃ history : List (List Bool),
      history.length ≤ (passages.filter charge).length + 1 ∧
      ∀ d, d ≤ passages.length →
        restrictedTonguesAt w N start d ∈ history := by
  induction htrace with
  | nil config =>
      refine ⟨[VectorCount.restrict N config.2], by simp, ?_⟩
      intro d hd
      have hd0 : d = 0 := by simp at hd; exact hd
      subst d
      simp [restrictedTonguesAt, tonguesAt, stepN]
  | @cons p x q u v rest finish harrive hlink tail ih =>
      have hone : stepN w 1 (p, u) = some (q, v) := by
        simp [stepN, step, harrive, hlink]
      have hchargedTail : ∀ before p₂ x₂ after u₂ v₂,
          rest = before ++ (p₂, x₂) :: after →
          PhysicalTrace w (q, v) before (p₂, u₂) →
          arrive u₂ p₂ = (x₂, v₂) →
          v₂ ≠ u₂ →
          charge (p₂, x₂) = true := by
        intro before p₂ x₂ after u₂ v₂ hsplit hprefix
          hlocal hne
        apply hcharged ((p, x) :: before) p₂ x₂ after u₂ v₂
        · simp [hsplit]
        · exact PhysicalTrace.cons harrive hlink hprefix
        · exact hlocal
        · exact hne
      obtain ⟨history, hlength, hmem⟩ := ih hchargedTail
      have hshift : ∀ d, d ≤ rest.length →
          restrictedTonguesAt w N (p, u) (d + 1) =
            restrictedTonguesAt w N (q, v) d := by
        intro d hd
        have hlive := stepN_prefix_some hd tail.sound
        have htongues := tonguesAt_add_of_reaches hone hlive
        unfold restrictedTonguesAt
        have hsum : d + 1 = 1 + d := by omega
        rw [hsum]
        exact congrArg (VectorCount.restrict N) htongues
      by_cases huv : v = u
      · refine ⟨history, ?_, ?_⟩
        · cases hc : charge (p, x) <;> simp [hc] <;> omega
        · intro d hd
          cases d with
          | zero =>
              have hzero := hmem 0 (Nat.zero_le _)
              simpa [restrictedTonguesAt, tonguesAt, stepN, huv] using hzero
          | succ d =>
              have hdRest : d ≤ rest.length := by
                simpa using hd
              have hm := hmem d hdRest
              have hs := hshift d hdRest
              simpa [Nat.succ_eq_add_one, hs] using hm
      · have hheadCharged : charge (p, x) = true := by
          apply hcharged [] p x rest u v
          · rfl
          · exact PhysicalTrace.nil _
          · exact harrive
          · exact huv
        refine ⟨VectorCount.restrict N u :: history, ?_, ?_⟩
        · simp [hheadCharged]
          omega
        · intro d hd
          cases d with
          | zero =>
              simp [restrictedTonguesAt, tonguesAt, stepN]
          | succ d =>
              apply List.mem_cons_of_mem
              have hdRest : d ≤ rest.length := by
                simpa using hd
              have hm := hmem d hdRest
              have hs := hshift d hdRest
              simpa [Nat.succ_eq_add_one, hs] using hm

/-! ## Coefficient-one charge up to the first support contact -/

/-- The exact local vector history along the support-fresh approach of the
second construction, including both endpoints. -/
noncomputable def SecondHistorySupportContact.approachHistory
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B) (N : Nat) :
    List (List Bool) :=
  (List.range (C.approach.length + 1)).map
    (restrictedTonguesAt w N (e, B.baseState))

/-- The first support contact is the correct truncation point.  The reusable
switches of `A` and the entire strict approach prefix of `B` are disjoint,
so they consume at most the `N` physical switches once. -/
theorem SecondHistorySupportContact.reusable_add_approach_le_N
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N)) :
    A.reusableSwitches.length + C.approach.length <= N := by
  let switches :=
    A.reusableSwitches ++ C.approach.map passageSwitch
  have hApproachSimple : SwitchSimple C.approach := by
    have hsimple := B.exploration_simple
    unfold SwitchSimple at hsimple
    unfold SwitchSimple
    rw [C.split] at hsimple
    simp only [List.map_append, List.map_cons] at hsimple
    exact (List.nodup_append.mp hsimple).1
  have hnd : switches.Nodup := by
    apply List.nodup_append.mpr
    refine And.intro A.reusableSwitches_nodup
      (And.intro hApproachSimple ?_)
    intro oldSwitch hOld freshSwitch hFresh hEq
    rcases A.mem_reusableSwitches hOld with
      ⟨path, hPath, old, hOldPath, hOldSwitchEq⟩
    rcases List.mem_map.mp hFresh with
      ⟨prior, hPrior, hPriorSwitchEq⟩
    apply C.approach_fresh prior hPrior
    exact Exists.intro path
      (And.intro hPath
        (Exists.intro old
          (And.intro hOldPath
            (hOldSwitchEq.trans
              (hEq.trans hPriorSwitchEq.symm)))))
  have hlt : forall k, List.Mem k switches -> k < N := by
    intro k hk
    rcases List.mem_append.mp hk with hA | hApproach
    case inl =>
      exact A.reusableSwitch_lt hN hA
    case inr =>
      rcases List.mem_map.mp hApproach with
        ⟨passage, hPassage, rfl⟩
      exact C.approach_trace.switch_lt hN passage hPassage
  have hbound := nodup_nat_lt_length hnd hlt
  simpa only [switches, List.length_append,
    List.length_map] using hbound

/-- Erase the guaranteed internal duplicate of `A` and the shared activation
boundary of the approach.  This is the coefficient-one history object. -/
noncomputable def SecondHistorySupportContact.firstContactHistoryCore
    {w : Wiring} {g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B) (N : Nat) :
    List (List Bool) :=
  A.sharpHistoryCore N ++
    (C.approachHistory N).erase
      (VectorCount.restrict N A.activatedState)

/-- The approach starts at the first reflector's activated vector. -/
theorem SecondHistorySupportContact.activated_mem_approachHistory
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState) :
    List.Mem (VectorCount.restrict N A.activatedState)
      (C.approachHistory N) := by
  unfold SecondHistorySupportContact.approachHistory
  apply List.mem_map.mpr
  refine Exists.intro 0 (And.intro (List.mem_range.mpr (by omega)) ?_)
  simp [restrictedTonguesAt, tonguesAt, stepN, hbase]

/-- The first construction and the exact first-contact approach together
have a cover of size at most `N+2`, not `2*N+O(1)`. -/
theorem SecondHistorySupportContact.firstContactHistoryCore_length_le_N_add_two
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hbase : B.baseState = A.activatedState) :
    (C.firstContactHistoryCore N).length <= N + 2 := by
  have hboundary := C.activated_mem_approachHistory
    (N := N) hbase
  have hsupport := C.reusable_add_approach_le_N hN
  have houter := A.exploration_length_le_reusable_add_one
  unfold SecondHistorySupportContact.firstContactHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length]
  simp only [SecondHistorySupportContact.approachHistory,
    List.length_map, List.length_range]
  omega

/-- Every vector represented by the first sharp history or by the truncated
second approach survives in the coefficient-one core. -/
theorem SecondHistorySupportContact.mem_firstContactHistoryCore
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    {x : List Bool}
    (hx : Or
      (List.Mem x (A.sharpConstructionHistory N))
      (List.Mem x (C.approachHistory N))) :
    List.Mem x (C.firstContactHistoryCore N) := by
  rcases hx with hA | hApproach
  case inl =>
    apply List.mem_append_left
    exact A.mem_sharpHistoryCore_of_mem hA
  case inr =>
    by_cases hBoundary :
        x = VectorCount.restrict N A.activatedState
    case pos =>
      rw [hBoundary]
      apply List.mem_append_left
      exact A.activated_mem_sharpHistoryCore
    case neg =>
      apply List.mem_append_right
      exact (List.mem_erase_of_ne hBoundary).mpr hApproach

/-- Pointwise raw coverage through the exact contact configuration.  The
first construction is covered by `A`'s sharp history; after its activated
boundary, only the support-fresh approach is added. -/
theorem SecondHistorySupportContact.prefix_mem_firstContactHistoryCore
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    {k : Nat}
    (hk : k <= A.exploration.length + A.runway.length + 1 +
      C.approach.length) :
    List.Mem
      (restrictedTonguesAt w N (g, A.baseState) k)
      (C.firstContactHistoryCore N) := by
  let travel := A.exploration.length + A.runway.length + 1
  have hreachA := A.manufacturing_journey_reaches_activated hApaths
  have hreachBase :
      stepN w travel (g, A.baseState) = some (e, B.baseState) := by
    dsimp [travel]
    rw [hbase]
    exact hreachA
  by_cases hFirst : k <= travel
  case pos =>
    apply List.mem_append_left
    apply A.mem_sharpHistoryCore_of_mem
    exact A.manufacturing_journey_mem_sharpHistory
      hApaths (by simpa [travel] using hFirst)
  case neg =>
    let d := k - travel
    have hkEq : k = travel + d := by
      dsimp [d]
      omega
    have hdLe : d <= C.approach.length := by
      dsimp [d, travel]
      omega
    have hlocalLive :=
      stepN_prefix_some hdLe C.approach_trace.sound
    have hshift :=
      tonguesAt_add_of_reaches hreachBase hlocalLive
    have hvector :
        restrictedTonguesAt w N (g, A.baseState) k =
          restrictedTonguesAt w N (e, B.baseState) d := by
      unfold restrictedTonguesAt
      rw [hkEq]
      exact congrArg (VectorCount.restrict N) hshift
    have hlocal : List.Mem
        (restrictedTonguesAt w N (e, B.baseState) d)
        (C.approachHistory N) := by
      unfold SecondHistorySupportContact.approachHistory
      apply List.mem_map.mpr
      exact Exists.intro d
        (And.intro (List.mem_range.mpr (by omega)) rfl)
    rw [hvector]
    exact C.mem_firstContactHistoryCore (Or.inr hlocal)

/-- Raw coefficient-one prefix theorem.  Any duplicate-free sample of tongue
vectors ending no later than the first old-support contact has size at most
`N+2`.  No completed second reflector is charged. -/
theorem SecondHistorySupportContact.prefix_distinct_le_N_add_two
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (times : List Nat)
    (htimes : forall k, List.Mem k times ->
      k <= A.exploration.length + A.runway.length + 1 +
        C.approach.length)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + 2 := by
  let history := C.firstContactHistoryCore N
  have hcover : NoveltyCoverOn w N (g, A.baseState)
      times history 0 := by
    refine Exists.intro [] (And.intro (by simp) ?_)
    intro k hk
    simp only [List.append_nil]
    exact C.prefix_mem_firstContactHistoryCore hbase hApaths
      (htimes k hk)
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hlength :=
    C.firstContactHistoryCore_length_le_N_add_two hN hbase
  dsimp [history] at hcount
  omega

/-- Boundary-overlap assembly at the truncated contact.  Once the post-contact
run itself has a direct cap `cap`, the whole trajectory has size at most
`N+cap+1`: the contact vector is already in the `N+2` prefix history and is
not paid twice.  Thus a genuine five-vector tail would give `N+6` directly.
This theorem does not assume that such a tail certificate exists. -/
theorem SecondHistorySupportContact.prefix_then_tail_distinct_le_N_add_cap_add_one
    {w : Wiring} {N g e cap : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (htail : forall tailTimes : List Nat,
      (forall k, List.Mem k tailTimes ->
        (stepN w k (C.fresh.1, C.contactState)).isSome) ->
      (tailTimes.map (restrictedTonguesAt w N
        (C.fresh.1, C.contactState))).Nodup ->
      tailTimes.length <= cap)
    (hcap : 0 < cap)
    (times : List Nat)
    (hlive : forall k, List.Mem k times ->
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length <= N + cap + 1 := by
  let travel := A.exploration.length + A.runway.length + 1
  let lead := travel + C.approach.length
  let history := C.firstContactHistoryCore N
  have hreachA := A.manufacturing_journey_reaches_activated hApaths
  have hreachBase :
      stepN w travel (g, A.baseState) = some (e, B.baseState) := by
    dsimp [travel]
    rw [hbase]
    exact hreachA
  have hreach :
      stepN w lead (g, A.baseState) =
        some (C.fresh.1, C.contactState) := by
    dsimp [lead]
    rw [stepN_add, hreachBase]
    exact C.approach_trace.sound
  have hprefix : forall d, d <= lead -> List.Mem
      (restrictedTonguesAt w N (g, A.baseState) d) history := by
    intro d hd
    dsimp [history]
    apply C.prefix_mem_firstContactHistoryCore hbase hApaths
    simpa [lead, travel] using hd
  have hboundary :
      List.Mem (VectorCount.restrict N C.contactState) history := by
    have hm := hprefix lead (Nat.le_refl lead)
    have hvector :
        restrictedTonguesAt w N (g, A.baseState) lead =
          VectorCount.restrict N C.contactState := by
      simp [restrictedTonguesAt, tonguesAt, hreach]
    rwa [hvector] at hm
  have hcount := boundary_history_then_direct_tail_distinct_le
    hreach history hprefix hboundary htail hcap times hlive hnd
  have hlength :=
    C.firstContactHistoryCore_length_le_N_add_two hN hbase
  dsimp [history] at hcount
  omega

/-- Unconditional first-contact accounting dichotomy.  Either every selected
vector from both completed sharp histories already fits in `N+2`, or an exact
first support contact exists and every selected vector up to that truncation
fits in `N+2`.  The second branch never charges the untraversed suffix of `B`.
-/
theorem ManufacturedReflector.two_history_nodup_union_or_charged_first_contact
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (pool : List (List Bool))
    (hpool : forall x, List.Mem x pool -> Or
      (List.Mem x (A.sharpConstructionHistory N))
      (List.Mem x (B.sharpConstructionHistory N)))
    (hnd : pool.Nodup) :
    Or (pool.length <= N + 2)
      (Exists fun C : SecondHistorySupportContact w A B =>
        forall times : List Nat,
          (forall k, List.Mem k times ->
            k <= A.exploration.length + A.runway.length + 1 +
              C.approach.length) ->
          (times.map (restrictedTonguesAt w N
            (g, A.baseState))).Nodup ->
          times.length <= N + 2) := by
  have hout :=
    A.two_history_nodup_union_bound_or_first_contact
      hN B hbase hApaths pool hpool hnd
  rcases hout with hbound | hcontact
  case inl =>
    exact Or.inl hbound
  case inr =>
    rcases hcontact with ⟨C⟩
    apply Or.inr
    exact Exists.intro C (fun times htimes htimesNodup =>
      C.prefix_distinct_le_N_add_two
        hN hbase hApaths times htimes htimesNodup)

/-! ## One-shot amortization inside the dynamic old-contact branch -/

/-- The selected fresh prefix and the complete old exploration are one
switch-simple list.  Their ranks therefore fit in the ambient `N` exactly.
This is the local amortized charge available before choosing a residual. -/
theorem UnionOldTrackedShrink.outer_rank_add_prefix_le_N
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage}
    {finish : Prod Nat Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N)) :
    C.raw.shrink.outer.supportContactRank +
      C.selection.before.length <= N := by
  have hnd :
      (A.exploration.map passageSwitch ++
        C.selection.before.map passageSwitch).Nodup := by
    simpa only [SwitchSimple, List.map_append] using
      C.selection.combinedSimple
  have hlt : forall k,
      List.Mem k
        (A.exploration.map passageSwitch ++
          C.selection.before.map passageSwitch) -> k < N := by
    intro k hk
    rcases List.mem_append.mp hk with hA | hPrefix
    case inl =>
      rcases List.mem_map.mp hA with
        ⟨passage, hPassage, rfl⟩
      exact A.exploration_trace.switch_lt hN passage hPassage
    case inr =>
      rcases List.mem_map.mp hPrefix with
        ⟨passage, hPassage, rfl⟩
      exact C.raw.beforeTrace.switch_lt hN passage hPassage
  have hbound := nodup_nat_lt_length hnd hlt
  unfold TrackedEndpointCurve.supportContactRank
  rw [C.raw.shrink.outer_switches]
  simpa only [List.length_append, List.length_map] using hbound

/-- Combining the local switch charge with the exact old-support split shows
that the fresh prefix and both strict residual ranks are paid once at this
contact.  What is still missing is an inherited global-history statement
preventing a later recursive prefix from revisiting an ancestor's discarded
support and being charged again. -/
theorem UnionOldTrackedShrink.prefix_add_both_residual_ranks_le_N
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage}
    {finish : Prod Nat Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish)
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N)) :
    C.selection.before.length +
        C.raw.shrink.left.supportContactRank + 1 +
          C.raw.shrink.right.supportContactRank <= N := by
  have hlocal := C.outer_rank_add_prefix_le_N hN
  have hsplit := C.raw.shrink.exact_support_split
  omega
/-! ## The exact runway/post-runway contact split -/

/-- The part of the first outward exploration after its runway.  It begins
at the lobe mouth and contains the stay arm or the flip candy. -/
def ManufacturedReflector.postRunwayExploration
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : List Passage :=
  match A with
  | .stay R => [(R.mouth, R.arm)]
  | .flip R => (R.mouth, R.firstArm) :: R.candy
/-- The unique passage at the mouth position of the original simple
exploration. -/
def ManufacturedReflector.mouthExplorationPassage
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : Passage :=
  match A with
  | .stay R => (R.mouth, R.arm)
  | .flip R => (R.mouth, R.firstArm)

/-- The strict post-mouth suffix.  This is empty for a stay reflector and is
the candy path for a flip reflector. -/
def ManufacturedReflector.afterMouthExploration
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) : List Passage :=
  match A with
  | .stay _ => []
  | .flip R => R.candy

theorem ManufacturedReflector.postRunway_eq_mouth_cons_afterMouth
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.postRunwayExploration =
      A.mouthExplorationPassage :: A.afterMouthExploration := by
  cases A <;> rfl

theorem ManufacturedReflector.exploration_eq_runway_append_postRunway
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    A.exploration = A.runway ++ A.postRunwayExploration := by
  cases A <;> rfl

/-- The runway and post-runway pieces have disjoint switch support. -/
theorem ManufacturedReflector.runway_postRunway_switch_disjoint
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e) :
    forall left, List.Mem left A.runway ->
      forall right, List.Mem right A.postRunwayExploration ->
        Not (passageSwitch left = passageSwitch right) := by
  intro left hleft right hright
  have hsimple := A.exploration_simple
  unfold SwitchSimple at hsimple
  rw [A.exploration_eq_runway_append_postRunway,
    List.map_append] at hsimple
  have hcross := (List.nodup_append.mp hsimple).2.2
  exact hcross
    (passageSwitch left)
    (List.mem_map.mpr
      (Exists.intro left (And.intro hleft rfl)))
    (passageSwitch right)
    (List.mem_map.mpr
      (Exists.intro right (And.intro hright rfl)))

/-- The suggested literal `runway ++ exploration` cannot be the previous
switch-simple path unless the runway is empty: `exploration` already contains
that runway. -/
theorem ManufacturedReflector.runway_append_exploration_not_simple
    {w : Wiring} {g e : Nat}
    (A : ManufacturedReflector w g e)
    (hne : Not (A.runway = [])) :
    Not (SwitchSimple (A.runway ++ A.exploration)) := by
  intro hsimple
  cases hrunway : A.runway with
  | nil =>
      exact hne hrunway
  | cons passage rest =>
      have hp : List.Mem passage A.runway := by
        rw [hrunway]
        exact List.mem_cons_self
      have hleft :
          List.Mem (passageSwitch passage)
            (A.runway.map passageSwitch) :=
        List.mem_map.mpr
          (Exists.intro passage (And.intro hp rfl))
      have hright :
          List.Mem (passageSwitch passage)
            (A.exploration.map passageSwitch) :=
        A.support_switch_mem_exploration
          A.runway_mem_support hp
      unfold SwitchSimple at hsimple
      rw [List.map_append] at hsimple
      have hcross := (List.nodup_append.mp hsimple).2.2
      exact
        (hcross (passageSwitch passage) hleft
          (passageSwitch passage) hright) rfl

/-- Every old contact lies in the pre-mouth runway or at/after the mouth.
Thus the proposed two-way index slogan is actually `j < i` versus
`j >= i`; equality is the mouth passage itself.  This does not infer
contact direction. -/
theorem UnionOldTrackedShrink.hit_runway_or_postRunway
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage}
    {finish : Prod Nat Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    Or
      (List.Mem C.raw.split.hit A.runway)
      (List.Mem C.raw.split.hit A.postRunwayExploration) := by
  let hit : Passage := C.raw.split.hit
  have hmem : List.Mem hit A.exploration := by
    rw [C.raw.split.split]
    exact List.mem_append_right
      C.raw.split.beforeHit List.mem_cons_self
  rw [A.exploration_eq_runway_append_postRunway] at hmem
  change Or
    (List.Mem hit A.runway)
    (List.Mem hit A.postRunwayExploration)
  exact List.mem_append.mp hmem
/-- Fully expanded occurrence classification: before the mouth, exactly at
the mouth, or strictly after the mouth.  Because the original exploration is
switch-simple, these are the unique three possible old occurrences. -/
theorem UnionOldTrackedShrink.hit_runway_or_mouth_or_afterMouth
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {fresh : List Passage}
    {finish : Prod Nat Tongues}
    (C : UnionOldTrackedShrink w N A fresh finish) :
    Or
      (List.Mem C.raw.split.hit A.runway)
      (Or
        (C.raw.split.hit = A.mouthExplorationPassage)
        (List.Mem C.raw.split.hit A.afterMouthExploration)) := by
  cases C.hit_runway_or_postRunway with
  | inl hrunway =>
      exact Or.inl hrunway
  | inr hpost =>
      let hit : Passage := C.raw.split.hit
      have hpostLocal :
          List.Mem hit A.postRunwayExploration := by
        simpa only [hit] using hpost
      rw [A.postRunway_eq_mouth_cons_afterMouth] at hpostLocal
      cases List.mem_cons.mp hpostLocal with
      | inl hmouth =>
          apply Or.inr
          apply Or.inl
          change hit = A.mouthExplorationPassage
          exact hmouth
      | inr hafter =>
          apply Or.inr
          apply Or.inr
          change List.Mem hit A.afterMouthExploration
          exact hafter

/-- Final direct classification after incorporating the sequence insight.
The generic old-contact case is split into its runway and post-runway
locations.  The other two outcomes are already bounded.  Closing either old
location requires additional dynamic information: backward orientation for
the runway dogbone, or a theorem excluding the post-runway interlacement. -/
theorem ManufacturedReflector.union_first_contact_runway_or_postRunway_or_bounded
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    {fresh : List Passage}
    {finish : Prod Nat Tongues}
    (hN : forall p q, w.link p = some q ->
      And (p < 3 * N) (q < 3 * N))
    (hApaths :
      PathGrooves A.toSupported.paths A.activatedState)
    (htrace :
      PhysicalTrace w (e, A.activatedState) fresh finish)
    (hnonsimple :
      Not (SwitchSimple (A.exploration ++ fresh))) :
    Or
      (exists C : UnionOldTrackedShrink w N A fresh finish,
        List.Mem C.raw.split.hit A.runway)
      (Or
        (exists C : UnionOldTrackedShrink w N A fresh finish,
          List.Mem C.raw.split.hit A.postRunwayExploration)
        (Or
          (forall H,
            (rawRepeatedWriterNovelTimes w N
              (g, A.baseState) H).length <= 2)
          (forall H,
            (rawRepeatedWriterNovelTimes w N
              (e, A.activatedState) H).length <= 4))) := by
  have outcome :=
    A.union_first_contact_old_or_cycle_le_two_or_compatible_le_four
      hN hApaths htrace hnonsimple
  rcases outcome with hold | hcycle | hpair
  case inl =>
    cases hold with
    | intro C =>
        cases C.hit_runway_or_postRunway with
        | inl hrunway =>
            exact Or.inl (Exists.intro C hrunway)
        | inr hpost =>
            exact Or.inr
              (Or.inl (Exists.intro C hpost))
  case inr.inl =>
    exact Or.inr (Or.inr (Or.inl hcycle))
  case inr.inr =>
    exact Or.inr (Or.inr (Or.inr hpair))

/-! ## Nonrecursive damaging-contact assembly -/

/-- Rebase the verified two-novelty theorem at a changing old-support contact
across the first manufactured journey.  The charged contact history already
contains every vector of that first journey, so no additional novelty is paid
before the second exploration. -/
theorem SecondHistoryContactData.global_changed_contact_two_novelty
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    {next : Tongues}
    (harrive :
      arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged : next (C.fresh.1 / 3) ≠
      C.contactState (C.fresh.1 / 3))
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome) :
    NoveltyCoverOn w N (g, A.baseState) times
      (C.damageContactHistory N next) 2 := by
  let travel := A.exploration.length + A.runway.length + 1
  let localTimes := times.map (fun k => k - travel)
  have hreachA := A.manufacturing_journey_reaches_activated hApaths
  have hreachBase :
      stepN w travel (g, A.baseState) = some (e, B.baseState) := by
    dsimp [travel]
    rw [hbase]
    exact hreachA
  obtain ⟨fresh, hfresh, hlocal⟩ :=
    C.changed_contact_two_novelty_charged
      (N := N) harrive hchanged localTimes
  refine ⟨fresh, hfresh, ?_⟩
  intro k hk
  by_cases hkTravel : k < travel
  · apply List.mem_append_left
    unfold SecondHistoryContactData.damageContactHistory
    apply List.mem_append_left
    apply A.mem_sharpHistoryCore_of_mem
    exact A.manufacturing_journey_mem_sharpHistory
      hApaths (by omega)
  · let d := k - travel
    have hkEq : k = travel + d := by
      dsimp [d]
      omega
    have hdMem : d ∈ localTimes := by
      dsimp [localTimes]
      apply List.mem_map.mpr
      exact ⟨k, hk, rfl⟩
    have hlocalLive :
        ∃ finish, stepN w d (e, B.baseState) = some finish := by
      have hglobalLive :
          ∃ finish, stepN w k (g, A.baseState) = some finish := by
        cases hstep : stepN w k (g, A.baseState) with
        | none =>
            have hkLive := hlive k hk
            simp [hstep] at hkLive
        | some finish =>
            exact ⟨finish, rfl⟩
      obtain ⟨finish, hfinish⟩ := hglobalLive
      refine ⟨finish, ?_⟩
      have hfinish' := hfinish
      rw [hkEq, stepN_add, hreachBase] at hfinish'
      simpa using hfinish'
    have hshift := tonguesAt_add_of_reaches hreachBase hlocalLive
    have hvector :
        restrictedTonguesAt w N (g, A.baseState) k =
          restrictedTonguesAt w N (e, B.baseState) d := by
      unfold restrictedTonguesAt
      rw [hkEq]
      exact congrArg (VectorCount.restrict N) hshift
    rw [hvector]
    exact hlocal d hdMem

/-- A changing old-support contact closes the complete raw trajectory with
the sharper `N+5` bound.  The coefficient-one history costs at most `N+3`
and the contact tail contributes at most two genuinely new vectors. -/
theorem SecondHistoryContactData.changed_contact_all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistoryContactData w A B)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    {next : Tongues}
    (harrive :
      arrive C.contactState C.fresh.1 = (C.fresh.2, next))
    (hchanged : next (C.fresh.1 / 3) ≠
      C.contactState (C.fresh.1 / 3))
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have hcover := C.global_changed_contact_two_novelty
    (N := N) hbase hApaths harrive hchanged times hlive
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory := C.damageContactHistory_length_le_N_add_three
    hN hbase hbaseGrooves next
  omega

/-- If the first support is damaged during the second simple exploration,
its earliest damaging passage supplies `SecondHistoryContactData`; harmless
earlier old-support overlaps are retained and charged only when productive.
No old-contact recursion remains. -/
theorem ManufacturedReflector.preReturn_broken_all_run_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hbroken : ¬ PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  have hbaseGrooves :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  obtain ⟨approach, p, x, suffix, u, v, path, old,
      hsplit, happroach, hgrooves, harrive,
      hpath, hold, hswitch, hchanged, _hexit⟩ :=
    B.exploration_trace.first_changed_support_passage
      hbaseGrooves hbroken
  have hfull := B.exploration_trace
  rw [hsplit] at hfull
  obtain ⟨middle, hbefore, hrest⟩ := hfull.split_append
  have hmiddle : middle = (p, u) := by
    have hactual := hbefore.sound
    have hgiven := happroach.sound
    rw [hgiven] at hactual
    exact (Option.some.inj hactual).symm
  subst middle
  let C : SecondHistoryContactData w A B := {
    approach := approach
    fresh := (p, x)
    suffix := suffix
    contactState := u
    split := hsplit
    approach_trace := happroach
    suffix_trace := hrest
    old_grooves := hgrooves
    touches := ⟨path, hpath, old, hold, by
      simpa [passageSwitch] using hswitch⟩
  }
  exact C.changed_contact_all_run_distinct_le_N_add_five
    hN hbase hApaths
      (by simpa [C] using harrive)
      (by simpa [C] using hchanged)
      times hlive hnd

/-- Stable endpoint branch in raw all-times form.  The verified
coefficient-one two-construction history is followed by the unconditional
four-vector protected-repair tail, sharing its initial corner. -/
theorem ManufacturedReflector.preReturn_grooved_all_run_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (hpre : PathGrooves A.toSupported.paths B.preReturn.2)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 6 := by
  have hreachA := A.manufacturing_journey_reaches_activated hApaths
  have hreachB := B.manufacturing_journey_reaches_activated hBpaths
  have hreachB' :
      stepN w (B.exploration.length + B.runway.length + 1)
        (e, A.activatedState) = some (g, B.activatedState) := by
    rw [← hbase]
    exact hreachB
  have hAatBase :
      PathGrooves A.toSupported.paths B.baseState := by
    rw [hbase]
    exact hApaths
  have htail : ∀ tailTimes : List Nat,
      (∀ k ∈ tailTimes,
        (stepN w k (g, B.activatedState)).isSome) →
      (tailTimes.map
        (restrictedTonguesAt w N (g, B.activatedState))).Nodup →
      tailTimes.length ≤ 4 := by
    intro tailTimes htailLive htailNodup
    exact manufactured_pair_protected_repair_distinct_le_four
      A B hAatBase hBpaths tailTimes htailLive htailNodup
  exact
    two_manufacturing_journeys_preserved_support_then_four_tail_le_N_add_six
      hN A B A.activatedState B.activatedState
      rfl rfl hreachA hApaths hbase rfl hreachB' hBpaths
      hpre htail times hlive hnd

/-- **Unconditional two-reflector all-times assembly.**  Either the old
support survives to the second pre-return and the protected four-corner tail
applies, or its first damaging passage yields the sharper `N+5` branch.
There is no residual selector and no recursive old-contact hypothesis. -/
theorem ManufacturedReflector.two_journeys_all_run_distinct_le_N_add_six
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = A.activatedState)
    (hApaths : PathGrooves A.toSupported.paths A.activatedState)
    (hBpaths : PathGrooves B.toSupported.paths B.activatedState)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, A.baseState)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, A.baseState))).Nodup) :
    times.length ≤ N + 6 := by
  by_cases hpre : PathGrooves A.toSupported.paths B.preReturn.2
  · exact A.preReturn_grooved_all_run_distinct_le_N_add_six
      hN B hbase hApaths hBpaths hpre times hlive hnd
  · have hcount := A.preReturn_broken_all_run_distinct_le_N_add_five
      hN B hbase hApaths hpre times hlive hnd
    omega

end GeneralN
