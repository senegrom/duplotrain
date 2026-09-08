import SharpCertificateClosure

/-!
# Retaining and closing the simple-cycle self-link branch

A cycle branch settles at its first arrival. Its positive-time constant-vector
contract is all downstream counting needs; the other branch retains the
manufactured reflector and its construction history.
-/

namespace GeneralN

/-- A same-exit revisit installs a grooved loop at its very first arrival. -/
theorem PhysicalTrace.simple_same_exit_cycle_all_time
    {w : Wiring} {p x q : Nat} {u₀ u v : Tongues} {rest : List Passage}
    (htrace : PhysicalTrace w (p, u₀) ((p, x) :: rest) (q, u))
    (hsimple : SwitchSimple ((p, x) :: rest))
    (hnext : arrive u q = (x, v)) :
    ∀ d, 0 < d → ∃ port, stepN w d (q, u) = some (port, v) := by
  have hold := htrace.grooved_of_switchSimple hsimple
  have hhead := hold (p, x) List.mem_cons_self
  have hpx := arrive_exit_switch u x
  have hqx := arrive_exit_switch u q
  rw [hhead] at hpx
  rw [hnext] at hqx
  have hrest : PassagesGrooved v rest := by
    apply PassagesGrooved.transfer
      (fun passage hp => hold passage (List.mem_cons_of_mem _ hp))
    intro passage hp
    apply arrive_preserves_other hnext
    grind [SwitchSimple, passageSwitch]
  have hg : PassagesGrooved v ((q, x) :: rest) := by
    intro passage hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simpa only [hnext] using arrive_back u q
    · exact hrest passage hp
  have hl : LinkedPassages w ((q, x) :: rest) := by
    have h := htrace.linked
    cases rest <;> simp_all [LinkedPassages]
  have hstable := physicalTrace_grooved_passages w v q x q rest hl hg htrace.last_link
  intro d hd
  obtain ⟨port, hr⟩ := hstable.grooved_loop_all_time (by simp) hg d
  exact ⟨port, (stepN_after_arrival hnext hd).trans hr⟩

/-- Split a long run at its first revisit and apply the activated normal
form: after a switch-simple lead, either a two-phase simple cycle follows or
a manufactured reflector is activated. -/
theorem first_revisit_fork
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N)
    {start finish : Nat × Tongues}
    (hlive : stepN w (N + 1) start = some finish)
    (hentry : w.link e = some start.1) :
    (∃ (lead : List Passage) (atRepeat : Nat × Tongues) (settled : Tongues),
      PhysicalTrace w start lead atRepeat ∧ SwitchSimple lead ∧
      ∀ d, 0 < d → ∃ port, stepN w d atRepeat = some (port, settled)) ∨
    ∃ A : ManufacturedReflector w start.1 e,
      PathGrooves A.toSupported.paths A.activatedState ∧ A.baseState = start.2 := by
  obtain ⟨before, old, repeated, after, middle,
      hbeforeTrace, hafterTrace, hsimple, hold, hsameSwitch⟩ :=
    first_revisit_of_long_run hN hlive
  obtain ⟨runway, path, hsplit⟩ := List.append_of_mem hold
  rcases old with ⟨p, x⟩
  rcases repeated with ⟨q, y⟩
  subst before
  obtain ⟨atOld, hrunway, hexcursion⟩ := hbeforeTrace.split_append
  have hatOldPort : atOld.1 = p := hexcursion.head_arrive.1
  rcases atOld with ⟨oldPort, u₀⟩
  simp only at hatOldPort
  subst oldPort
  obtain ⟨v, hrepeat⟩ := hafterTrace.head_arrive.2
  have hmiddlePort : middle.1 = q := hafterTrace.head_arrive.1
  rcases middle with ⟨middlePort, u⟩
  simp only at hmiddlePort
  subst middlePort
  have hsw : p / 3 = q / 3 := by
    simpa [passageSwitch] using hsameSwitch
  have hsimpleExcursion : SwitchSimple ((p, x) :: path) := by grind [SwitchSimple]
  have hgrooved := hexcursion.grooved_of_switchSimple hsimpleExcursion
  have hhead := groove_forward (hgrooved (p, x) List.mem_cons_self)
  have hshare : p = q ∨ p = y ∨ x = q ∨ x = y := by
    have hs := same_switch_passages_share_port u u p q hsw
    simpa [hhead, hrepeat] using hs
  have hsupport := crossed_revisit_support_grooved
    hrunway hexcursion hsimple hsw hrepeat
  by_cases hxq : x = q
  · subst q
    have hold := hgrooved (p, x) List.mem_cons_self
    have holdGroove := hold
    rw [hrepeat] at hold
    injection hold with hyp huv
    subst y
    subst v
    have hpathNil := same_exit_excursion_path_nil
      hexcursion hsimpleExcursion
    subst path
    have hself : w.link x = some x := by
      simpa [lastPassageExit] using hexcursion.last_link
    let A : ManufacturedStayReflector w start.1 e := {
      base := start.2
      mouthState := u₀
      returnState := u
      runway := runway
      mouth := p
      arm := x
      runwayTrace := by simpa using hrunway
      coreTrace := by simpa using hexcursion
      simple := hsimple
      stemEndpoint := by
        obtain ⟨u, v, _, harrive, _⟩ := hexcursion.passage_step (p, x) List.mem_cons_self
        simpa only [harrive, passageSwitch] using arrive_stem_endpoint u (p, x).1
      selfLink := hself
      entryEdge := hentry
    }
    refine Or.inr ⟨.stay A, ?_, rfl⟩
    change PathGrooves [runway, [(p, x)]] u
    exact pathGrooves_pair.mpr ⟨(pathGrooves_pair.mp hsupport).1,
      passagesGrooved_singleton.mpr holdGroove⟩
  by_cases hxy : x = y
  · subst y
    exact Or.inl ⟨_, _, _, hbeforeTrace, hsimple,
      hexcursion.simple_same_exit_cycle_all_time hsimpleExcursion hrepeat⟩
  have hpy : p = y := by grind
  subst y
  let A : ManufacturedFlipReflector w start.1 e := {
    base := start.2
    mouthState := u₀
    returnState := u
    afterReturn := v
    runway := runway
    candy := path
    mouth := p
    firstArm := x
    secondArm := q
    runwayTrace := by simpa using hrunway
    candyTrace := hexcursion
    simple := hsimple
    crossed := hrepeat
    arms_ne := hxq
    entryEdge := hentry
  }
  exact Or.inr ⟨.flip A, hsupport, rfl⟩

/-- After a historical prefix, a settled tail contributes at most its one
constant tongue vector. The boundary sample belongs to the prefix. -/
theorem history_then_settled_one_novelty
    {w : Wiring} {N L : Nat} {start atRepeat : Nat × Tongues} {settled : Tongues}
    {history : List (List Bool)}
    (hreach : stepN w L start = some atRepeat)
    (hprefix : ∀ k, k ≤ L → restrictedTonguesAt w N start k ∈ history)
    (htail : ∀ d, 0 < d → ∃ port, stepN w d atRepeat = some (port, settled))
    (times : List Nat) : NoveltyCoverOn w N start times history 1 := by
  refine ⟨[VectorCount.restrict N settled], by simp, ?_⟩
  intro k _
  by_cases hk : k ≤ L
  · exact List.mem_append_left _ (hprefix k hk)
  · obtain ⟨port, hr⟩ := htail (k - L) (by omega)
    have hglobal : stepN w k start = some (port, settled) := by
      rw [show k = L + (k - L) by omega, stepN_add, hreach]
      exact hr
    apply List.mem_append_right
    simp [restrictedTonguesAt, tonguesAt, hglobal]

/-- A prefix of length at most `N` followed by one settled vector has at
most `N+2` distinct vectors, including the initial and boundary samples. -/
theorem prefix_then_settled_distinct_le
    {w : Wiring} {N L : Nat} {start atRepeat : Nat × Tongues} {settled : Tongues}
    (hreach : stepN w L start = some atRepeat) (hL : L ≤ N)
    (htail : ∀ d, 0 < d → ∃ port, stepN w d atRepeat = some (port, settled))
    (times : List Nat)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ N + 2 := by
  have hcover := history_then_settled_one_novelty hreach
    (history := (List.range (L + 1)).map (restrictedTonguesAt w N start))
    (fun k hk => List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩) htail times
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simp only [List.length_map, List.length_range] at hcount
  omega

end GeneralN
