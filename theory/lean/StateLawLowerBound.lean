import StateLaw

/-!
# The `N+4` lower bound, for every `N ≥ 3`

The matching lower bound to `GeneralN.stateLaw`: for every `N ≥ 3` there
is an `N`-switch wiring, a start, and `N+4` live sample times whose
restricted tongue vectors are pairwise distinct.

The witness is the family discovered empirically (`FamilyLowerBound.lean`,
`../tools/bstates.py`): switch `0` is a teardrop (its branches tied, its
stem wired to switch `1`'s stem), switches `1 … N-3` form a
branch-to-stem chain, and switches `N-2, N-1` are doubly linked
(branch1→stem and branch2→branch2).  A cold run started into branch 2 of
switch `N-2` flips the chain down to the teardrop (minting one vector per
switch), rides back, closes the far switch, and then walks the four-corner
Gray square on switches `N-2` and `0`:

* times `0, 1, …, N-2`: the chain prefixes `∅, {N-2}, {N-3,N-2}, …,
  {1,…,N-2}`;
* time `N`: `{0,…,N-2}` (teardrop closed);
* time `2N-1`: `{0,…,N-1}` (far switch closed);
* time `2N`: all but `N-2`;
* time `3N-1`: all but `N-2, 0`;
* time `4N-1`: all but `0`.

Distinctness is witnessed by explicit coordinates: `N-1-m'` inside the
chain block, coordinate `0` against the teardrop closure, coordinate
`N-1` between the blocks, and coordinates `N-2, 0` among the four Gray
corners.
-/

namespace GeneralN

/-! ## The wiring -/

/-- Teardrop at switch 0, chain `1 … N-3`, doubly-linked end pair. -/
def lbLink (N p : Nat) : Option Nat :=
  if p = 0 then some 3
  else if p = 3 then some 0
  else if p = 1 then some 2
  else if p = 2 then some 1
  else if p = 3 * (N - 2) + 1 then some (3 * (N - 1))
  else if p = 3 * (N - 1) then some (3 * (N - 2) + 1)
  else if p = 3 * (N - 2) + 2 then some (3 * (N - 1) + 2)
  else if p = 3 * (N - 1) + 2 then some (3 * (N - 2) + 2)
  else if p % 3 = 2 ∧ 1 ≤ p / 3 ∧ p / 3 ≤ N - 3 then
    some (3 * (p / 3 + 1))
  else if p % 3 = 0 ∧ 2 ≤ p / 3 ∧ p / 3 ≤ N - 2 then
    some (3 * (p / 3 - 1) + 2)
  else none

theorem lb_link_0 (N : Nat) : lbLink N 0 = some 3 := by
  unfold lbLink
  rw [if_pos rfl]

theorem lb_link_3 (N : Nat) : lbLink N 3 = some 0 := by
  unfold lbLink
  rw [if_neg (by omega), if_pos rfl]

theorem lb_link_1 (N : Nat) : lbLink N 1 = some 2 := by
  unfold lbLink
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem lb_link_2 (N : Nat) : lbLink N 2 = some 1 := by
  unfold lbLink
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]

theorem lb_link_endL1 {N : Nat} (h3 : 3 ≤ N) :
    lbLink N (3 * (N - 2) + 1) = some (3 * (N - 1)) := by
  unfold lbLink
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

theorem lb_link_endF {N : Nat} (h3 : 3 ≤ N) :
    lbLink N (3 * (N - 1)) = some (3 * (N - 2) + 1) := by
  unfold lbLink
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem lb_link_endL2 {N : Nat} (h3 : 3 ≤ N) :
    lbLink N (3 * (N - 2) + 2) = some (3 * (N - 1) + 2) := by
  unfold lbLink
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl]

theorem lb_link_endF2 {N : Nat} (h3 : 3 ≤ N) :
    lbLink N (3 * (N - 1) + 2) = some (3 * (N - 2) + 2) := by
  unfold lbLink
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

theorem lb_link_chain_br2 {N k : Nat} (hk1 : 1 ≤ k)
    (hk3 : k ≤ N - 3) :
    lbLink N (3 * k + 2) = some (3 * (k + 1)) := by
  unfold lbLink
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have hdiv : (3 * k + 2) / 3 = k := by omega
  rw [hdiv]

theorem lb_link_chain_stem {N k : Nat} (hk2 : 2 ≤ k)
    (hkN : k ≤ N - 2) :
    lbLink N (3 * k) = some (3 * (k - 1) + 2) := by
  unfold lbLink
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  have hdiv : (3 * k) / 3 = k := by omega
  rw [hdiv]

/-- The family is symmetric for `N ≥ 3`. -/
theorem lb_symm {N : Nat} (h3 : 3 ≤ N) :
    ∀ p q, lbLink N p = some q → lbLink N q = some p := by
  intro p q h
  unfold lbLink at h
  split at h
  · rename_i hp
    cases h
    subst hp
    exact lb_link_3 N
  · split at h
    · rename_i hp
      cases h
      subst hp
      exact lb_link_0 N
    · split at h
      · rename_i hp
        cases h
        subst hp
        exact lb_link_2 N
      · split at h
        · rename_i hp
          cases h
          subst hp
          exact lb_link_1 N
        · split at h
          · rename_i hp
            cases h
            subst hp
            exact lb_link_endF h3
          · split at h
            · rename_i hp
              cases h
              subst hp
              exact lb_link_endL1 h3
            · split at h
              · rename_i hp
                cases h
                subst hp
                exact lb_link_endF2 h3
              · split at h
                · rename_i hp
                  cases h
                  subst hp
                  exact lb_link_endL2 h3
                · split at h
                  · rename_i hcond
                    cases h
                    have hchain := lb_link_chain_stem
                      (N := N) (k := p / 3 + 1)
                      (by omega) (by omega)
                    have hp : 3 * (p / 3 + 1 - 1) + 2 = p := by
                      omega
                    rw [hp] at hchain
                    exact hchain
                  · split at h
                    · rename_i hcond
                      cases h
                      have hchain := lb_link_chain_br2
                        (N := N) (k := p / 3 - 1)
                        (by omega) (by omega)
                      have hq : 3 * (p / 3 - 1) + 2 =
                          3 * (p / 3 - 1) + 2 := rfl
                      have hp : 3 * (p / 3 - 1 + 1) = p := by
                        omega
                      rw [hp] at hchain
                      exact hchain
                    · cases h

/-- Every linked port lies below `3*N`. -/
theorem lb_bound {N : Nat} (h3 : 3 ≤ N) :
    ∀ p q, lbLink N p = some q → p < 3 * N ∧ q < 3 * N := by
  intro p q h
  unfold lbLink at h
  split at h
  · rename_i hp
    cases h
    omega
  · split at h
    · rename_i hp
      cases h
      omega
    · split at h
      · rename_i hp
        cases h
        omega
      · split at h
        · rename_i hp
          cases h
          omega
        · split at h
          · rename_i hp
            cases h
            omega
          · split at h
            · rename_i hp
              cases h
              omega
            · split at h
              · rename_i hp
                cases h
                omega
              · split at h
                · rename_i hp
                  cases h
                  omega
                · split at h
                  · rename_i hcond
                    cases h
                    omega
                  · split at h
                    · rename_i hcond
                      cases h
                      omega
                    · cases h

/-- The lower-bound wiring. -/
def lbWiring (N : Nat) (h3 : 3 ≤ N) : Wiring :=
  ⟨lbLink N, lb_symm h3⟩

/-! ## The tongue states of the witness run -/

/-- Chain prefix: switches `N-1-m … N-2` are set. -/
def lbTA (N m : Nat) : Tongues :=
  fun j => decide (N - 1 - m ≤ j ∧ j ≤ N - 2)

/-- Teardrop closed: switches `0 … N-2`. -/
def lbTB (N : Nat) : Tongues := fun j => decide (j ≤ N - 2)

/-- Everything set: switches `0 … N-1`. -/
def lbTC (N : Nat) : Tongues := fun j => decide (j ≤ N - 1)

/-- All but `N-2`. -/
def lbTD (N : Nat) : Tongues :=
  fun j => decide (j ≤ N - 1 ∧ j ≠ N - 2)

/-- All but `N-2` and `0`. -/
def lbTE (N : Nat) : Tongues :=
  fun j => decide (j ≤ N - 1 ∧ j ≠ N - 2 ∧ j ≠ 0)

/-- All but `0`. -/
def lbTF (N : Nat) : Tongues :=
  fun j => decide (j ≤ N - 1 ∧ j ≠ 0)

/-- The cold start: about to enter branch 2 of switch `N-2`. -/
def lbStart (N : Nat) : Nat × Tongues :=
  (3 * (N - 2) + 2, lbTA N 0)

/-! ## Arrival helpers -/

theorem lb_arrive_stem (t : Tongues) (k : Nat) :
    arrive t (3 * k) = (branchPort k (t k), t) := by
  unfold arrive
  have h0 : (3 * k) % 3 = 0 := by omega
  have hd : (3 * k) / 3 = k := by omega
  rw [if_pos h0, hd]

theorem lb_arrive_br2 (t : Tongues) (k : Nat) :
    arrive t (3 * k + 2) =
      (3 * k, fun j => if j = k then true else t j) := by
  unfold arrive
  have h2 : (3 * k + 2) % 3 = 2 := by omega
  have hd : (3 * k + 2) / 3 = k := by omega
  rw [if_neg (by omega), hd]
  refine congrArg (Prod.mk (3 * k)) ?_
  funext j
  unfold pin bval
  rw [hd, h2]
  rfl

theorem lb_arrive_br1 (t : Tongues) (k : Nat) :
    arrive t (3 * k + 1) =
      (3 * k, fun j => if j = k then false else t j) := by
  unfold arrive
  have h1 : (3 * k + 1) % 3 = 1 := by omega
  have hd : (3 * k + 1) / 3 = k := by omega
  rw [if_neg (by omega), hd]
  refine congrArg (Prod.mk (3 * k)) ?_
  funext j
  unfold pin bval
  rw [hd, h1]
  rfl

theorem lb_set_noop {t : Tongues} {k : Nat} (h : t k = true) :
    (fun j => if j = k then true else t j) = t := by
  funext j
  by_cases hj : j = k
  · subst hj
    rw [if_pos rfl, h]
  · rw [if_neg hj]

theorem lb_stepN_one (w : Wiring) (c : Nat × Tongues) :
    stepN w 1 c = step w c := by
  cases hs : step w c <;> simp [stepN, hs]

/-! ## Tongue transitions -/

theorem lb_TA_succ {N m : Nat} (_hm : m ≤ N - 3) (h4 : 4 ≤ N) :
    (fun j => if j = N - 2 - m then true else lbTA N m j) =
      lbTA N (m + 1) := by
  funext j
  by_cases hj : j = N - 2 - m
  · subst hj
    rw [if_pos rfl]
    unfold lbTA
    rw [eq_comm, decide_eq_true_eq]
    omega
  · rw [if_neg hj]
    unfold lbTA
    rw [decide_eq_decide]
    omega

theorem lb_TA_to_TB {N : Nat} (h4 : 4 ≤ N) :
    (fun j => if j = 0 then true else lbTA N (N - 2) j) = lbTB N := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl]
    unfold lbTB
    rw [eq_comm, decide_eq_true_eq]
    omega
  · rw [if_neg hj]
    unfold lbTA lbTB
    rw [decide_eq_decide]
    omega

theorem lb_TB_to_TC {N : Nat} (h4 : 4 ≤ N) :
    (fun j => if j = N - 1 then true else lbTB N j) = lbTC N := by
  funext j
  by_cases hj : j = N - 1
  · subst hj
    rw [if_pos rfl]
    unfold lbTC
    rw [eq_comm, decide_eq_true_eq]
    omega
  · rw [if_neg hj]
    unfold lbTB lbTC
    rw [decide_eq_decide]
    omega

theorem lb_TC_to_TD {N : Nat} (h4 : 4 ≤ N) :
    (fun j => if j = N - 2 then false else lbTC N j) = lbTD N := by
  funext j
  by_cases hj : j = N - 2
  · subst hj
    rw [if_pos rfl]
    unfold lbTD
    rw [eq_comm]
    simp only [decide_eq_false_iff_not]
    omega
  · rw [if_neg hj]
    unfold lbTC lbTD
    rw [decide_eq_decide]
    omega

theorem lb_TD_to_TE {N : Nat} (h4 : 4 ≤ N) :
    (fun j => if j = 0 then false else lbTD N j) = lbTE N := by
  funext j
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl]
    unfold lbTE
    rw [eq_comm]
    simp only [decide_eq_false_iff_not]
    omega
  · rw [if_neg hj]
    unfold lbTD lbTE
    rw [decide_eq_decide]
    omega

theorem lb_TE_to_TF {N : Nat} (h4 : 4 ≤ N) :
    (fun j => if j = N - 2 then true else lbTE N j) = lbTF N := by
  funext j
  by_cases hj : j = N - 2
  · subst hj
    rw [if_pos rfl]
    unfold lbTF
    rw [eq_comm, decide_eq_true_eq]
    omega
  · rw [if_neg hj]
    unfold lbTE lbTF
    rw [decide_eq_decide]
    omega

/-! ## The trajectory -/

section Trajectory

variable {N : Nat}

/-- Phase A: flipping down the chain. -/
theorem lb_phaseA (h4 : 4 ≤ N) (h3 : 3 ≤ N) {m : Nat}
    (hm : m ≤ N - 3) :
    stepN (lbWiring N h3) m (lbStart N) =
      some (3 * (N - 2 - m) + 2, lbTA N m) := by
  induction m with
  | zero =>
      simp [stepN, lbStart]
  | succ m ih =>
      have hm' : m ≤ N - 3 := by omega
      have hstep := ih hm'
      have hone : stepN (lbWiring N h3) (m + 1) (lbStart N) =
          (stepN (lbWiring N h3) m (lbStart N)).bind
            (stepN (lbWiring N h3) 1) := by
        exact stepN_add _ m 1 _
      rw [hone, hstep]
      simp only [Option.bind_some]
      rw [lb_stepN_one]
      unfold step
      rw [lb_arrive_br2]
      simp only []
      have hlink : (lbWiring N h3).link (3 * (N - 2 - m)) =
          some (3 * (N - 2 - (m + 1)) + 2) := by
        show lbLink N (3 * (N - 2 - m)) = _
        have hthis := lb_link_chain_stem (N := N) (k := N - 2 - m)
          (by omega) (by omega)
        have hidx : N - 2 - m - 1 = N - 2 - (m + 1) := by omega
        rw [hidx] at hthis
        exact hthis
      rw [hlink]
      simp only [Option.map_some]
      rw [lb_TA_succ hm' h4]

/-- Reaching the teardrop stem at time `N-2`. -/
theorem lb_cfg_N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (N - 2) (lbStart N) =
      some (0, lbTA N (N - 2)) := by
  have hmain : stepN (lbWiring N h3) ((N - 3) + 1) (lbStart N) =
      some (0, lbTA N (N - 2)) := by
    rw [stepN_add, lb_phaseA h4 h3 (Nat.le_refl _)]
    simp only [Option.bind_some]
    rw [lb_stepN_one]
    unfold step
    have hport : 3 * (N - 2 - (N - 3)) + 2 = 3 * 1 + 2 := by omega
    rw [hport, lb_arrive_br2]
    simp only []
    have hlink : (lbWiring N h3).link (3 * 1) = some 0 := by
      show lbLink N 3 = some 0
      exact lb_link_3 N
    rw [hlink]
    simp only [Option.map_some]
    have hT : (fun j => if j = 1 then true else lbTA N (N - 3) j) =
        lbTA N (N - 2) := by
      have h := lb_TA_succ (N := N) (m := N - 3) (Nat.le_refl _) h4
      have hidx : N - 2 - (N - 3) = 1 := by omega
      rw [hidx] at h
      have hsucc : N - 3 + 1 = N - 2 := by omega
      rw [hsucc] at h
      exact h
    rw [hT]
  have hidx : (N - 3) + 1 = N - 2 := by omega
  rw [hidx] at hmain
  exact hmain

/-- Bouncing through the teardrop: time `N-1`. -/
theorem lb_cfg_N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (N - 1) (lbStart N) =
      some (2, lbTA N (N - 2)) := by
  have hsplit : N - 1 = (N - 2) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_N2 h4 h3]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  have hzero : (0 : Nat) = 3 * 0 := by omega
  rw [hzero, lb_arrive_stem]
  simp only []
  have hval : lbTA N (N - 2) 0 = false := by
    unfold lbTA
    simp only [decide_eq_false_iff_not]
    omega
  rw [hval]
  unfold branchPort
  simp only [if_neg (Bool.false_ne_true ∘ id)]
  have hlink : (lbWiring N h3).link (3 * 0 + 1) = some 2 := by
    show lbLink N 1 = some 2
    exact lb_link_1 N
  rw [hlink]
  simp only [Option.map_some]

/-- Closing the teardrop: time `N`. -/
theorem lb_cfg_N (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) N (lbStart N) =
      some (3, lbTB N) := by
  have hmain : stepN (lbWiring N h3) ((N - 1) + 1) (lbStart N) =
      some (3, lbTB N) := by
    rw [stepN_add, lb_cfg_N1 h4 h3]
    simp only [Option.bind_some]
    rw [lb_stepN_one]
    unfold step
    have htwo : (2 : Nat) = 3 * 0 + 2 := by omega
    rw [htwo, lb_arrive_br2]
    simp only []
    have hlink : (lbWiring N h3).link (3 * 0) = some 3 := by
      show lbLink N 0 = some 3
      exact lb_link_0 N
    rw [hlink]
    simp only [Option.map_some]
    rw [lb_TA_to_TB h4]
  have hidx : (N - 1) + 1 = N := by omega
  rw [hidx] at hmain
  exact hmain

/-- Phase B: riding the stems back up with the teardrop closed. -/
theorem lb_phaseB (h4 : 4 ≤ N) (h3 : 3 ≤ N) {j : Nat}
    (hj : j ≤ N - 3) :
    stepN (lbWiring N h3) (N + j) (lbStart N) =
      some (3 * (j + 1), lbTB N) := by
  induction j with
  | zero =>
      have h := lb_cfg_N h4 h3
      simpa using h
  | succ j ih =>
      have hj' : j ≤ N - 3 := by omega
      have hstep := ih hj'
      have hone : N + (j + 1) = (N + j) + 1 := by omega
      rw [hone, stepN_add, hstep]
      simp only [Option.bind_some]
      rw [lb_stepN_one]
      unfold step
      rw [lb_arrive_stem]
      simp only []
      have hval : lbTB N (j + 1) = true := by
        unfold lbTB
        rw [decide_eq_true_eq]
        omega
      rw [hval]
      unfold branchPort
      simp only [if_true]
      have hlink : (lbWiring N h3).link (3 * (j + 1) + 2) =
          some (3 * (j + 1 + 1)) := by
        show lbLink N (3 * (j + 1) + 2) = _
        exact lb_link_chain_br2 (by omega) (by omega)
      rw [hlink]
      simp only [Option.map_some]

/-- Crossing to the far switch: time `2N-2`. -/
theorem lb_cfg_2N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N - 2) (lbStart N) =
      some (3 * (N - 1) + 2, lbTB N) := by
  have hsplit : 2 * N - 2 = (N + (N - 3)) + 1 := by omega
  rw [hsplit, stepN_add, lb_phaseB h4 h3 (Nat.le_refl _)]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  have hport : 3 * (N - 3 + 1) = 3 * (N - 2) := by omega
  rw [hport, lb_arrive_stem]
  simp only []
  have hval : lbTB N (N - 2) = true := by
    unfold lbTB
    rw [decide_eq_true_eq]
    omega
  rw [hval]
  unfold branchPort
  simp only [if_true]
  have hlink : (lbWiring N h3).link (3 * (N - 2) + 2) =
      some (3 * (N - 1) + 2) := by
    show lbLink N (3 * (N - 2) + 2) = _
    exact lb_link_endL2 h3
  rw [hlink]
  simp only [Option.map_some]

/-- Closing the far switch: time `2N-1`. -/
theorem lb_cfg_2N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N - 1) (lbStart N) =
      some (3 * (N - 2) + 1, lbTC N) := by
  have hsplit : 2 * N - 1 = (2 * N - 2) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_2N2 h4 h3]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  rw [lb_arrive_br2]
  simp only []
  have hlink : (lbWiring N h3).link (3 * (N - 1)) =
      some (3 * (N - 2) + 1) := by
    show lbLink N (3 * (N - 1)) = _
    exact lb_link_endF h3
  rw [hlink]
  simp only [Option.map_some]
  rw [lb_TB_to_TC h4]

/-- Reopening the near end switch: time `2N`. -/
theorem lb_cfg_2N (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N) (lbStart N) =
      some (3 * (N - 3) + 2, lbTD N) := by
  have hsplit : 2 * N = (2 * N - 1) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_2N1 h4 h3]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  rw [lb_arrive_br1]
  simp only []
  have hlink : (lbWiring N h3).link (3 * (N - 2)) =
      some (3 * (N - 3) + 2) := by
    show lbLink N (3 * (N - 2)) = _
    have hthis := lb_link_chain_stem (N := N) (k := N - 2)
      (by omega) (Nat.le_refl _)
    have hidx : N - 2 - 1 = N - 3 := by omega
    rw [hidx] at hthis
    exact hthis
  rw [hlink]
  simp only [Option.map_some]
  rw [lb_TC_to_TD h4]

/-- Phase C: gliding back down with the near end switch open. -/
theorem lb_phaseC (h4 : 4 ≤ N) (h3 : 3 ≤ N) {j : Nat}
    (hj : j ≤ N - 4) :
    stepN (lbWiring N h3) (2 * N + j) (lbStart N) =
      some (3 * (N - 3 - j) + 2, lbTD N) := by
  induction j with
  | zero =>
      have h := lb_cfg_2N h4 h3
      simpa using h
  | succ j ih =>
      have hj' : j ≤ N - 4 := by omega
      have hstep := ih hj'
      have hone : 2 * N + (j + 1) = (2 * N + j) + 1 := by omega
      rw [hone, stepN_add, hstep]
      simp only [Option.bind_some]
      rw [lb_stepN_one]
      unfold step
      rw [lb_arrive_br2]
      simp only []
      have hnoop : (fun i => if i = N - 3 - j then true
          else lbTD N i) = lbTD N := by
        apply lb_set_noop
        unfold lbTD
        rw [decide_eq_true_eq]
        omega
      rw [hnoop]
      have hlink : (lbWiring N h3).link (3 * (N - 3 - j)) =
          some (3 * (N - 3 - (j + 1)) + 2) := by
        show lbLink N (3 * (N - 3 - j)) = _
        have hthis := lb_link_chain_stem (N := N) (k := N - 3 - j)
          (by omega) (by omega)
        have hidx : N - 3 - j - 1 = N - 3 - (j + 1) := by omega
        rw [hidx] at hthis
        exact hthis
      rw [hlink]
      simp only [Option.map_some]

/-- Back at the teardrop stem: time `3N-3`. -/
theorem lb_cfg_3N3 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 3) (lbStart N) =
      some (0, lbTD N) := by
  have hsplit : 3 * N - 3 = (2 * N + (N - 4)) + 1 := by omega
  rw [hsplit, stepN_add, lb_phaseC h4 h3 (Nat.le_refl _)]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  have hport : 3 * (N - 3 - (N - 4)) + 2 = 3 * 1 + 2 := by omega
  rw [hport, lb_arrive_br2]
  simp only []
  have hnoop : (fun i => if i = 1 then true else lbTD N i) =
      lbTD N := by
    apply lb_set_noop
    unfold lbTD
    rw [decide_eq_true_eq]
    omega
  rw [hnoop]
  have hlink : (lbWiring N h3).link (3 * 1) = some 0 := by
    show lbLink N 3 = some 0
    exact lb_link_3 N
  rw [hlink]
  simp only [Option.map_some]

/-- Through the teardrop the other way: time `3N-2`. -/
theorem lb_cfg_3N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 2) (lbStart N) =
      some (1, lbTD N) := by
  have hsplit : 3 * N - 2 = (3 * N - 3) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_3N3 h4 h3]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  have hzero : (0 : Nat) = 3 * 0 := by omega
  rw [hzero, lb_arrive_stem]
  simp only []
  have hval : lbTD N 0 = true := by
    unfold lbTD
    rw [decide_eq_true_eq]
    omega
  rw [hval]
  unfold branchPort
  simp only [if_true]
  have hlink : (lbWiring N h3).link (3 * 0 + 2) = some 1 := by
    show lbLink N 2 = some 1
    exact lb_link_2 N
  rw [hlink]
  simp only [Option.map_some]

/-- Reopening the teardrop: time `3N-1`. -/
theorem lb_cfg_3N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 1) (lbStart N) =
      some (3, lbTE N) := by
  have hsplit : 3 * N - 1 = (3 * N - 2) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_3N2 h4 h3]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  have hone : (1 : Nat) = 3 * 0 + 1 := by omega
  rw [hone, lb_arrive_br1]
  simp only []
  have hlink : (lbWiring N h3).link (3 * 0) = some 3 := by
    show lbLink N 0 = some 3
    exact lb_link_0 N
  rw [hlink]
  simp only [Option.map_some]
  rw [lb_TD_to_TE h4]

/-- Phase D: riding back up with teardrop and near end both open. -/
theorem lb_phaseD (h4 : 4 ≤ N) (h3 : 3 ≤ N) {j : Nat}
    (hj : j ≤ N - 3) :
    stepN (lbWiring N h3) (3 * N - 1 + j) (lbStart N) =
      some (3 * (j + 1), lbTE N) := by
  induction j with
  | zero =>
      have h := lb_cfg_3N1 h4 h3
      simpa using h
  | succ j ih =>
      have hj' : j ≤ N - 3 := by omega
      have hstep := ih hj'
      have hone : 3 * N - 1 + (j + 1) = (3 * N - 1 + j) + 1 := by
        omega
      rw [hone, stepN_add, hstep]
      simp only [Option.bind_some]
      rw [lb_stepN_one]
      unfold step
      rw [lb_arrive_stem]
      simp only []
      have hval : lbTE N (j + 1) = true := by
        unfold lbTE
        rw [decide_eq_true_eq]
        omega
      rw [hval]
      unfold branchPort
      simp only [if_true]
      have hlink : (lbWiring N h3).link (3 * (j + 1) + 2) =
          some (3 * (j + 1 + 1)) := by
        show lbLink N (3 * (j + 1) + 2) = _
        exact lb_link_chain_br2 (by omega) (by omega)
      rw [hlink]
      simp only [Option.map_some]

/-- Deflected at the open near end switch: time `4N-3`. -/
theorem lb_cfg_4N3 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 3) (lbStart N) =
      some (3 * (N - 1), lbTE N) := by
  have hsplit : 4 * N - 3 = (3 * N - 1 + (N - 3)) + 1 := by omega
  rw [hsplit, stepN_add, lb_phaseD h4 h3 (Nat.le_refl _)]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  have hport : 3 * (N - 3 + 1) = 3 * (N - 2) := by omega
  rw [hport, lb_arrive_stem]
  simp only []
  have hval : lbTE N (N - 2) = false := by
    unfold lbTE
    simp only [decide_eq_false_iff_not]
    omega
  rw [hval]
  unfold branchPort
  simp only [if_neg (Bool.false_ne_true ∘ id)]
  have hlink : (lbWiring N h3).link (3 * (N - 2) + 1) =
      some (3 * (N - 1)) := by
    show lbLink N (3 * (N - 2) + 1) = _
    exact lb_link_endL1 h3
  rw [hlink]
  simp only [Option.map_some]

/-- Across the far switch: time `4N-2`. -/
theorem lb_cfg_4N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 2) (lbStart N) =
      some (3 * (N - 2) + 2, lbTE N) := by
  have hsplit : 4 * N - 2 = (4 * N - 3) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_4N3 h4 h3]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  rw [lb_arrive_stem]
  simp only []
  have hval : lbTE N (N - 1) = true := by
    unfold lbTE
    rw [decide_eq_true_eq]
    omega
  rw [hval]
  unfold branchPort
  simp only [if_true]
  have hlink : (lbWiring N h3).link (3 * (N - 1) + 2) =
      some (3 * (N - 2) + 2) := by
    show lbLink N (3 * (N - 1) + 2) = _
    exact lb_link_endF2 h3
  rw [hlink]
  simp only [Option.map_some]

/-- Reclosing the near end switch: time `4N-1`. -/
theorem lb_cfg_4N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 1) (lbStart N) =
      some (3 * (N - 3) + 2, lbTF N) := by
  have hsplit : 4 * N - 1 = (4 * N - 2) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_4N2 h4 h3]
  simp only [Option.bind_some]
  rw [lb_stepN_one]
  unfold step
  rw [lb_arrive_br2]
  simp only []
  have hlink : (lbWiring N h3).link (3 * (N - 2)) =
      some (3 * (N - 3) + 2) := by
    show lbLink N (3 * (N - 2)) = _
    have hthis := lb_link_chain_stem (N := N) (k := N - 2)
      (by omega) (Nat.le_refl _)
    have hidx : N - 2 - 1 = N - 3 := by omega
    rw [hidx] at hthis
    exact hthis
  rw [hlink]
  simp only [Option.map_some]
  rw [lb_TE_to_TF h4]

end Trajectory

/-! ## Distinctness -/

private theorem lb_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, xs.Nodup →
      (∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) →
      (xs.map f).Nodup := by
  intro xs hnd hinj
  induction xs with
  | nil => simp
  | cons a rest ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
        have hab : a = b := hinj a (by simp) b
          (List.mem_cons_of_mem _ hb) hfb.symm
        subst hab
        exact hnd.1 hb
      · exact ih hnd.2 (fun x hx y hy =>
          hinj x (List.mem_cons_of_mem _ hx) y
            (List.mem_cons_of_mem _ hy))

/-- Restricted vectors differing at a coordinate below `N` are distinct. -/
theorem lb_restrict_ne {N j : Nat} {u v : Tongues} (hj : j < N)
    (h : u j ≠ v j) :
    VectorCount.restrict N u ≠ VectorCount.restrict N v := by
  intro hEq
  apply h
  have hcongr := congrArg (fun l => l[j]?) hEq
  simp only [VectorCount.restrict, List.getElem?_map,
    List.getElem?_range, hj] at hcongr
  exact Option.some.inj hcongr

section Distinct

variable {N : Nat}

theorem lb_ne_TA_TA (h4 : 4 ≤ N) {m m' : Nat} (hlt : m < m')
    (hm' : m' ≤ N - 2) :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTA N m') := by
  apply lb_restrict_ne (j := N - 1 - m') (by omega)
  unfold lbTA
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TA_TB (h4 : 4 ≤ N) {m : Nat} (hm : m ≤ N - 2) :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTB N) := by
  apply lb_restrict_ne (j := 0) (by omega)
  unfold lbTA lbTB
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TA_TC (h4 : 4 ≤ N) {m : Nat} (_hm : m ≤ N - 2) :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTC N) := by
  apply lb_restrict_ne (j := N - 1) (by omega)
  unfold lbTA lbTC
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TA_TD (h4 : 4 ≤ N) {m : Nat} (hm : m ≤ N - 2) :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTD N) := by
  apply lb_restrict_ne (j := N - 1) (by omega)
  unfold lbTA lbTD
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TA_TE (h4 : 4 ≤ N) {m : Nat} (hm : m ≤ N - 2) :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTE N) := by
  apply lb_restrict_ne (j := N - 1) (by omega)
  unfold lbTA lbTE
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TA_TF (h4 : 4 ≤ N) {m : Nat} (_hm : m ≤ N - 2) :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTF N) := by
  apply lb_restrict_ne (j := N - 1) (by omega)
  unfold lbTA lbTF
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TB_TC (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTB N) ≠
      VectorCount.restrict N (lbTC N) := by
  apply lb_restrict_ne (j := N - 1) (by omega)
  unfold lbTB lbTC
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TB_TD (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTB N) ≠
      VectorCount.restrict N (lbTD N) := by
  apply lb_restrict_ne (j := N - 1) (by omega)
  unfold lbTB lbTD
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TB_TE (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTB N) ≠
      VectorCount.restrict N (lbTE N) := by
  apply lb_restrict_ne (j := N - 1) (by omega)
  unfold lbTB lbTE
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TB_TF (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTB N) ≠
      VectorCount.restrict N (lbTF N) := by
  apply lb_restrict_ne (j := N - 1) (by omega)
  unfold lbTB lbTF
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TC_TD (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTC N) ≠
      VectorCount.restrict N (lbTD N) := by
  apply lb_restrict_ne (j := N - 2) (by omega)
  unfold lbTC lbTD
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TC_TE (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTC N) ≠
      VectorCount.restrict N (lbTE N) := by
  apply lb_restrict_ne (j := N - 2) (by omega)
  unfold lbTC lbTE
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TC_TF (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTC N) ≠
      VectorCount.restrict N (lbTF N) := by
  apply lb_restrict_ne (j := 0) (by omega)
  unfold lbTC lbTF
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TD_TE (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTD N) ≠
      VectorCount.restrict N (lbTE N) := by
  apply lb_restrict_ne (j := 0) (by omega)
  unfold lbTD lbTE
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TD_TF (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTD N) ≠
      VectorCount.restrict N (lbTF N) := by
  apply lb_restrict_ne (j := N - 2) (by omega)
  unfold lbTD lbTF
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

theorem lb_ne_TE_TF (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTE N) ≠
      VectorCount.restrict N (lbTF N) := by
  apply lb_restrict_ne (j := N - 2) (by omega)
  unfold lbTE lbTF
  intro hEq
  rw [decide_eq_decide] at hEq
  omega

end Distinct

/-! ## Assembly -/

/-- The sample times. -/
def lbTimes (N : Nat) : List Nat :=
  (List.range (N - 1)) ++ [N, 2 * N - 1, 2 * N, 3 * N - 1, 4 * N - 1]

theorem lb_times_length {N : Nat} (h4 : 4 ≤ N) :
    (lbTimes N).length = N + 4 := by
  unfold lbTimes
  simp only [List.length_append, List.length_range,
    List.length_cons, List.length_nil]
  omega

/-- The vector visited at each chain time. -/
theorem lb_vector_range {N : Nat} (h4 : 4 ≤ N) (h3 : 3 ≤ N)
    {m : Nat} (hm : m ≤ N - 2) :
    VectorCount.restrict N
      (tonguesAt (lbWiring N h3) (lbStart N) m) =
      VectorCount.restrict N (lbTA N m) := by
  by_cases hcase : m ≤ N - 3
  · unfold tonguesAt
    rw [lb_phaseA h4 h3 hcase]
    rfl
  · have hm2 : m = N - 2 := by omega
    subst hm2
    unfold tonguesAt
    rw [lb_cfg_N2 h4 h3]
    rfl

theorem lb_vector_N {N : Nat} (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    VectorCount.restrict N
      (tonguesAt (lbWiring N h3) (lbStart N) N) =
      VectorCount.restrict N (lbTB N) := by
  unfold tonguesAt
  rw [lb_cfg_N h4 h3]
  rfl

theorem lb_vector_2N1 {N : Nat} (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    VectorCount.restrict N
      (tonguesAt (lbWiring N h3) (lbStart N) (2 * N - 1)) =
      VectorCount.restrict N (lbTC N) := by
  unfold tonguesAt
  rw [lb_cfg_2N1 h4 h3]
  rfl

theorem lb_vector_2N {N : Nat} (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    VectorCount.restrict N
      (tonguesAt (lbWiring N h3) (lbStart N) (2 * N)) =
      VectorCount.restrict N (lbTD N) := by
  unfold tonguesAt
  rw [lb_cfg_2N h4 h3]
  rfl

theorem lb_vector_3N1 {N : Nat} (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    VectorCount.restrict N
      (tonguesAt (lbWiring N h3) (lbStart N) (3 * N - 1)) =
      VectorCount.restrict N (lbTE N) := by
  unfold tonguesAt
  rw [lb_cfg_3N1 h4 h3]
  rfl

theorem lb_vector_4N1 {N : Nat} (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    VectorCount.restrict N
      (tonguesAt (lbWiring N h3) (lbStart N) (4 * N - 1)) =
      VectorCount.restrict N (lbTF N) := by
  unfold tonguesAt
  rw [lb_cfg_4N1 h4 h3]
  rfl

/-- **The `N+4` lower bound, symbolically, for `N ≥ 4`.** -/
theorem state_law_lower_bound_of_four {N : Nat} (h4 : 4 ≤ N) :
    ∃ w : Wiring,
      (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) ∧
      ∃ (c0 : Nat × Tongues) (ks : List Nat),
        (∀ k ∈ ks, (stepN w k c0).isSome) ∧
        (ks.map fun k =>
          VectorCount.restrict N (tonguesAt w c0 k)).Nodup ∧
        ks.length = N + 4 := by
  have h3 : 3 ≤ N := by omega
  refine ⟨lbWiring N h3, lb_bound h3, lbStart N, lbTimes N,
    ?_, ?_, lb_times_length h4⟩
  · intro k hk
    unfold lbTimes at hk
    rcases List.mem_append.mp hk with hkr | hks
    · have hm : k < N - 1 := List.mem_range.mp hkr
      by_cases hcase : k ≤ N - 3
      · rw [lb_phaseA h4 h3 hcase]
        rfl
      · have hk2 : k = N - 2 := by omega
        subst hk2
        rw [lb_cfg_N2 h4 h3]
        rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hks
      rcases hks with rfl | rfl | rfl | rfl | rfl
      · rw [lb_cfg_N h4 h3]
        rfl
      · rw [lb_cfg_2N1 h4 h3]
        rfl
      · rw [lb_cfg_2N h4 h3]
        rfl
      · rw [lb_cfg_3N1 h4 h3]
        rfl
      · rw [lb_cfg_4N1 h4 h3]
        rfl
  · have hmap : (lbTimes N).map (fun k =>
        VectorCount.restrict N
          (tonguesAt (lbWiring N h3) (lbStart N) k)) =
        ((List.range (N - 1)).map (fun m =>
          VectorCount.restrict N (lbTA N m))) ++
        [VectorCount.restrict N (lbTB N),
         VectorCount.restrict N (lbTC N),
         VectorCount.restrict N (lbTD N),
         VectorCount.restrict N (lbTE N),
         VectorCount.restrict N (lbTF N)] := by
      unfold lbTimes
      rw [List.map_append]
      have hL : (List.range (N - 1)).map (fun k =>
          VectorCount.restrict N
            (tonguesAt (lbWiring N h3) (lbStart N) k)) =
          (List.range (N - 1)).map (fun m =>
            VectorCount.restrict N (lbTA N m)) := by
        apply List.map_congr_left
        intro m hm
        have hm' : m < N - 1 := List.mem_range.mp hm
        exact lb_vector_range h4 h3 (by omega)
      have hR : [N, 2 * N - 1, 2 * N, 3 * N - 1, 4 * N - 1].map
          (fun k => VectorCount.restrict N
            (tonguesAt (lbWiring N h3) (lbStart N) k)) =
          [VectorCount.restrict N (lbTB N),
           VectorCount.restrict N (lbTC N),
           VectorCount.restrict N (lbTD N),
           VectorCount.restrict N (lbTE N),
           VectorCount.restrict N (lbTF N)] := by
        simp only [List.map_cons, List.map_nil]
        rw [lb_vector_N h4 h3, lb_vector_2N1 h4 h3,
          lb_vector_2N h4 h3, lb_vector_3N1 h4 h3,
          lb_vector_4N1 h4 h3]
      rw [hL, hR]
    rw [hmap]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply lb_map_nodup _ List.nodup_range
      intro a ha b hb hEq
      have ha' : a < N - 1 := List.mem_range.mp ha
      have hb' : b < N - 1 := List.mem_range.mp hb
      by_cases hab : a = b
      · exact hab
      · rcases Nat.lt_or_ge a b with hlt | hge
        · exact absurd hEq (lb_ne_TA_TA h4 hlt (by omega))
        · have hlt : b < a := by omega
          exact absurd hEq.symm (lb_ne_TA_TA h4 hlt (by omega))
    · refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h | h
        · exact lb_ne_TB_TC h4 h
        · exact lb_ne_TB_TD h4 h
        · exact lb_ne_TB_TE h4 h
        · exact lb_ne_TB_TF h4 h
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h
        · exact lb_ne_TC_TD h4 h
        · exact lb_ne_TC_TE h4 h
        · exact lb_ne_TC_TF h4 h
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h
        · exact lb_ne_TD_TE h4 h
        · exact lb_ne_TD_TF h4 h
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        exact lb_ne_TE_TF h4 hmem
      exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
    · intro a haL b hbR
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp haL
      have hm' : m < N - 1 := List.mem_range.mp hm
      rcases List.mem_cons.mp hbR with h | hbR
      · subst h
        exact lb_ne_TA_TB h4 (by omega)
      rcases List.mem_cons.mp hbR with h | hbR
      · subst h
        exact lb_ne_TA_TC h4 (by omega)
      rcases List.mem_cons.mp hbR with h | hbR
      · subst h
        exact lb_ne_TA_TD h4 (by omega)
      rcases List.mem_cons.mp hbR with h | hbR
      · subst h
        exact lb_ne_TA_TE h4 (by omega)
      rcases List.mem_cons.mp hbR with h | hbR
      · subst h
        exact lb_ne_TA_TF h4 (by omega)
      exact absurd hbR (List.not_mem_nil)

/-- **The lower-bound half of the state law, for every `N ≥ 3`.**  The
teardrop / chain / Gray-end-pair family realizes `N + 4` distinct
restricted tongue vectors on `N` switches: there is a wiring on switches
`0 … N-1`, a start configuration, and `N + 4` live sample times whose
tongue vectors are pairwise distinct.  For `N ≥ 4` this is the symbolic
trajectory above; for `N = 3` the same wiring, start, and sample-time
formula are checked by `decide`. -/
theorem state_law_lower_bound {N : Nat} (h3 : 3 ≤ N) :
    ∃ w : Wiring,
      (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) ∧
      ∃ (c0 : Nat × Tongues) (ks : List Nat),
        (∀ k ∈ ks, (stepN w k c0).isSome) ∧
        (ks.map fun k =>
          VectorCount.restrict N (tonguesAt w c0 k)).Nodup ∧
        ks.length = N + 4 := by
  rcases Nat.lt_or_ge N 4 with hlt | h4
  · have hN : N = 3 := by omega
    subst hN
    refine ⟨lbWiring 3 (by decide), lb_bound (by decide), lbStart 3, lbTimes 3,
      ?_, ?_, ?_⟩
    · decide
    · decide
    · decide
  · exact state_law_lower_bound_of_four h4

end GeneralN
