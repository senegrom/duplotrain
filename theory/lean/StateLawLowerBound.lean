import VectorCount

/-!
# The `N+4` lower bound, for every `N ≥ 3`

The matching lower bound to `GeneralN.state_law`: for every `N ≥ 3` there
is an `N`-switch wiring, a start, and `N+4` live sample times whose
restricted tongue vectors are pairwise distinct.

The witness is the family discovered empirically:
switch `0` is a teardrop (its branches tied, its
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

theorem lb_link_0 (N : Nat) : lbLink N 0 = some 3 := by grind [lbLink]

theorem lb_link_3 (N : Nat) : lbLink N 3 = some 0 := by grind [lbLink]

theorem lb_link_1 (N : Nat) : lbLink N 1 = some 2 := by grind [lbLink]

theorem lb_link_2 (N : Nat) : lbLink N 2 = some 1 := by grind [lbLink]

theorem lb_link_endL1 {N : Nat} (h3 : 3 ≤ N) :
    lbLink N (3 * (N - 2) + 1) = some (3 * (N - 1)) := by grind [lbLink]

theorem lb_link_endF {N : Nat} (h3 : 3 ≤ N) :
    lbLink N (3 * (N - 1)) = some (3 * (N - 2) + 1) := by grind [lbLink]

theorem lb_link_endL2 {N : Nat} (h3 : 3 ≤ N) :
    lbLink N (3 * (N - 2) + 2) = some (3 * (N - 1) + 2) := by grind [lbLink]

theorem lb_link_endF2 {N : Nat} (h3 : 3 ≤ N) :
    lbLink N (3 * (N - 1) + 2) = some (3 * (N - 2) + 2) := by grind [lbLink]

theorem lb_link_chain_br2 {N k : Nat} (hk1 : 1 ≤ k)
    (hk3 : k ≤ N - 3) :
    lbLink N (3 * k + 2) = some (3 * (k + 1)) := by
  have hdiv : (3 * k + 2) / 3 = k := by omega
  unfold lbLink
  grind (splits := 12)

theorem lb_link_chain_stem {N k : Nat} (hk2 : 2 ≤ k)
    (hkN : k ≤ N - 2) :
    lbLink N (3 * k) = some (3 * (k - 1) + 2) := by
  have hdiv : (3 * k) / 3 = k := by omega
  unfold lbLink
  grind (splits := 12)

/-- The family is symmetric for `N ≥ 3`. -/
theorem lb_symm {N : Nat} (h3 : 3 ≤ N) :
    ∀ p q, lbLink N p = some q → lbLink N q = some p := by
  intro p q h
  unfold lbLink at h ⊢
  grind (splits := 40)

/-- Every linked port lies below `3*N`. -/
theorem lb_bound {N : Nat} (h3 : 3 ≤ N) :
    ∀ p q, lbLink N p = some q → p < 3 * N ∧ q < 3 * N := by
  intro p q h
  unfold lbLink at h
  grind (splits := 40)

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
  simp [arrive]

theorem lb_arrive_br2 (t : Tongues) (k : Nat) :
    arrive t (3 * k + 2) =
      (3 * k, fun j => if j = k then true else t j) := by
  have hdiv : (3 * k + 2) / 3 = k := by omega
  simp [arrive, hdiv]
  funext j
  unfold pin bval
  rw [hdiv]
  simp

theorem lb_arrive_br1 (t : Tongues) (k : Nat) :
    arrive t (3 * k + 1) =
      (3 * k, fun j => if j = k then false else t j) := by
  have hdiv : (3 * k + 1) / 3 = k := by omega
  simp [arrive, hdiv]
  funext j
  unfold pin bval
  rw [hdiv]
  simp

theorem lb_set_noop {t : Tongues} {k : Nat} (h : t k = true) :
    (fun j => if j = k then true else t j) = t := by grind

theorem lb_stepN_one (w : Wiring) (c : Nat × Tongues) :
    stepN w 1 c = step w c := by
  simp [stepN]

private theorem lb_stepN_br2 {w : Wiring} {t : Tongues} {k q : Nat}
    (hlink : w.link (3 * k) = some q) :
    stepN w 1 (3 * k + 2, t) =
      some (q, fun j => if j = k then true else t j) := by
  rw [lb_stepN_one]
  unfold step
  rw [lb_arrive_br2, hlink]
  rfl

private theorem lb_stepN_br1 {w : Wiring} {t : Tongues} {k q : Nat}
    (hlink : w.link (3 * k) = some q) :
    stepN w 1 (3 * k + 1, t) =
      some (q, fun j => if j = k then false else t j) := by
  rw [lb_stepN_one]
  unfold step
  rw [lb_arrive_br1, hlink]
  rfl

private theorem lb_stepN_stem_true {w : Wiring} {t : Tongues} {k q : Nat}
    (ht : t k = true) (hlink : w.link (3 * k + 2) = some q) :
    stepN w 1 (3 * k, t) = some (q, t) := by
  rw [lb_stepN_one]
  unfold step
  rw [lb_arrive_stem]
  simp only []
  rw [ht]
  simp only [branchPort, if_true]
  rw [hlink]
  rfl

private theorem lb_stepN_stem_false {w : Wiring} {t : Tongues} {k q : Nat}
    (ht : t k = false) (hlink : w.link (3 * k + 1) = some q) :
    stepN w 1 (3 * k, t) = some (q, t) := by
  rw [lb_stepN_one]
  unfold step
  rw [lb_arrive_stem]
  simp only []
  rw [ht]
  unfold branchPort
  simp only [if_neg (Bool.false_ne_true ∘ id)]
  rw [hlink]
  rfl

/-! ## Tongue transitions -/

theorem lb_TA_succ {N m : Nat} :
    (fun j => if j = N - 2 - m then true else lbTA N m j) =
      lbTA N (m + 1) := by grind [lbTA]

theorem lb_TA_to_TB {N : Nat} :
    (fun j => if j = 0 then true else lbTA N (N - 2) j) = lbTB N := by grind [
      lbTA, lbTB]

theorem lb_TB_to_TC {N : Nat} :
    (fun j => if j = N - 1 then true else lbTB N j) = lbTC N := by grind [lbTB,
      lbTC]

theorem lb_TC_to_TD {N : Nat} :
    (fun j => if j = N - 2 then false else lbTC N j) = lbTD N := by grind [
      lbTC, lbTD]

theorem lb_TD_to_TE {N : Nat} :
    (fun j => if j = 0 then false else lbTD N j) = lbTE N := by grind [lbTD,
      lbTE]

theorem lb_TE_to_TF {N : Nat} (h3 : 3 ≤ N) :
    (fun j => if j = N - 2 then true else lbTE N j) = lbTF N := by grind [lbTE,
      lbTF]

/-! ## The trajectory -/

section Trajectory

variable {N : Nat}

/-- Phase A: flipping down the chain. -/
theorem lb_phaseA (h3 : 3 ≤ N) {m : Nat}
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
      have hlink : (lbWiring N h3).link (3 * (N - 2 - m)) =
          some (3 * (N - 2 - (m + 1)) + 2) := by
        show lbLink N (3 * (N - 2 - m)) = _
        have hthis := lb_link_chain_stem (N := N) (k := N - 2 - m)
          (by omega) (by omega)
        have hidx : N - 2 - m - 1 = N - 2 - (m + 1) := by omega
        rw [hidx] at hthis
        exact hthis
      rw [lb_stepN_br2 hlink, lb_TA_succ]

/-- Reaching the teardrop stem at time `N-2`. -/
theorem lb_cfg_N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (N - 2) (lbStart N) =
      some (0, lbTA N (N - 2)) := by
  have hmain : stepN (lbWiring N h3) ((N - 3) + 1) (lbStart N) =
      some (0, lbTA N (N - 2)) := by
    rw [stepN_add, lb_phaseA h3 (Nat.le_refl _)]
    simp only [Option.bind_some]
    have hport : 3 * (N - 2 - (N - 3)) + 2 = 3 * 1 + 2 := by omega
    rw [hport]
    have hlink : (lbWiring N h3).link (3 * 1) = some 0 := by
      show lbLink N 3 = some 0
      exact lb_link_3 N
    have hT : (fun j => if j = 1 then true else lbTA N (N - 3) j) =
        lbTA N (N - 2) := by
      have h := lb_TA_succ (N := N) (m := N - 3)
      have hidx : N - 2 - (N - 3) = 1 := by omega
      rw [hidx] at h
      have hsucc : N - 3 + 1 = N - 2 := by omega
      rw [hsucc] at h
      exact h
    rw [lb_stepN_br2 hlink, hT]
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
  have hzero : (0 : Nat) = 3 * 0 := by omega
  rw [hzero]
  have hval : lbTA N (N - 2) 0 = false := by
    unfold lbTA
    simp only [decide_eq_false_iff_not]
    omega
  have hlink : (lbWiring N h3).link (3 * 0 + 1) = some 2 := by
    show lbLink N 1 = some 2
    exact lb_link_1 N
  rw [lb_stepN_stem_false hval hlink]

/-- Closing the teardrop: time `N`. -/
theorem lb_cfg_N (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) N (lbStart N) =
      some (3, lbTB N) := by
  have hmain : stepN (lbWiring N h3) ((N - 1) + 1) (lbStart N) =
      some (3, lbTB N) := by
    rw [stepN_add, lb_cfg_N1 h4 h3]
    simp only [Option.bind_some]
    have htwo : (2 : Nat) = 3 * 0 + 2 := by omega
    rw [htwo]
    have hlink : (lbWiring N h3).link (3 * 0) = some 3 := by
      show lbLink N 0 = some 3
      exact lb_link_0 N
    rw [lb_stepN_br2 hlink, lb_TA_to_TB]
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
      have hval : lbTB N (j + 1) = true := by
        unfold lbTB
        rw [decide_eq_true_eq]
        omega
      have hlink : (lbWiring N h3).link (3 * (j + 1) + 2) =
          some (3 * (j + 1 + 1)) := by
        show lbLink N (3 * (j + 1) + 2) = _
        exact lb_link_chain_br2 (by omega) (by omega)
      rw [lb_stepN_stem_true hval hlink]

/-- Crossing to the far switch: time `2N-2`. -/
theorem lb_cfg_2N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N - 2) (lbStart N) =
      some (3 * (N - 1) + 2, lbTB N) := by
  have hsplit : 2 * N - 2 = (N + (N - 3)) + 1 := by omega
  rw [hsplit, stepN_add, lb_phaseB h4 h3 (Nat.le_refl _)]
  simp only [Option.bind_some]
  have hport : 3 * (N - 3 + 1) = 3 * (N - 2) := by omega
  rw [hport]
  have hval : lbTB N (N - 2) = true := by
    unfold lbTB
    rw [decide_eq_true_eq]
    omega
  have hlink : (lbWiring N h3).link (3 * (N - 2) + 2) =
      some (3 * (N - 1) + 2) := by
    show lbLink N (3 * (N - 2) + 2) = _
    exact lb_link_endL2 h3
  rw [lb_stepN_stem_true hval hlink]

/-- Closing the far switch: time `2N-1`. -/
theorem lb_cfg_2N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N - 1) (lbStart N) =
      some (3 * (N - 2) + 1, lbTC N) := by
  have hsplit : 2 * N - 1 = (2 * N - 2) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_2N2 h4 h3]
  simp only [Option.bind_some]
  have hlink : (lbWiring N h3).link (3 * (N - 1)) =
      some (3 * (N - 2) + 1) := by
    show lbLink N (3 * (N - 1)) = _
    exact lb_link_endF h3
  rw [lb_stepN_br2 hlink, lb_TB_to_TC]

/-- Reopening the near end switch: time `2N`. -/
theorem lb_cfg_2N (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N) (lbStart N) =
      some (3 * (N - 3) + 2, lbTD N) := by
  have hsplit : 2 * N = (2 * N - 1) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_2N1 h4 h3]
  simp only [Option.bind_some]
  have hlink : (lbWiring N h3).link (3 * (N - 2)) =
      some (3 * (N - 3) + 2) := by
    show lbLink N (3 * (N - 2)) = _
    have hthis := lb_link_chain_stem (N := N) (k := N - 2)
      (by omega) (Nat.le_refl _)
    have hidx : N - 2 - 1 = N - 3 := by omega
    rw [hidx] at hthis
    exact hthis
  rw [lb_stepN_br1 hlink, lb_TC_to_TD]

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
      have hnoop : (fun i => if i = N - 3 - j then true
          else lbTD N i) = lbTD N := by
        apply lb_set_noop
        unfold lbTD
        rw [decide_eq_true_eq]
        omega
      have hlink : (lbWiring N h3).link (3 * (N - 3 - j)) =
          some (3 * (N - 3 - (j + 1)) + 2) := by
        show lbLink N (3 * (N - 3 - j)) = _
        have hthis := lb_link_chain_stem (N := N) (k := N - 3 - j)
          (by omega) (by omega)
        have hidx : N - 3 - j - 1 = N - 3 - (j + 1) := by omega
        rw [hidx] at hthis
        exact hthis
      simpa only [hnoop] using
        (lb_stepN_br2 (t := lbTD N) hlink)

/-- Back at the teardrop stem: time `3N-3`. -/
theorem lb_cfg_3N3 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 3) (lbStart N) =
      some (0, lbTD N) := by
  have hsplit : 3 * N - 3 = (2 * N + (N - 4)) + 1 := by omega
  rw [hsplit, stepN_add, lb_phaseC h4 h3 (Nat.le_refl _)]
  simp only [Option.bind_some]
  have hport : 3 * (N - 3 - (N - 4)) + 2 = 3 * 1 + 2 := by omega
  rw [hport]
  have hnoop : (fun i => if i = 1 then true else lbTD N i) =
      lbTD N := by
    apply lb_set_noop
    unfold lbTD
    rw [decide_eq_true_eq]
    omega
  have hlink : (lbWiring N h3).link (3 * 1) = some 0 := by
    show lbLink N 3 = some 0
    exact lb_link_3 N
  simpa only [hnoop] using (lb_stepN_br2 (t := lbTD N) hlink)

/-- Through the teardrop the other way: time `3N-2`. -/
theorem lb_cfg_3N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 2) (lbStart N) =
      some (1, lbTD N) := by
  have hsplit : 3 * N - 2 = (3 * N - 3) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_3N3 h4 h3]
  simp only [Option.bind_some]
  have hzero : (0 : Nat) = 3 * 0 := by omega
  rw [hzero]
  have hval : lbTD N 0 = true := by
    unfold lbTD
    rw [decide_eq_true_eq]
    omega
  have hlink : (lbWiring N h3).link (3 * 0 + 2) = some 1 := by
    show lbLink N 2 = some 1
    exact lb_link_2 N
  rw [lb_stepN_stem_true hval hlink]

/-- Reopening the teardrop: time `3N-1`. -/
theorem lb_cfg_3N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 1) (lbStart N) =
      some (3, lbTE N) := by
  have hsplit : 3 * N - 1 = (3 * N - 2) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_3N2 h4 h3]
  simp only [Option.bind_some]
  have hone : (1 : Nat) = 3 * 0 + 1 := by omega
  rw [hone]
  have hlink : (lbWiring N h3).link (3 * 0) = some 3 := by
    show lbLink N 0 = some 3
    exact lb_link_0 N
  rw [lb_stepN_br1 hlink, lb_TD_to_TE]

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
      have hval : lbTE N (j + 1) = true := by
        unfold lbTE
        rw [decide_eq_true_eq]
        omega
      have hlink : (lbWiring N h3).link (3 * (j + 1) + 2) =
          some (3 * (j + 1 + 1)) := by
        show lbLink N (3 * (j + 1) + 2) = _
        exact lb_link_chain_br2 (by omega) (by omega)
      rw [lb_stepN_stem_true hval hlink]

/-- Deflected at the open near end switch: time `4N-3`. -/
theorem lb_cfg_4N3 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 3) (lbStart N) =
      some (3 * (N - 1), lbTE N) := by
  have hsplit : 4 * N - 3 = (3 * N - 1 + (N - 3)) + 1 := by omega
  rw [hsplit, stepN_add, lb_phaseD h4 h3 (Nat.le_refl _)]
  simp only [Option.bind_some]
  have hport : 3 * (N - 3 + 1) = 3 * (N - 2) := by omega
  rw [hport]
  have hval : lbTE N (N - 2) = false := by
    unfold lbTE
    simp only [decide_eq_false_iff_not]
    omega
  have hlink : (lbWiring N h3).link (3 * (N - 2) + 1) =
      some (3 * (N - 1)) := by
    show lbLink N (3 * (N - 2) + 1) = _
    exact lb_link_endL1 h3
  rw [lb_stepN_stem_false hval hlink]

/-- Across the far switch: time `4N-2`. -/
theorem lb_cfg_4N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 2) (lbStart N) =
      some (3 * (N - 2) + 2, lbTE N) := by
  have hsplit : 4 * N - 2 = (4 * N - 3) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_4N3 h4 h3]
  simp only [Option.bind_some]
  have hval : lbTE N (N - 1) = true := by
    unfold lbTE
    rw [decide_eq_true_eq]
    omega
  have hlink : (lbWiring N h3).link (3 * (N - 1) + 2) =
      some (3 * (N - 2) + 2) := by
    show lbLink N (3 * (N - 1) + 2) = _
    exact lb_link_endF2 h3
  rw [lb_stepN_stem_true hval hlink]

/-- Reclosing the near end switch: time `4N-1`. -/
theorem lb_cfg_4N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 1) (lbStart N) =
      some (3 * (N - 3) + 2, lbTF N) := by
  have hsplit : 4 * N - 1 = (4 * N - 2) + 1 := by omega
  rw [hsplit, stepN_add, lb_cfg_4N2 h4 h3]
  simp only [Option.bind_some]
  have hlink : (lbWiring N h3).link (3 * (N - 2)) =
      some (3 * (N - 3) + 2) := by
    show lbLink N (3 * (N - 2)) = _
    have hthis := lb_link_chain_stem (N := N) (k := N - 2)
      (by omega) (Nat.le_refl _)
    have hidx : N - 2 - 1 = N - 3 := by omega
    rw [hidx] at hthis
    exact hthis
  rw [lb_stepN_br2 hlink, lb_TE_to_TF h3]

end Trajectory

/-! ## Distinctness -/

/-- Restricted vectors differing at a coordinate below `N` are distinct. -/
theorem lb_restrict_ne {N j : Nat} {u v : Tongues} (hj : j < N)
    (h : u j ≠ v j) :
    VectorCount.restrict N u ≠ VectorCount.restrict N v := by
  intro hEq
  apply h
  simpa [VectorCount.restrict, hj] using
    congrArg (fun l => l[j]?) hEq

section Distinct

variable {N : Nat}

theorem lb_ne_TA_TA (h4 : 4 ≤ N) {m m' : Nat} (hlt : m < m')
    (hm' : m' ≤ N - 2) :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTA N m') :=
  lb_restrict_ne (j := N - 1 - m') (by omega) (by unfold lbTA; grind)

theorem lb_ne_TA_TB (h4 : 4 ≤ N) {m : Nat} (hm : m ≤ N - 2) :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTB N) :=
  lb_restrict_ne (j := 0) (by omega) (by unfold lbTA lbTB; grind)

theorem lb_ne_TA_TC (h4 : 4 ≤ N) {m : Nat} :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTC N) :=
  lb_restrict_ne (j := N - 1) (by omega) (by unfold lbTA lbTC; grind)

theorem lb_ne_TA_TD (h4 : 4 ≤ N) {m : Nat} :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTD N) :=
  lb_restrict_ne (j := N - 1) (by omega) (by unfold lbTA lbTD; grind)

theorem lb_ne_TA_TE (h4 : 4 ≤ N) {m : Nat} :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTE N) :=
  lb_restrict_ne (j := N - 1) (by omega) (by unfold lbTA lbTE; grind)

theorem lb_ne_TA_TF (h4 : 4 ≤ N) {m : Nat} :
    VectorCount.restrict N (lbTA N m) ≠
      VectorCount.restrict N (lbTF N) :=
  lb_restrict_ne (j := N - 1) (by omega) (by unfold lbTA lbTF; grind)

theorem lb_ne_TB_TC (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTB N) ≠
      VectorCount.restrict N (lbTC N) :=
  lb_restrict_ne (j := N - 1) (by omega) (by unfold lbTB lbTC; grind)

theorem lb_ne_TB_TD (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTB N) ≠
      VectorCount.restrict N (lbTD N) :=
  lb_restrict_ne (j := N - 1) (by omega) (by unfold lbTB lbTD; grind)

theorem lb_ne_TB_TE (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTB N) ≠
      VectorCount.restrict N (lbTE N) :=
  lb_restrict_ne (j := N - 1) (by omega) (by unfold lbTB lbTE; grind)

theorem lb_ne_TB_TF (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTB N) ≠
      VectorCount.restrict N (lbTF N) :=
  lb_restrict_ne (j := N - 1) (by omega) (by unfold lbTB lbTF; grind)

theorem lb_ne_TC_TD (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTC N) ≠
      VectorCount.restrict N (lbTD N) :=
  lb_restrict_ne (j := N - 2) (by omega) (by unfold lbTC lbTD; grind)

theorem lb_ne_TC_TE (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTC N) ≠
      VectorCount.restrict N (lbTE N) :=
  lb_restrict_ne (j := N - 2) (by omega) (by unfold lbTC lbTE; grind)

theorem lb_ne_TC_TF (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTC N) ≠
      VectorCount.restrict N (lbTF N) :=
  lb_restrict_ne (j := 0) (by omega) (by unfold lbTC lbTF; grind)

theorem lb_ne_TD_TE (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTD N) ≠
      VectorCount.restrict N (lbTE N) :=
  lb_restrict_ne (j := 0) (by omega) (by unfold lbTD lbTE; grind)

theorem lb_ne_TD_TF (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTD N) ≠
      VectorCount.restrict N (lbTF N) :=
  lb_restrict_ne (j := N - 2) (by omega) (by unfold lbTD lbTF; grind)

theorem lb_ne_TE_TF (h4 : 4 ≤ N) :
    VectorCount.restrict N (lbTE N) ≠
      VectorCount.restrict N (lbTF N) :=
  lb_restrict_ne (j := N - 2) (by omega) (by unfold lbTE lbTF; grind)

end Distinct

/-! ## Assembly -/

/-- The sample times. -/
def lbTimes (N : Nat) : List Nat :=
  (List.range (N - 1)) ++ [N, 2 * N - 1, 2 * N, 3 * N - 1, 4 * N - 1]

theorem lb_times_length {N : Nat} (h4 : 4 ≤ N) :
    (lbTimes N).length = N + 4 := by grind [lbTimes]

/-- The vector visited at each chain time. -/
theorem lb_vector_range {N : Nat} (h4 : 4 ≤ N) (h3 : 3 ≤ N)
    {m : Nat} (hm : m ≤ N - 2) :
    VectorCount.restrict N
      (tonguesAt (lbWiring N h3) (lbStart N) m) =
      VectorCount.restrict N (lbTA N m) := by
  by_cases hcase : m ≤ N - 3
  · simp [tonguesAt, lb_phaseA h3 hcase]
  · have hm2 : m = N - 2 := by omega
    subst hm2
    simp [tonguesAt, lb_cfg_N2 h4 h3]

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
      · simp [lb_phaseA h3 hcase]
      · have hk2 : k = N - 2 := by omega
        subst hk2
        simp [lb_cfg_N2 h4 h3]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hks
      rcases hks with rfl | rfl | rfl | rfl | rfl
      all_goals simp [lb_cfg_N h4 h3, lb_cfg_2N1 h4 h3,
        lb_cfg_2N h4 h3, lb_cfg_3N1 h4 h3, lb_cfg_4N1 h4 h3]
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
        simp [tonguesAt, lb_cfg_N h4 h3, lb_cfg_2N1 h4 h3,
          lb_cfg_2N h4 h3, lb_cfg_3N1 h4 h3,
          lb_cfg_4N1 h4 h3]
      rw [hL, hR]
    rw [hmap]
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · apply nodup_map_of_injective_on_mem
      intro a ha b hb hEq
      have ha' : a < N - 1 := List.mem_range.mp ha
      have hb' : b < N - 1 := List.mem_range.mp hb
      by_cases hab : a = b
      · exact hab
      · rcases Nat.lt_or_ge a b with hlt | hge
        · exact absurd hEq (lb_ne_TA_TA h4 hlt (by omega))
        · have hlt : b < a := by omega
          exact absurd hEq.symm (lb_ne_TA_TA h4 hlt (by omega))
      exact List.nodup_range
    · simp [lb_ne_TB_TC h4, lb_ne_TB_TD h4,
        lb_ne_TB_TE h4, lb_ne_TB_TF h4,
        lb_ne_TC_TD h4, lb_ne_TC_TE h4,
        lb_ne_TC_TF h4, lb_ne_TD_TE h4,
        lb_ne_TD_TF h4, lb_ne_TE_TF h4]
    · intro a haL b hbR
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp haL
      have hm' : m < N - 1 := List.mem_range.mp hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbR
      rcases hbR with rfl | rfl | rfl | rfl | rfl
      · exact lb_ne_TA_TB h4 (by omega)
      · exact lb_ne_TA_TC h4
      · exact lb_ne_TA_TD h4
      · exact lb_ne_TA_TE h4
      · exact lb_ne_TA_TF h4

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
