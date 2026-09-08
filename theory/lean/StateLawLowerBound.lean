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

/-- Every linked port lies below `3*N`. -/
theorem lb_bound {N : Nat} (h3 : 3 ≤ N) :
    ∀ p q, lbLink N p = some q → p < 3 * N ∧ q < 3 * N := by
  intro p q h
  unfold lbLink at h
  grind (splits := 40)

/-- The lower-bound wiring. -/
def lbWiring (N : Nat) (h3 : 3 ≤ N) : Wiring :=
  ⟨lbLink N, fun p q h => by unfold lbLink at h ⊢; grind (splits := 40)⟩

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

/-! ## One-step transitions -/

private theorem lb_stepN_br2 {w : Wiring} {t : Tongues} {k q : Nat}
    (hlink : w.link (3 * k) = some q) :
    stepN w 1 (3 * k + 2, t) =
      some (q, fun j => if j = k then true else t j) := by
  have hdiv : (3 * k + 2) / 3 = k := by omega
  simp [stepN, step, arrive, hdiv, hlink]; funext j; simp [pin, bval, hdiv]

private theorem lb_stepN_br1 {w : Wiring} {t : Tongues} {k q : Nat}
    (hlink : w.link (3 * k) = some q) :
    stepN w 1 (3 * k + 1, t) =
      some (q, fun j => if j = k then false else t j) := by
  have hdiv : (3 * k + 1) / 3 = k := by omega
  simp [stepN, step, arrive, hdiv, hlink]; funext j; simp [pin, bval, hdiv]

private theorem lb_stepN_stem {w : Wiring} {t : Tongues} {k q : Nat}
    (hlink : w.link (branchPort k (t k)) = some q) :
    stepN w 1 (3 * k, t) = some (q, t) := by simp [stepN, step, arrive, hlink]

private theorem lb_next {w : Wiring} {m n : Nat} {a b c : Nat × Tongues}
    (h : stepN w m a = some b) (ht : n = m + 1)
    (hs : stepN w 1 b = some c) : stepN w n a = some c := by
  rw [ht, stepN_add, h]; exact hs

/-! ## The trajectory -/

section Trajectory

variable {N : Nat}

/-- Both upward phases traverse the same selected chain without moving a tongue. -/
private theorem lb_chain_up {N : Nat} (h3 : 3 ≤ N) (t : Tongues) {j : Nat}
    (hj : j ≤ N - 3) (ht : ∀ k, 1 ≤ k → k ≤ j → t k = true) :
    stepN (lbWiring N h3) j (3, t) = some (3 * (j + 1), t) := by
  induction j with
  | zero => simp [stepN]
  | succ j ih =>
      rw [stepN_add, ih (by omega) (fun k hk hk' => ht k hk (by omega))]
      simp only [Option.bind_some]
      apply lb_stepN_stem
      simpa [lbWiring, branchPort, ht (j + 1) (by omega) (by omega)] using
        lb_link_chain_br2 (N := N) (k := j + 1) (by omega) (by omega)

/-- Descending writes the visited interval and exits at the teardrop stem. -/
private theorem lb_chain_down {N k m : Nat} (h3 : 3 ≤ N) (t : Tongues)
    (hk : 1 ≤ k) (hkN : k ≤ N - 2) (hm : m ≤ k) :
    stepN (lbWiring N h3) m (3 * k + 2, t) =
      some (if m = k then 0 else 3 * (k - m) + 2,
        fun j => if k + 1 - m ≤ j ∧ j ≤ k then true else t j) := by
  induction m with
  | zero =>
      simp only [stepN, Nat.sub_zero, if_neg (by omega : 0 ≠ k)]
      congr 2; funext j; grind
  | succ m ih =>
      rw [stepN_add, ih (by omega)]
      simp only [Option.bind_some, if_neg (by omega : m ≠ k)]
      have hlink : (lbWiring N h3).link (3 * (k - m)) =
          some (if m + 1 = k then 0 else 3 * (k - (m + 1)) + 2) := by
        by_cases h : m + 1 = k
        · have hkm : k - m = 1 := by omega
          simp [h, hkm, lbWiring, lbLink]
        · simpa [lbWiring, h, Nat.sub_sub] using
            lb_link_chain_stem (N := N) (k := k - m) (by omega) (by omega)
      rw [lb_stepN_br2 hlink]
      congr 2; funext j; grind

/-- Phase A: flipping down the chain. -/
theorem lb_phaseA (h3 : 3 ≤ N) {m : Nat} (hm : m ≤ N - 2) :
    stepN (lbWiring N h3) m (lbStart N) =
      some (if m = N - 2 then 0 else 3 * (N - 2 - m) + 2, lbTA N m) := by
  unfold lbStart
  rw [lb_chain_down h3 _ (by omega) (Nat.le_refl _) hm]
  congr 2; funext j; grind [lbTA]

/-- Reaching the teardrop stem at time `N-2`. -/
theorem lb_cfg_N2 (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (N - 2) (lbStart N) =
      some (0, lbTA N (N - 2)) := by
  simpa using lb_phaseA h3 (Nat.le_refl _)

/-- Bouncing through the teardrop: time `N-1`. -/
theorem lb_cfg_N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (N - 1) (lbStart N) =
      some (2, lbTA N (N - 2)) := by
  apply lb_next (lb_cfg_N2 h3) (by omega)
  apply lb_stepN_stem (k := 0)
  have hidx : N - 1 - (N - 2) = 1 := by omega
  simp [lbWiring, branchPort, lbTA, hidx, lbLink]

/-- Closing the teardrop: time `N`. -/
theorem lb_cfg_N (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) N (lbStart N) =
      some (3, lbTB N) := by
  apply lb_next (lb_cfg_N1 h4 h3) (by omega)
  change stepN _ 1 (3 * 0 + 2, _) = _
  rw [lb_stepN_br2 (k := 0) (q := 3) (by simp [lbWiring, lbLink])]
  congr 2; funext j; grind [lbTA, lbTB]

/-- Phase B: riding the stems back up with the teardrop closed. -/
theorem lb_phaseB (h4 : 4 ≤ N) (h3 : 3 ≤ N) {j : Nat}
    (hj : j ≤ N - 3) :
    stepN (lbWiring N h3) (N + j) (lbStart N) =
      some (3 * (j + 1), lbTB N) := by
  rw [stepN_add, lb_cfg_N h4 h3]
  exact lb_chain_up h3 _ hj (by intros; simp only [lbTB, decide_eq_true_eq]; omega)

/-- Crossing to the far switch: time `2N-2`. -/
theorem lb_cfg_2N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N - 2) (lbStart N) =
      some (3 * (N - 1) + 2, lbTB N) := by
  apply lb_next (lb_phaseB h4 h3 (Nat.le_refl _)) (by omega)
  rw [show N - 3 + 1 = N - 2 by omega]
  apply lb_stepN_stem
  simp only [lbTB, branchPort, lbWiring]
  grind [lbLink]

/-- Closing the far switch: time `2N-1`. -/
theorem lb_cfg_2N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N - 1) (lbStart N) =
      some (3 * (N - 2) + 1, lbTC N) := by
  apply lb_next (lb_cfg_2N2 h4 h3) (by omega)
  rw [lb_stepN_br2 (k := N - 1) (q := 3 * (N - 2) + 1)
    (by simp only [lbWiring]; grind [lbLink])]
  congr 2; funext j; grind [lbTB, lbTC]

/-- Reopening the near end switch: time `2N`. -/
theorem lb_cfg_2N (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (2 * N) (lbStart N) =
      some (3 * (N - 3) + 2, lbTD N) := by
  apply lb_next (lb_cfg_2N1 h4 h3) (by omega)
  rw [lb_stepN_br1 (w := lbWiring N h3)
    (lb_link_chain_stem (k := N - 2) (by omega) (Nat.le_refl _))]
  congr 2; funext j; grind [lbTC, lbTD]

/-- Phase C: gliding back down with the near end switch open. -/
theorem lb_phaseC (h4 : 4 ≤ N) (h3 : 3 ≤ N) {j : Nat} (hj : j ≤ N - 3) :
    stepN (lbWiring N h3) (2 * N + j) (lbStart N) =
      some (if j = N - 3 then 0 else 3 * (N - 3 - j) + 2, lbTD N) := by
  rw [stepN_add, lb_cfg_2N h4 h3]
  simp only [Option.bind_some]
  rw [lb_chain_down h3 _ (by omega) (by omega) hj]
  congr 2; funext i; grind [lbTD]

/-- Back at the teardrop stem: time `3N-3`. -/
theorem lb_cfg_3N3 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 3) (lbStart N) =
      some (0, lbTD N) := by
  have ht : 2 * N + (N - 3) = 3 * N - 3 := by omega
  simpa [ht] using lb_phaseC h4 h3 (Nat.le_refl _)

/-- Through the teardrop the other way: time `3N-2`. -/
theorem lb_cfg_3N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 2) (lbStart N) =
      some (1, lbTD N) := by
  apply lb_next (lb_cfg_3N3 h4 h3) (by omega)
  apply lb_stepN_stem (k := 0)
  have hval : lbTD N 0 = true := by simp only [lbTD, decide_eq_true_eq]; omega
  simp [branchPort, hval, lbWiring, lbLink]

/-- Reopening the teardrop: time `3N-1`. -/
theorem lb_cfg_3N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (3 * N - 1) (lbStart N) =
      some (3, lbTE N) := by
  apply lb_next (lb_cfg_3N2 h4 h3) (by omega)
  change stepN _ 1 (3 * 0 + 1, _) = _
  rw [lb_stepN_br1 (k := 0) (q := 3) (by simp [lbWiring, lbLink])]
  congr 2; funext j; grind [lbTD, lbTE]

/-- Phase D: riding back up with teardrop and near end both open. -/
theorem lb_phaseD (h4 : 4 ≤ N) (h3 : 3 ≤ N) {j : Nat}
    (hj : j ≤ N - 3) :
    stepN (lbWiring N h3) (3 * N - 1 + j) (lbStart N) =
      some (3 * (j + 1), lbTE N) := by
  rw [stepN_add, lb_cfg_3N1 h4 h3]
  exact lb_chain_up h3 _ hj (by intros; simp only [lbTE, decide_eq_true_eq]; omega)

/-- Deflected at the open near end switch: time `4N-3`. -/
theorem lb_cfg_4N3 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 3) (lbStart N) =
      some (3 * (N - 1), lbTE N) := by
  apply lb_next (lb_phaseD h4 h3 (Nat.le_refl _)) (by omega)
  rw [show N - 3 + 1 = N - 2 by omega]
  apply lb_stepN_stem
  simp [branchPort, lbTE, lbWiring]; grind [lbLink]

/-- Across the far switch: time `4N-2`. -/
theorem lb_cfg_4N2 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 2) (lbStart N) =
      some (3 * (N - 2) + 2, lbTE N) := by
  apply lb_next (lb_cfg_4N3 h4 h3) (by omega)
  apply lb_stepN_stem
  have hval : lbTE N (N - 1) = true := by simp only [lbTE, decide_eq_true_eq]; omega
  simp [branchPort, hval, lbWiring]; grind [lbLink]

/-- Reclosing the near end switch: time `4N-1`. -/
theorem lb_cfg_4N1 (h4 : 4 ≤ N) (h3 : 3 ≤ N) :
    stepN (lbWiring N h3) (4 * N - 1) (lbStart N) =
      some (3 * (N - 3) + 2, lbTF N) := by
  apply lb_next (lb_cfg_4N2 h4 h3) (by omega)
  rw [lb_stepN_br2 (w := lbWiring N h3)
    (lb_link_chain_stem (k := N - 2) (by omega) (Nat.le_refl _))]
  congr 2; funext j; grind [lbTE, lbTF]

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

/-- The named vectors differ pairwise at coordinate `0`, `N - 1` or `N - 2`. -/
macro "lb_ne" N:term : tactic => `(tactic| first
  | exact lb_restrict_ne (j := 0) (by omega)
      (by simp only [lbTA, lbTB, lbTC, lbTD, lbTE, lbTF]; grind)
  | exact lb_restrict_ne (j := $N - 1) (by omega)
      (by simp only [lbTA, lbTB, lbTC, lbTD, lbTE, lbTF]; grind)
  | exact lb_restrict_ne (j := $N - 2) (by omega)
      (by simp only [lbTA, lbTB, lbTC, lbTD, lbTE, lbTF]; grind))

/-! ## Assembly -/

/-- The sample times. -/
def lbTimes (N : Nat) : List Nat :=
  (List.range (N - 1)) ++ [N, 2 * N - 1, 2 * N, 3 * N - 1, 4 * N - 1]

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
    ?_, ?_, by grind [lbTimes]⟩
  · intro k hk
    unfold lbTimes at hk
    rcases List.mem_append.mp hk with hkr | hks
    · have hm : k < N - 1 := List.mem_range.mp hkr
      simp [lb_phaseA h3 (by omega : k ≤ N - 2)]
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
      simp only [lbTimes, List.map_append]
      congr 1
      · apply List.map_congr_left
        intro m hm
        have hm' := List.mem_range.mp hm
        simp [tonguesAt, lb_phaseA h3 (by omega : m ≤ N - 2)]
      · simp [tonguesAt, lb_cfg_N h4 h3, lb_cfg_2N1 h4 h3,
          lb_cfg_2N h4 h3, lb_cfg_3N1 h4 h3, lb_cfg_4N1 h4 h3]
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
        · exact absurd hEq (lb_restrict_ne (j := N - 1 - b) (by omega) (by unfold lbTA; grind))
        · exact absurd hEq.symm (lb_restrict_ne (j := N - 1 - a) (by omega) (by unfold lbTA; grind))
      exact List.nodup_range
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, not_false_eq_true, and_true]
      and_intros <;> lb_ne N
    · intro a haL b hbR
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp haL
      have hm' : m < N - 1 := List.mem_range.mp hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hbR
      rcases hbR with rfl | rfl | rfl | rfl | rfl <;> lb_ne N

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
