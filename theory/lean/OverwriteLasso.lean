import OverwriteDynamics

/-!
# Lifting an abstract lasso through overwrite dynamics

Let `actions k` be the fixed list of branch pins performed by abstract step
`k`.  If the action sequence is periodic from time `μ` with positive period
`λ`, then the full tongue trajectory need not agree at `μ` and `μ+λ`:
off-path bits may still remember older traffic.  But one further traversal
of the same overwrite word removes that memory.  The period transformation
is idempotent, so

    tongue (μ + 2λ + r) = tongue (μ + λ + r)

for every `r`.

Thus an echo-machine lasso lifts to a concrete tongue lasso with at most one
extra abstract period.  This replaces the false requirement that one
register snapshot uniquely determine every latent tree tongue.
-/

namespace GeneralN

/-- Tongue states obtained by executing one fixed pin word per abstract
step. -/
def pinTrajectory (actions : Nat → List Nat) (t0 : Tongues) :
    Nat → Tongues
  | 0 => t0
  | k + 1 => pinList (actions k) (pinTrajectory actions t0 k)

/-- The concatenated pin word executed by `len` actions beginning at
`start`. -/
def pinBlock (actions : Nat → List Nat) (start : Nat) :
    Nat → List Nat
  | 0 => []
  | len + 1 =>
      pinBlock actions start len ++ actions (start + len)

/-- A trajectory segment is exactly the concatenated overwrite block. -/
theorem pinTrajectory_add
    (actions : Nat → List Nat) (t0 : Tongues) :
    ∀ start len,
      pinTrajectory actions t0 (start + len) =
        pinList (pinBlock actions start len)
          (pinTrajectory actions t0 start) := by
  intro start len
  induction len with
  | zero => rfl
  | succ n ih =>
      have hidx : start + (n + 1) = (start + n) + 1 := by omega
      rw [hidx]
      unfold pinTrajectory
      rw [ih]
      unfold pinBlock
      rw [pinList_append]

/-- Pointwise periodicity makes every shifted finite action block equal. -/
theorem pinBlock_period_shift
    (actions : Nat → List Nat) (start period : Nat)
    (hperiod : ∀ k, start ≤ k →
      actions (k + period) = actions k) :
    ∀ len,
      pinBlock actions (start + period) len =
        pinBlock actions start len := by
  intro len
  induction len with
  | zero => rfl
  | succ n ih =>
      unfold pinBlock
      rw [ih]
      have hact := hperiod (start + n) (by omega)
      have hidx : start + period + n = start + n + period := by omega
      rw [hidx, hact]

/-- After one warm-up traversal of a periodic overwrite word, its endpoint
is fixed by all later traversals. -/
theorem pinTrajectory_period_stabilizes
    (actions : Nat → List Nat) (t0 : Tongues)
    (start period : Nat)
    (hperiod : ∀ k, start ≤ k →
      actions (k + period) = actions k) :
    pinTrajectory actions t0 (start + 2 * period) =
      pinTrajectory actions t0 (start + period) := by
  let word := pinBlock actions start period
  have hfirst := pinTrajectory_add actions t0 start period
  have hsecond := pinTrajectory_add actions t0
    (start + period) period
  have hword : pinBlock actions (start + period) period = word := by
    dsimp [word]
    exact pinBlock_period_shift actions start period hperiod period
  have hidx : start + 2 * period = start + period + period := by omega
  rw [hidx, hsecond, hword, hfirst]
  exact pinList_idempotent word (pinTrajectory actions t0 start)

/-- **Overwrite-lasso theorem.**  The complete tongue trajectory is periodic
one abstract period after the abstract action sequence becomes periodic. -/
theorem pinTrajectory_eventually_periodic
    (actions : Nat → List Nat) (t0 : Tongues)
    (start period : Nat)
    (hperiod : ∀ k, start ≤ k →
      actions (k + period) = actions k) :
    ∀ r,
      pinTrajectory actions t0 (start + 2 * period + r) =
        pinTrajectory actions t0 (start + period + r) := by
  intro r
  have hstab := pinTrajectory_period_stabilizes
    actions t0 start period hperiod
  have hperiod' : ∀ k, start + period ≤ k →
      actions (k + period) = actions k := by
    intro k hk
    exact hperiod k (by omega)
  have hblock := pinBlock_period_shift actions
    (start + period) period hperiod' r
  have hleft := pinTrajectory_add actions t0
    (start + 2 * period) r
  have hright := pinTrajectory_add actions t0
    (start + period) r
  rw [hleft, hright]
  have hstart : start + period + period = start + 2 * period := by
    omega
  rw [← hstart] at hblock
  rw [hblock, hstab]

/-- Facing-only movement between abstract cascade steps does not affect the
lasso argument: any observation function of the current tongue vector also
repeats after the warm-up period. -/
theorem observe_pinTrajectory_eventually_periodic
    {α : Type} (observe : Tongues → α)
    (actions : Nat → List Nat) (t0 : Tongues)
    (start period : Nat)
    (hperiod : ∀ k, start ≤ k →
      actions (k + period) = actions k) :
    ∀ r,
      observe (pinTrajectory actions t0
        (start + 2 * period + r)) =
      observe (pinTrajectory actions t0
        (start + period + r)) := by
  intro r
  exact congrArg observe
    (pinTrajectory_eventually_periodic
      actions t0 start period hperiod r)

end GeneralN
