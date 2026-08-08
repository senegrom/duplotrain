import StateLaw
import PhysicalPrefixCount
import FiniteListBounds

/-!
# Correct full physical-run bridge

Every physical tongue vector in a live run is either a cascade-boundary vector
or a prefixAt of the fixed overwrite word of the current cascade.  A concrete
compilation therefore supplies, for each sampled physical time:

* its owning abstract echo step;
* its prefixAt length inside that step's cascade word; and
* equality of the actual tongue vector with that prefixAt overwrite.

The abstract strict bound, deterministic replay, overwrite idempotence and the
`N+1` prefixAt positions then give a strict-base bound for all physical tongue
vectors, not merely the cascade boundaries.
-/

namespace GeneralN

/-- A finite physical sample compiled into an echo overwrite trace. -/
structure PhysicalOverwriteCompilation
    (w : Wiring) (N : Nat) (c0 : Nat × Tongues)
    (sample : List Nat) (globalLo globalHi : Nat) where
  machine : Echo.Machine
  echoEntry : Nat → Nat
  initialRegister : Nat → Nat
  cells : List Nat
  slots : List Nat
  entries : List Nat
  actionOf : Nat × List Nat → List Nat
  initialTongues : Tongues
  owner : Nat → Nat
  prefixAt : Nat → Nat
  run : Echo.IsRun machine echoEntry initialRegister
  initialRegister_wellFormed :
    ∀ c, machine.cellOf (initialRegister c) = c
  frame : Echo.CompleteFiniteEpochFrame
    machine echoEntry initialRegister
    globalLo globalHi cells slots
  cells_length : cells.length ≤ N
  slots_length : slots.length ≤ 2 * N
  entries_nodup : entries.Nodup
  entries_length : entries.length ≤ 2 * N
  owner_entry : ∀ x ∈ sample, echoEntry (owner x) ∈ entries
  owner_range : ∀ x ∈ sample,
    globalLo ≤ owner x ∧ owner x ≤ globalHi
  partner_cover : ∀ k,
    machine.star (machine.cellOf (echoEntry k)) ∈ cells
  prefix_length : ∀ x ∈ sample, prefixAt x ≤ N
  concrete_live : ∀ x ∈ sample, (stepN w x c0).isSome
  physical_tongues : ∀ x ∈ sample,
    tonguesAt w c0 x =
      pinList
        ((actionOf
          (Echo.configSnap machine echoEntry initialRegister
            cells (owner x))).take (prefixAt x))
        (pinTrajectory
          (fun n => actionOf
            (Echo.configSnap machine echoEntry initialRegister cells n))
          initialTongues (owner x))

/-- **Correct full physical bridge theorem.** -/
theorem strict_physical_bound_of_overwriteCompilation
    {w : Wiring} {N : Nat} {c0 : Nat × Tongues}
    {sample : List Nat} {globalLo globalHi : Nat}
    (comp : PhysicalOverwriteCompilation w N c0 sample
      globalLo globalHi)
    (hnd : (sample.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).Nodup) :
    Echo.blockCoreEighth sample.length ≤
      Echo.blockCoreEighth (2 * (N + 1)) *
        (Echo.blockCoreEighth (2*N) *
          (Echo.blockCoreEighth (4*N + 2) * 2^(7*N+18))) := by
  let observed := fun k => tonguesAt w c0 k
  have hndObserved : (sample.map observed).Nodup := by
    apply FiniteListBounds.nodup_map_of_fibre sample observed
      (fun k => VectorCount.restrict N (tonguesAt w c0 k))
    · intro i hi j hj heq
      exact congrArg (VectorCount.restrict N) heq
    · exact hnd
  exact Echo.finite_echo_physical_prefix_bound
    comp.machine comp.echoEntry comp.initialRegister
    comp.run comp.initialRegister_wellFormed
    N globalLo globalHi comp.cells comp.slots
    comp.entries sample comp.frame
    comp.cells_length comp.slots_length
    comp.entries_nodup comp.entries_length
    comp.owner comp.prefixAt comp.owner_entry comp.owner_range
    comp.partner_cover comp.actionOf comp.initialTongues
    observed comp.prefix_length comp.physical_tongues hndObserved

/-- Strict-base replacement for the open state law, conditional only on the
explicit concrete forest/overwrite compilation. -/
def StrictPhysicalStateLaw : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N) →
    ∀ (c0 : Nat × Tongues) (sample : List Nat),
      (∀ k ∈ sample, (stepN w k c0).isSome) →
      (sample.map fun k =>
        VectorCount.restrict N (tonguesAt w c0 k)).Nodup →
      ∀ globalLo globalHi,
      ∀ comp : PhysicalOverwriteCompilation w N c0 sample
        globalLo globalHi,
      Echo.blockCoreEighth sample.length ≤
        Echo.blockCoreEighth (2 * (N + 1)) *
          (Echo.blockCoreEighth (2*N) *
            (Echo.blockCoreEighth (4*N + 2) * 2^(7*N+18)))

/-- The corrected compiled physical state law. -/
theorem strictPhysicalStateLaw : StrictPhysicalStateLaw := by
  intro w N hN c0 sample hlive hnd
    globalLo globalHi comp
  exact strict_physical_bound_of_overwriteCompilation comp hnd

/-- Constructing this proposition from the raw `Wiring` dynamics is now the
only remaining concrete bridge.  All subsequent counting is unconditional. -/
def EveryFinitePhysicalRunCompiles : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N) →
    ∀ (c0 : Nat × Tongues) (sample : List Nat),
      (∀ k ∈ sample, (stepN w k c0).isSome) →
      ∃ globalLo globalHi,
        Nonempty (PhysicalOverwriteCompilation w N c0 sample
          globalLo globalHi)

/-- The unconditional raw-track strict state law follows from the concrete
forest compilation and no further orbit-structure conjecture. -/
theorem strictPhysicalStateLaw_of_compilation
    (hcompile : EveryFinitePhysicalRunCompiles) :
    ∀ (w : Wiring) (N : Nat),
      (∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N) →
      ∀ (c0 : Nat × Tongues) (sample : List Nat),
        (∀ k ∈ sample, (stepN w k c0).isSome) →
        (sample.map fun k =>
          VectorCount.restrict N (tonguesAt w c0 k)).Nodup →
        Echo.blockCoreEighth sample.length ≤
          Echo.blockCoreEighth (2 * (N + 1)) *
            (Echo.blockCoreEighth (2*N) *
              (Echo.blockCoreEighth (4*N + 2) * 2^(7*N+18))) := by
  intro w N hN c0 sample hlive hnd
  obtain ⟨globalLo, globalHi, ⟨comp⟩⟩ :=
    hcompile w N hN c0 sample hlive
  exact strict_physical_bound_of_overwriteCompilation comp hnd

end GeneralN
