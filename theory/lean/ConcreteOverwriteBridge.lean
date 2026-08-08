import StateLaw
import CanonicalConfigurationRepresentatives

/-!
# Correct concrete-to-echo bridge through overwrite dynamics

A register snapshot does not encode every latent off-path tongue in a branching
tree.  The correct bridge records instead that every abstract echo step emits
a fixed finite word of concrete branch-pin assignments.  Deterministic echo
configuration replay plus overwrite idempotence then proves that each finite
configuration carries at most two full tongue vectors.

This file packages exactly that correct semantic interface and transfers the
unconditional strict-base echo bound to concrete tongue vectors observed at
abstract cascade boundaries.
-/

namespace GeneralN

/-- A finite concrete boundary trace compiled into an echo overwrite trace. -/
structure OverwriteEchoCompilation
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
  concreteTime : Nat → Nat
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
  entry_cover : ∀ k ∈ sample, echoEntry k ∈ entries
  echo_range : ∀ k ∈ sample,
    globalLo ≤ k ∧ k ≤ globalHi
  partner_cover : ∀ k,
    machine.star (machine.cellOf (echoEntry k)) ∈ cells
  concrete_live : ∀ k ∈ sample,
    (stepN w (concreteTime k) c0).isSome
  boundary_tongues : ∀ k ∈ sample,
    tonguesAt w c0 (concreteTime k) =
      pinTrajectory
        (fun n => actionOf
          (Echo.configSnap machine echoEntry initialRegister cells n))
        initialTongues k

private theorem nodup_map_of_fibre
    {α β γ : Type} (xs : List α)
    (f : α → β) (g : α → γ)
    (hfibre : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → g x = g y)
    (hnd : (xs.map g).Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      constructor
      · intro hmem
        obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
        have hgy : g x = g y :=
          hfibre x List.mem_cons_self y
            (List.mem_cons_of_mem _ hy) hfy.symm
        exact hnd.1 (List.mem_map.mpr ⟨y, hy, hgy.symm⟩)
      · exact ih
          (fun a ha b hb => hfibre a (List.mem_cons_of_mem _ ha)
            b (List.mem_cons_of_mem _ hb))
          hnd.2

/-- **Corrected bridge theorem at cascade boundaries.**  Any valid overwrite
compilation inherits the unconditional strict-base bound. -/
theorem strict_boundary_bound_of_overwriteCompilation
    {w : Wiring} {N : Nat} {c0 : Nat × Tongues}
    {sample : List Nat} {globalLo globalHi : Nat}
    (comp : OverwriteEchoCompilation w N c0 sample
      globalLo globalHi)
    (hnd : (sample.map fun k =>
      VectorCount.restrict N
        (tonguesAt w c0 (comp.concreteTime k))).Nodup) :
    Echo.blockCoreEighth sample.length ≤
      Echo.blockCoreEighth 2 *
        (Echo.blockCoreEighth (2*N) *
          (Echo.blockCoreEighth (4*N + 2) * 2^(7*N+18))) := by
  let cfg := Echo.configSnap comp.machine comp.echoEntry
    comp.initialRegister comp.cells
  let boundary := pinTrajectory
    (fun n => comp.actionOf (cfg n)) comp.initialTongues
  have hndBoundary : (sample.map boundary).Nodup := by
    apply nodup_map_of_fibre sample boundary
      (fun k => VectorCount.restrict N
        (tonguesAt w c0 (comp.concreteTime k)))
    · intro i hi j hj heq
      have hiEq := comp.boundary_tongues i hi
      have hjEq := comp.boundary_tongues j hj
      dsimp [boundary, cfg] at heq
      rw [hiEq, hjEq]
      exact congrArg (VectorCount.restrict N) heq
    · exact hnd
  exact Echo.finite_echo_overwrite_trace_bound
    comp.machine comp.echoEntry comp.initialRegister
    comp.run comp.initialRegister_wellFormed
    N globalLo globalHi comp.cells comp.slots
    comp.entries sample comp.frame
    comp.cells_length comp.slots_length
    comp.entries_nodup comp.entries_length
    comp.entry_cover comp.echo_range comp.partner_cover
    comp.actionOf comp.initialTongues (by
      simpa [boundary, cfg] using hndBoundary)

/-- Strict-base state law restricted to concrete cascade-boundary samples. -/
def StrictBoundaryStateLaw : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3*N ∧ q < 3*N) →
    ∀ (c0 : Nat × Tongues) (sample : List Nat),
      ∀ globalLo globalHi,
      ∀ comp : OverwriteEchoCompilation w N c0 sample
        globalLo globalHi,
      (sample.map fun k =>
        VectorCount.restrict N
          (tonguesAt w c0 (comp.concreteTime k))).Nodup →
      Echo.blockCoreEighth sample.length ≤
        Echo.blockCoreEighth 2 *
          (Echo.blockCoreEighth (2*N) *
            (Echo.blockCoreEighth (4*N + 2) * 2^(7*N+18)))

/-- The corrected boundary state law follows immediately from the overwrite
compilation interface. -/
theorem strictBoundaryStateLaw : StrictBoundaryStateLaw := by
  intro w N hN c0 sample globalLo globalHi comp hnd
  exact strict_boundary_bound_of_overwriteCompilation comp hnd

end GeneralN
