import StateLaw
import FiniteFrameSwitchCorollary

/-!
# The concrete-to-echo bridge interface

The strict-base counting theorem is now unconditional for every finite echo
frame.  This file isolates exactly what the concrete lazy-point compilation
must provide for one finite list of observed train times.

The clock is allowed to compress many physical train steps into one echo
ascent.  The replay field says equal register snapshots at two sampled echo
times force equal concrete tongue vectors.  Consequently pairwise-distinct
concrete vectors inject into pairwise-distinct echo snapshots, and the
unconditional finite-frame theorem applies.
-/

namespace GeneralN

/-- A finite sampled concrete run compiled into an echo-machine frame. -/
structure EchoCompilation
    (w : Wiring) (N : Nat) (c0 : Nat × Tongues)
    (sample : List Nat) (globalLo globalHi : Nat) where
  machine : Echo.Machine
  entries : Nat → Nat
  initial : Nat → Nat
  cells : List Nat
  slots : List Nat
  clock : Nat → Nat
  run : Echo.IsRun machine entries initial
  initial_wellFormed : ∀ c, machine.cellOf (initial c) = c
  frame : Echo.CompleteFiniteEpochFrame machine entries initial
    globalLo globalHi cells slots
  cells_length : cells.length ≤ N
  slots_length : slots.length ≤ 2 * N
  live : ∀ k ∈ sample, (stepN w k c0).isSome
  clock_range : ∀ k ∈ sample,
    globalLo ≤ clock k ∧ clock k ≤ globalHi
  replay : ∀ i ∈ sample, ∀ j ∈ sample,
    Echo.snap machine entries initial cells (clock i) =
      Echo.snap machine entries initial cells (clock j) →
    VectorCount.restrict N (tonguesAt w c0 i) =
      VectorCount.restrict N (tonguesAt w c0 j)

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

/-- **Bridge theorem.**  Any valid concrete echo compilation inherits the
unconditional strict-base bound. -/
theorem strict_bound_of_echoCompilation
    {w : Wiring} {N : Nat} {c0 : Nat × Tongues}
    {sample : List Nat} {globalLo globalHi : Nat}
    (comp : EchoCompilation w N c0 sample globalLo globalHi)
    (hnd : (sample.map fun k =>
      VectorCount.restrict N (tonguesAt w c0 k)).Nodup) :
    Echo.blockCoreEighth sample.length ≤
      Echo.blockCoreEighth (4*N + 2) * 2^(7*N+18) := by
  have hndAtConcreteTimes :
      (sample.map fun k =>
        Echo.snap comp.machine comp.entries comp.initial
          comp.cells (comp.clock k)).Nodup := by
    exact nodup_map_of_fibre sample
      (fun k => Echo.snap comp.machine comp.entries comp.initial
        comp.cells (comp.clock k))
      (fun k => VectorCount.restrict N (tonguesAt w c0 k))
      (fun i hi j hj hs => comp.replay i hi j hj hs)
      hnd
  have hndEchoTimes :
      ((sample.map comp.clock).map
        (Echo.snap comp.machine comp.entries comp.initial comp.cells)).Nodup := by
    simpa [List.map_map, Function.comp_def] using hndAtConcreteTimes
  have htimeRange : ∀ t ∈ sample.map comp.clock,
      globalLo ≤ t ∧ t ≤ globalHi := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ht
    exact comp.clock_range k hk
  have hbound := Echo.finiteFrame_atMost_N_strict_bound
    comp.machine comp.entries comp.initial
    comp.run comp.initial_wellFormed
    N globalLo globalHi comp.cells comp.slots
    (sample.map comp.clock) comp.frame
    comp.cells_length comp.slots_length htimeRange hndEchoTimes
  simpa using hbound

/-- The strict-base replacement for the open linear `StateLaw`. -/
def StrictBaseStateLaw : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (c0 : Nat × Tongues) (sample : List Nat),
      (∀ k ∈ sample, (stepN w k c0).isSome) →
      (sample.map fun k =>
        VectorCount.restrict N (tonguesAt w c0 k)).Nodup →
      Echo.blockCoreEighth sample.length ≤
        Echo.blockCoreEighth (4*N + 2) * 2^(7*N+18)

/-- Every finite live sample admits a concrete echo compilation.  Proving
this proposition from `Wiring` is the remaining static/dynamical bridge. -/
def EveryFiniteRunCompiles : Prop :=
  ∀ (w : Wiring) (N : Nat),
    (∀ p q, w.link p = some q → p < 3 * N ∧ q < 3 * N) →
    ∀ (c0 : Nat × Tongues) (sample : List Nat),
      (∀ k ∈ sample, (stepN w k c0).isSome) →
      ∃ globalLo globalHi,
        EchoCompilation w N c0 sample globalLo globalHi

/-- Once the concrete forest compilation is supplied, the strict-base state
law follows with no further dynamical hypothesis. -/
theorem strictBaseStateLaw_of_compilation
    (hcompile : EveryFiniteRunCompiles) : StrictBaseStateLaw := by
  intro w N hN c0 sample hlive hnd
  obtain ⟨globalLo, globalHi, comp⟩ :=
    hcompile w N hN c0 sample hlive
  exact strict_bound_of_echoCompilation comp hnd

end GeneralN
