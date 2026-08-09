import SerialSerialPlacementClosure
import TripleSelfLinkSimpleCycleClosure
import TripleSelfLinkSimpleCycleTail

/-!
# Retaining the manufactured reflector in a serial window

The older serial-continuation interface retained the completed reverse but
erased the first-revisit object which caused it. This file repeats the raw
first-revisit split once and keeps that object. The simple-cycle alternatives
are discharged against the serially later repeated novelty, so the result is
an actual activated `ManufacturedReflector`, not a conditional certificate.
-/

namespace GeneralN

/-- Once an explicitly switch-simple cycle has reached its settled state, a
serially later repeated-writer novelty is impossible. This is the public,
reusable form of the cycle exclusion used inside `FiveFrameObstruction`. -/
theorem repeated_novel_after_simple_cycle_trace_false
    {w : Wiring} {N : Nat} {global : Nat × Tongues}
    {base laterOpen laterClose p : Nat} {u settled : Tongues}
    {cycle : List Passage}
    (hbase : stepN w base global = some (p, u))
    (htransient : PhysicalTrace w (p, u) cycle (p, settled))
    (hstable : PhysicalTrace w (p, settled) cycle (p, settled))
    (hsimple : SwitchSimple cycle)
    (hnonempty : cycle ≠ [])
    (G : RawLastWriterFrame w N global laterOpen laterClose)
    (H : RawRepeatedWriterNovelAt w N global laterClose)
    (hserial : base ≤ laterOpen) : False := by
  cases hcycle : cycle with
  | nil => exact hnonempty hcycle
  | cons passage rest =>
      rcases passage with ⟨head, x⟩
      have htransient' :
          PhysicalTrace w (p, u) ((head, x) :: rest) (p, settled) := by
        simpa [hcycle] using htransient
      have hstable' :
          PhysicalTrace w (p, settled) ((head, x) :: rest)
            (p, settled) := by
        simpa [hcycle] using hstable
      have hsimple' : SwitchSimple ((head, x) :: rest) := by
        simpa [hcycle] using hsimple
      have hhead : p = head := htransient'.head_arrive.1
      subst head
      let period := ((p, x) :: rest).length
      have hsettledAt :
          stepN w (base + period) global = some (p, settled) := by
        rw [stepN_add, hbase]
        simpa [period] using htransient'.sound
      have hcycleGrooved :
          PassagesGrooved settled ((p, x) :: rest) :=
        hstable'.grooved_of_switchSimple hsimple'
      have hcycleLinked : LinkedPassages w ((p, x) :: rest) :=
        hstable'.linked
      have hcycleFinal :
          w.link (lastPassageExit x rest) = some p :=
        hstable'.last_link
      by_cases hbeforeStable : laterClose < base + period
      · let i := laterOpen - base
        let j := laterClose - base
        have hi : i < period := by
          dsimp [i]
          omega
        have hj : j < period := by
          dsimp [j]
          omega
        have htimeI : base + i = laterOpen := by
          dsimp [i]
          omega
        have htimeJ : base + j = laterClose := by
          dsimp [j]
          omega
        have hsameWriter :
            rawWriterAt w global (base + i) =
              rawWriterAt w global (base + j) := by
          rw [htimeI, htimeJ]
          exact G.same_writer
        have hij := htransient'.rawWriterAt_add_injective
          hbase hsimple' hi hj hsameWriter
        have hopenClose : laterOpen = laterClose := by omega
        exact (Nat.ne_of_lt G.order) hopenClose
      · have hge : base + period ≤ laterClose :=
          Nat.le_of_not_gt hbeforeStable
        let d := laterClose + 1 - (base + period)
        have hsplit : laterClose + 1 = base + period + d := by
          dsimp [d]
          omega
        obtain ⟨port, hfuture⟩ :=
          grooved_cycle_forever_state w settled p x rest
            hcycleLinked hcycleGrooved hcycleFinal d
        have hpostAt : stepN w (laterClose + 1) global =
            some (port, settled) := by
          rw [hsplit, stepN_add, hsettledAt]
          exact hfuture
        have hvector :
            restrictedTonguesAt w N global (laterClose + 1) =
              restrictedTonguesAt w N global (base + period) := by
          simp [restrictedTonguesAt, tonguesAt, hpostAt, hsettledAt]
        apply H.2.2
        apply List.mem_map.mpr
        exact ⟨base + period, List.mem_range.mpr (by omega),
          hvector.symm⟩

end GeneralN
