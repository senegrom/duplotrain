import EchoOverwriteFibre
import ObservedConfigurationFibre

/-!
# Two physical states per configuration and cascade-prefix position

A physical tongue vector inside a cascade is a deterministic prefix overwrite
of the boundary tongue vector.  Fixing both the finite echo configuration and
the prefix length therefore preserves the two-state recurrent fibre bound.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- **Physical prefix fibre theorem.** -/
theorem physical_prefix_fibre_length_le_two
    (hrun : IsRun m e r0)
    (cells : List Nat)
    (hpartnerCover : ∀ k,
      m.star (m.cellOf (e k)) ∈ cells)
    (actionOf : Nat × List Nat → List Nat)
    (t0 : GeneralN.Tongues)
    (owner prefix : Nat → Nat)
    (observed : Nat → GeneralN.Tongues)
    (q : Nat × List Nat) (r : Nat)
    (sample : List Nat)
    (hsame : ∀ x ∈ sample,
      configSnap m e r0 cells (owner x) = q)
    (hprefix : ∀ x ∈ sample, prefix x = r)
    (hobserve : ∀ x ∈ sample,
      observed x =
        GeneralN.pinList
          ((actionOf (configSnap m e r0 cells (owner x))).take
            (prefix x))
          (GeneralN.pinTrajectory
            (fun n => actionOf (configSnap m e r0 cells n))
            t0 (owner x)))
    (hnd : (sample.map observed).Nodup) :
    sample.length ≤ 2 := by
  let cfg := configSnap m e r0 cells
  let boundary := GeneralN.pinTrajectory
    (fun n => actionOf (cfg n)) t0
  let times := sample.map owner
  let observeR : (Nat × List Nat) →
      GeneralN.Tongues → GeneralN.Tongues :=
    fun config tongue =>
      GeneralN.pinList ((actionOf config).take r) tongue
  have hsameTimes : ∀ k ∈ times, cfg k = q := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
    exact hsame x hx
  have hlistEq :
      times.map (fun k => observeR (cfg k) (boundary k)) =
        sample.map observed := by
    dsimp [times]
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    have hp := hprefix x hx
    have ho := hobserve x hx
    dsimp [observeR, boundary, cfg]
    rw [← ho, hp]
  have hndTimes :
      (times.map (fun k => observeR (cfg k) (boundary k))).Nodup := by
    rw [hlistEq]
    exact hnd
  have htwo := GeneralN.same_config_observation_fibre_length_le_two
    cfg actionOf t0
    (configSnap_replays m e r0 hrun cells hpartnerCover)
    observeR q times hsameTimes (by
      simpa [boundary] using hndTimes)
  simpa [times] using htwo

end Echo
