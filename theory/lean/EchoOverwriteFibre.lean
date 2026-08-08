import EchoConfiguration
import TwoStateConfigurationFibre

/-!
# Two concrete states per recurrent echo configuration

The finite echo configuration `(entry, register snapshot)` is deterministic
when the listed cells cover every partner register read by the run.  Therefore
the generic overwrite-fibre theorem applies directly: in a duplicate-free
sample of concrete tongue vectors, each fixed echo configuration occurs at
most twice.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Finite echo configurations replay equal futures. -/
theorem configSnap_replays
    (hrun : IsRun m e r0) (cells : List Nat)
    (hcover : ∀ k, m.star (m.cellOf (e k)) ∈ cells) :
    GeneralN.Replays (configSnap m e r0 cells) := by
  intro i j hcfg r
  exact configSnap_add_eq m e r0 hrun cells hcover hcfg r

/-- **Echo overwrite-fibre theorem.**  At most two pairwise-distinct concrete
tongue vectors can accompany one finite echo configuration. -/
theorem config_tongue_fibre_length_le_two
    (hrun : IsRun m e r0) (cells : List Nat)
    (hcover : ∀ k, m.star (m.cellOf (e k)) ∈ cells)
    (actionOf : Nat × List Nat → List Nat)
    (t0 : GeneralN.Tongues)
    (q : Nat × List Nat) (times : List Nat)
    (hsame : ∀ k ∈ times, configSnap m e r0 cells k = q)
    (hnd : (times.map
      (GeneralN.pinTrajectory
        (fun n => actionOf (configSnap m e r0 cells n)) t0)).Nodup) :
    times.length ≤ 2 := by
  exact GeneralN.same_config_fibre_length_le_two
    (configSnap m e r0 cells) actionOf t0
    (configSnap_replays m e r0 hrun cells hcover)
    q times hsame hnd

end Echo
