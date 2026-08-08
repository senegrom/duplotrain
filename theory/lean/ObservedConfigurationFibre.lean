import TwoStateConfigurationFibre

/-!
# Deterministic observations preserve the two-state fibre bound

For a fixed abstract configuration, any observation obtained by applying a
fixed function to the boundary tongue vector also has at most two distinct
values.  The intended observation is a prefix of that configuration's
cascade overwrite word, which represents an intermediate physical train
state inside the cascade.
-/

namespace GeneralN

/-- Among three visits to one configuration, any deterministic observation of
the configuration and boundary vector coincides at some pair. -/
theorem three_same_config_some_observations_equal
    {α β : Type} (cfg : Nat → α) (actionOf : α → List Nat)
    (t0 : Tongues)
    (hreplay : Replays cfg)
    (observe : α → Tongues → β)
    {a b c : Nat}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcfgab : cfg a = cfg b)
    (hcfgac : cfg a = cfg c) :
    observe (cfg a)
        (pinTrajectory (fun n => actionOf (cfg n)) t0 a) =
        observe (cfg b)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 b) ∨
      observe (cfg a)
        (pinTrajectory (fun n => actionOf (cfg n)) t0 a) =
        observe (cfg c)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 c) ∨
      observe (cfg b)
        (pinTrajectory (fun n => actionOf (cfg n)) t0 b) =
        observe (cfg c)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 c) := by
  have hpairs := three_same_config_some_tongues_equal
    cfg actionOf t0 hreplay hab hac hbc hcfgab hcfgac
  rcases hpairs with h | h | h
  · left
    calc
      observe (cfg a)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 a)
          = observe (cfg b)
              (pinTrajectory (fun n => actionOf (cfg n)) t0 a) := by
                rw [hcfgab]
      _ = observe (cfg b)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 b) :=
            congrArg (observe (cfg b)) h
  · right
    left
    calc
      observe (cfg a)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 a)
          = observe (cfg c)
              (pinTrajectory (fun n => actionOf (cfg n)) t0 a) := by
                rw [hcfgac]
      _ = observe (cfg c)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 c) :=
            congrArg (observe (cfg c)) h
  · right
    right
    have hcfgbc : cfg b = cfg c := hcfgab.symm.trans hcfgac
    calc
      observe (cfg b)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 b)
          = observe (cfg c)
              (pinTrajectory (fun n => actionOf (cfg n)) t0 b) := by
                rw [hcfgbc]
      _ = observe (cfg c)
          (pinTrajectory (fun n => actionOf (cfg n)) t0 c) :=
            congrArg (observe (cfg c)) h

/-- **Observed two-state fibre theorem.**  Pairwise-distinct deterministic
observations contain at most two visits to one configuration. -/
theorem same_config_observation_fibre_length_le_two
    {α β : Type} (cfg : Nat → α) (actionOf : α → List Nat)
    (t0 : Tongues)
    (hreplay : Replays cfg)
    (observe : α → Tongues → β)
    (q : α) (times : List Nat)
    (hsame : ∀ k ∈ times, cfg k = q)
    (hnd : (times.map fun k =>
      observe (cfg k)
        (pinTrajectory (fun n => actionOf (cfg n)) t0 k)).Nodup) :
    times.length ≤ 2 := by
  cases times with
  | nil => simp
  | cons a rest =>
      cases rest with
      | nil => simp
      | cons b rest' =>
          cases rest' with
          | nil => simp
          | cons c tail =>
              let observed := fun k =>
                observe (cfg k)
                  (pinTrajectory (fun n => actionOf (cfg n)) t0 k)
              have hndA := List.nodup_cons.mp hnd
              have hndB := List.nodup_cons.mp hndA.2
              have habState : observed a ≠ observed b := by
                intro h
                apply hndA.1
                exact List.mem_map.mpr
                  ⟨b, List.mem_cons_self, h.symm⟩
              have hacState : observed a ≠ observed c := by
                intro h
                apply hndA.1
                exact List.mem_map.mpr
                  ⟨c, List.mem_cons_of_mem _ List.mem_cons_self, h.symm⟩
              have hbcState : observed b ≠ observed c := by
                intro h
                apply hndB.1
                exact List.mem_map.mpr
                  ⟨c, List.mem_cons_self, h.symm⟩
              have hab : a ≠ b := by
                intro h
                apply habState
                exact congrArg observed h
              have hac : a ≠ c := by
                intro h
                apply hacState
                exact congrArg observed h
              have hbc : b ≠ c := by
                intro h
                apply hbcState
                exact congrArg observed h
              have hca := hsame a List.mem_cons_self
              have hcb := hsame b
                (List.mem_cons_of_mem _ List.mem_cons_self)
              have hcc := hsame c
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ List.mem_cons_self))
              have hpairs := three_same_config_some_observations_equal
                cfg actionOf t0 hreplay observe hab hac hbc
                (hca.trans hcb.symm) (hca.trans hcc.symm)
              dsimp [observed] at habState hacState hbcState hpairs
              rcases hpairs with h | h | h
              · exact False.elim (habState h)
              · exact False.elim (hacState h)
              · exact False.elim (hbcState h)

end GeneralN
