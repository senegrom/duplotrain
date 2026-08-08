import DeterministicOverwriteReturn

/-!
# At most two concrete states per deterministic configuration

The least-return theorem says that for three chronologically ordered visits to
one deterministic abstract configuration, the concrete vectors at the second
and third visits agree.  Therefore a list whose concrete vectors are
pairwise-distinct contains at most two times from any one configuration fibre.
-/

namespace GeneralN

/-- Among three distinct visits to one configuration, some two concrete
tongue vectors coincide. -/
theorem three_same_config_some_tongues_equal
    {α : Type} (cfg : Nat → α) (actionOf : α → List Nat)
    (t0 : Tongues)
    (hreplay : Replays cfg)
    {a b c : Nat}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcfgab : cfg a = cfg b)
    (hcfgac : cfg a = cfg c) :
    pinTrajectory (fun n => actionOf (cfg n)) t0 a =
        pinTrajectory (fun n => actionOf (cfg n)) t0 b ∨
      pinTrajectory (fun n => actionOf (cfg n)) t0 a =
        pinTrajectory (fun n => actionOf (cfg n)) t0 c ∨
      pinTrajectory (fun n => actionOf (cfg n)) t0 b =
        pinTrajectory (fun n => actionOf (cfg n)) t0 c := by
  have hcfgba : cfg b = cfg a := hcfgab.symm
  have hcfgbc : cfg b = cfg c := hcfgba.trans hcfgac
  have hcfgca : cfg c = cfg a := hcfgac.symm
  have hcfgcb : cfg c = cfg b := hcfgca.trans hcfgab
  by_cases hablt : a < b
  · by_cases hbclt : b < c
    · exact Or.inr (Or.inr
        (three_config_visits_second_eq_third
          cfg actionOf t0 hreplay hablt hbclt hcfgab hcfgac))
    · have hcb : c < b := by omega
      by_cases haclt : a < c
      · have h := three_config_visits_second_eq_third
          cfg actionOf t0 hreplay haclt hcb hcfgac hcfgab
        exact Or.inr (Or.inr h.symm)
      · have hca : c < a := by omega
        have h := three_config_visits_second_eq_third
          cfg actionOf t0 hreplay hca hablt hcfgca hcfgcb
        exact Or.inl h
  · have hba : b < a := by omega
    by_cases haclt : a < c
    · have h := three_config_visits_second_eq_third
        cfg actionOf t0 hreplay hba haclt hcfgba hcfgbc
      exact Or.inr (Or.inl h)
    · have hca : c < a := by omega
      by_cases hbclt : b < c
      · have h := three_config_visits_second_eq_third
          cfg actionOf t0 hreplay hbclt hca hcfgbc hcfgba
        exact Or.inr (Or.inl h.symm)
      · have hcb : c < b := by omega
        have h := three_config_visits_second_eq_third
          cfg actionOf t0 hreplay hcb hba hcfgcb hcfgca
        exact Or.inl h.symm

/-- **Two-state fibre theorem.**  A pairwise-distinct concrete tongue sample
contains at most two times carrying one fixed deterministic configuration. -/
theorem same_config_fibre_length_le_two
    {α : Type} (cfg : Nat → α) (actionOf : α → List Nat)
    (t0 : Tongues)
    (hreplay : Replays cfg)
    (q : α) (times : List Nat)
    (hsame : ∀ k ∈ times, cfg k = q)
    (hnd : (times.map
      (pinTrajectory (fun n => actionOf (cfg n)) t0)).Nodup) :
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
              have hndA := List.nodup_cons.mp hnd
              have hndB := List.nodup_cons.mp hndA.2
              let tongue :=
                pinTrajectory (fun n => actionOf (cfg n)) t0
              have habState : tongue a ≠ tongue b := by
                intro h
                apply hndA.1
                exact List.mem_map.mpr
                  ⟨b, List.mem_cons_self, h.symm⟩
              have hacState : tongue a ≠ tongue c := by
                intro h
                apply hndA.1
                exact List.mem_map.mpr
                  ⟨c, List.mem_cons_of_mem _ List.mem_cons_self, h.symm⟩
              have hbcState : tongue b ≠ tongue c := by
                intro h
                apply hndB.1
                exact List.mem_map.mpr
                  ⟨c, List.mem_cons_self, h.symm⟩
              have hab : a ≠ b := by
                intro h
                apply habState
                exact congrArg tongue h
              have hac : a ≠ c := by
                intro h
                apply hacState
                exact congrArg tongue h
              have hbc : b ≠ c := by
                intro h
                apply hbcState
                exact congrArg tongue h
              have hca := hsame a List.mem_cons_self
              have hcb := hsame b
                (List.mem_cons_of_mem _ List.mem_cons_self)
              have hcc := hsame c
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ List.mem_cons_self))
              have hpairs := three_same_config_some_tongues_equal
                cfg actionOf t0 hreplay hab hac hbc
                (hca.trans hcb.symm) (hca.trans hcc.symm)
              dsimp [tongue] at habState hacState hbcState hpairs
              rcases hpairs with h | h | h
              · exact False.elim (habState h)
              · exact False.elim (hacState h)
              · exact False.elim (hbcState h)

end GeneralN
