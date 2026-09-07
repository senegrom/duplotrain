import PartialSecondRunSharp

/-!
# Historical corners of a completed protected repair

Every protected repair prefix ends in the activated or pre-return state.
Replay a completed repair at its final state, then use the restored pair's
four-corner orbit. The final state and its protected action are historical;
the caller supplies coverage for the other two corners.
-/

namespace GeneralN

/-- **Shared core of the completed protected repair.**  After the repair the
run stays on the four action corners of the restored pair.  Two corners
(the final vector and its `B`-action) are always historical; whenever the
other two lie in `history ++ fresh`, so does every sampled vector. -/
theorem ManufacturedReflector.completed_protected_route_cover
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (hA : PathGrooves A.toSupported.paths B.baseState)
    (hB : PathGrooves B.toSupported.paths B.activatedState)
    {finalState : Tongues}
    (hrepair : PhysicalTrace w (g, B.activatedState)
      (A.orientedRoute B.activatedState)
      (A.orientedFinish B.activatedState, finalState))
    (hAfinal : PathGrooves A.toSupported.paths finalState)
    (hBfinal : PathGrooves B.toSupported.paths finalState)
    (history fresh : List (List Bool))
    (hinitialHistorical : VectorCount.restrict N B.activatedState ∈ history)
    (hpreHistorical : VectorCount.restrict N B.preReturn.2 ∈ history)
    (hAcovered : VectorCount.restrict N
      (A.toSupported.action.apply finalState) ∈ history ++ fresh)
    (hBAcovered : VectorCount.restrict N
      (B.toSupported.action.apply
        (A.toSupported.action.apply finalState)) ∈ history ++ fresh)
    (times : List Nat)
    (hlive : ∀ k ∈ times,
      (stepN w k (g, B.activatedState)).isSome) :
    ∀ k ∈ times,
      restrictedTonguesAt w N (g, B.activatedState) k ∈ history ++ fresh := by
  have hfinalGrooved := hrepair.grooved_of_switchSimple
    (A.orientedRoute_simple B.activatedState)
  let L := (A.orientedRoute B.activatedState).length
  let endpoint : Nat × Tongues :=
    (A.orientedFinish B.activatedState, finalState)
  have hrepairReach : stepN w L (g, B.activatedState) =
      some endpoint := by
    simpa [L, endpoint] using hrepair.sound
  have hpairReach : stepN w L (g, finalState) = some endpoint := by
    simpa [L, endpoint] using (hrepair.replay_grooved finalState hfinalGrooved).sound
  have hprefixPhase := A.repair_prefix_two_phase B hA hB
    hrepair (A.orientedRoute_simple B.activatedState)
    (by intro passage hp; exact hp) hBfinal
  have hrelation := A.repair_prefix_contact_eq_activated_or_preReturn B hA hB
    hrepair (A.orientedRoute_simple B.activatedState) (fun _ hp => hp) hBfinal
  have ⟨hfinalHistorical, hBfinalHistorical⟩ :
      VectorCount.restrict N finalState ∈ history ∧
      VectorCount.restrict N (B.toSupported.action.apply finalState) ∈ history := by
    rcases hrelation with rfl | rfl
    · exact ⟨hinitialHistorical, by rwa [← B.preReturn_eq_action_activated]⟩
    · exact ⟨hpreHistorical, by simpa [B.preReturn_eq_action_activated,
        B.toSupported.action.involutive] using hinitialHistorical⟩
  have hcornerCover : ∀ phase ∈ manufacturedPairActionCorners A B finalState,
      VectorCount.restrict N phase ∈ history ++ fresh := by
    intro phase hp
    simp only [manufacturedPairActionCorners, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact List.mem_append_left _ hfinalHistorical
    · exact hAcovered
    · exact List.mem_append_left _ hBfinalHistorical
    · exact hBAcovered
  refine cover_of_phase_orbit hrepairReach (fun d hd => by
    rw [← tonguesAt_add_of_reaches hpairReach (Option.isSome_iff_exists.mp hd)]
    exact manufactured_pair_all_time_action_corners_tongues A B finalState hAfinal hBfinal _)
    hcornerCover hlive ?_
  intro k hk hkpre
  obtain ⟨port, phase, hrun, hphase⟩ := hprefixPhase k (Nat.le_of_lt hkpre)
  rw [show restrictedTonguesAt w N (g, B.activatedState) k =
    VectorCount.restrict N phase by simp [restrictedTonguesAt, tonguesAt, hrun]]
  rcases hphase with rfl | rfl
  · exact hinitialHistorical
  · exact hfinalHistorical

end GeneralN
