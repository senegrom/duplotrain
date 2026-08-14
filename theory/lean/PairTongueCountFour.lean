import TrackThetaAllTime
import PairTongueCountSharp

/-!
# Tongue counts from the absolute phase laws

The four-phase capstone (`manufactured_flip_pair_all_time_four_phase`) and
the compatible-orbit law make every flip/flip and every avoiding reflector
pair cost **four** tongue vectors flat.  Only the stay/flip contact
geometries still pay a travel-shaped price (`8*N+1`), so the reflector-pair
count drops from `12*N+3` to `8*N+4`, and the complete-repair branch from
`13*N+3` to `9*N+4`.
-/

namespace GeneralN

private theorem pairfour_nodup_of_map_nodup
    {α β : Type} [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β]
    (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      rw [List.nodup_cons]
      constructor
      · intro hx
        apply hnd.1
        exact List.mem_map.mpr ⟨x, hx, rfl⟩
      · exact ih hnd.2

private theorem pairfour_nodup_filter_nat (p : Nat → Bool) :
    ∀ {xs : List Nat}, xs.Nodup → (xs.filter p).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.nodup_cons]
          exact ⟨fun hm => hnd.1 (List.mem_filter.mp hm).1, ih hnd.2⟩
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem pairfour_nodup_map_filter
    {α : Type} [BEq α] [LawfulBEq α]
    {f : Nat → α} (p : Nat → Bool) :
    ∀ {xs : List Nat},
      (xs.map f).Nodup → ((xs.filter p).map f).Nodup := by
  intro xs
  induction xs with
  | nil => intro _; simp
  | cons x rest ih =>
      intro hnd
      simp only [List.map_cons, List.nodup_cons] at hnd
      cases hp : p x with
      | true =>
          simp only [List.filter_cons, hp, if_true, List.map_cons,
            List.nodup_cons]
          constructor
          · intro hm
            obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
            apply hnd.1
            exact List.mem_map.mpr
              ⟨y, (List.mem_filter.mp hy).1, hfy⟩
          · exact ih hnd.2
      | false =>
          simp only [List.filter_cons, hp]
          exact ih hnd.2

private theorem pairfour_lt_ge_partition (L : Nat) :
    ∀ xs : List Nat,
      (xs.filter (fun k => decide (k < L))).length +
        (xs.filter (fun k => decide (L ≤ k))).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons k rest ih =>
      by_cases hk : k < L
      · have hnot : ¬ L ≤ k := by omega
        simp [hk, hnot]
        omega
      · have hge : L ≤ k := by omega
        simp [hk, hge]
        omega

/-- A mutually avoiding manufactured pair exposes at most four distinct
restricted tongue vectors — no liveness hypothesis needed. -/
theorem manufactured_pair_avoid_distinct_le_four
    {w : Wiring} {N g e : Nat}
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (hAB : A.toSupported.action.Avoids B.toSupported.paths)
    (hBA : B.toSupported.action.Avoids A.toSupported.paths)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ 4 := by
  have hcover : NoveltyCoverOn w N (g, state) times [] 4 := by
    refine ⟨[VectorCount.restrict N state,
      VectorCount.restrict N (A.toSupported.action.apply state),
      VectorCount.restrict N
        (B.toSupported.action.apply (A.toSupported.action.apply state)),
      VectorCount.restrict N
        (A.toSupported.action.apply
          (B.toSupported.action.apply
            (A.toSupported.action.apply state)))],
      by simp, ?_⟩
    intro k hk
    have hmem := manufactured_pair_all_time_four_phase_tongues
      A B state hA hB hAB hBA k
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    unfold restrictedTonguesAt
    rcases hmem with h | h | h | h
    · rw [h]
      simp
    · rw [h]
      simp
    · rw [h]
      simp
    · rw [h]
      simp
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  simpa using hcount

/-- Reflector-pair tongue count, sharpened by the absolute phase laws:
`8*N+4` distinct restricted tongue vectors, with the stay/flip contact
geometries as the only travel-shaped contributors. -/
theorem manufactured_pair_tongue_vector_count_eight_succ_four
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k (g, state)).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N (g, state))).Nodup) :
    times.length ≤ 8 * N + 4 := by
  classical
  have hnd' : (times.map (fun k =>
      VectorCount.restrict N (tonguesAt w (g, state) k))).Nodup := by
    exact hnd
  cases A with
  | stay SA =>
      cases B with
      | stay SB =>
          have hc := manufactured_pair_avoid_distinct_le_four
            (.stay SA) (.stay SB) state hA hB
              (by trivial) (by trivial) times hnd
          omega
      | flip FB =>
          change PathGrooves
            [SA.runway, [(SA.mouth, SA.arm)]] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          by_cases hBA : (LocalAction.flip FB.actionSwitch).Avoids
              [SA.runway, [(SA.mouth, SA.arm)]]
          · have hc := manufactured_pair_avoid_distinct_le_four
              (.stay SA) (.flip FB) state hA hB
                (by trivial) hBA times hnd
            omega
          · have hcontact := contact_of_not_avoids_flip hBA
            have hlocal := manufactured_flip_then_stay_within_eight
              hN FB SA state hB hA hcontact
            have hlocal' : EventuallyPeriodicWithin w
                (e, (ManufacturedReflector.stay SA).toSupported.action.apply state)
                (8 * N) := by
              simpa [ManufacturedReflector.toSupported,
                ManufacturedStayReflector.toSupported, LocalAction.apply]
                using hlocal
            have hc := ManufacturedReflector.traversal_then_lasso_distinct_le_succ
              (ManufacturedReflector.stay SA) state hA hlocal'
                times hlive hnd
            omega
  | flip FA =>
      cases B with
      | stay SB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves
            [SB.runway, [(SB.mouth, SB.arm)]] state at hB
          by_cases hAB : (LocalAction.flip FA.actionSwitch).Avoids
              [SB.runway, [(SB.mouth, SB.arm)]]
          · have hc := manufactured_pair_avoid_distinct_le_four
              (.flip FA) (.stay SB) state hA hB
                hAB (by trivial) times hnd
            omega
          · have hcontact := contact_of_not_avoids_flip hAB
            have hlocal := manufactured_flip_then_stay_within_eight
              hN FA SB state hA hB hcontact
            have hc := hlocal.tongue_vector_count times hlive hnd'
            omega
      | flip FB =>
          change PathGrooves [FA.runway, FA.candy] state at hA
          change PathGrooves [FB.runway, FB.candy] state at hB
          have hc := manufactured_flip_pair_distinct_le_four
            FA FB state hA hB times hnd
          omega

/-- The `8*N+4` pair count is inherited by every reached suffix of the
pair trajectory. -/
theorem manufactured_pair_reached_tongue_vector_count_eight_succ_four
    {w : Wiring} {N g e shift : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (A : ManufacturedReflector w g e)
    (B : ManufacturedReflector w e g)
    (state : Tongues)
    (hA : PathGrooves A.toSupported.paths state)
    (hB : PathGrooves B.toSupported.paths state)
    {middle : Nat × Tongues}
    (hreach : stepN w shift (g, state) = some middle)
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k middle).isSome)
    (hnd : (times.map
      (restrictedTonguesAt w N middle)).Nodup) :
    times.length ≤ 8 * N + 4 := by
  let lifted := times.map (fun k => shift + k)
  have hliftLive : ∀ j ∈ lifted,
      (stepN w j (g, state)).isSome := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
    have hkLive := hlive k hk
    rw [stepN_add, hreach]
    exact hkLive
  have hvector : lifted.map
      (restrictedTonguesAt w N (g, state)) =
      times.map (restrictedTonguesAt w N middle) := by
    dsimp [lifted]
    rw [List.map_map]
    apply List.map_congr_left
    intro k hk
    have hkLive := hlive k hk
    cases htail : stepN w k middle with
    | none =>
        rw [htail] at hkLive
        simp at hkLive
    | some finish =>
        have hshift := tonguesAt_add_of_reaches hreach ⟨finish, htail⟩
        unfold restrictedTonguesAt
        exact congrArg (VectorCount.restrict N) hshift
  have hliftNodup :
      (lifted.map (restrictedTonguesAt w N (g, state))).Nodup := by
    rw [hvector]
    exact hnd
  have hbound := manufactured_pair_tongue_vector_count_eight_succ_four
    hN A B state hA hB lifted hliftLive hliftNodup
  simpa [lifted] using hbound

end GeneralN
