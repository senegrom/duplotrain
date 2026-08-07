import SupportBound

/-!
# Support and tokens determine the register state

A jump edge is occupied when at least one endpoint is confirmed, and `s` is a
token endpoint when `s` is unconfirmed while `bar s` is confirmed.  Therefore

    confirmed s  ↔  occupied s ∧ not token s.

It follows that the occupied-support predicate together with the token-end
predicate determines every register, hence every finite register snapshot.
This turns state recurrence questions into questions about finite token motion
on the monotone occupied support.
-/

namespace Echo

variable (m : Machine) (e : Nat → Nat) (r0 : Nat → Nat)

/-- Confirmation is exactly occupancy at the non-token end. -/
theorem confirmed_iff_occupied_not_token (k s : Nat) :
    Confirmed m e r0 k s ↔
      Occupied m e r0 k s ∧ ¬ TokenEnd m e r0 k s := by
  constructor
  · intro hc
    exact ⟨Or.inl hc, fun ht => ht.1 hc⟩
  · rintro ⟨ho, hnt⟩
    rcases ho with hc | hb
    · exact hc
    · by_contra hnc
      exact hnt ⟨hnc, hb⟩

/-- Pointwise equality of occupied support and token ends forces equality of
one register. -/
theorem register_eq_of_support_token_eq
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    {i j C : Nat}
    (hocc : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (htok : ∀ s, TokenEnd m e r0 i s ↔ TokenEnd m e r0 j s) :
    reg m e r0 i C = reg m e r0 j C := by
  let s := reg m e r0 i C
  have hcell : m.cellOf s = C := by
    exact reg_cell m e r0 hr0 i C
  have hci : Confirmed m e r0 i s := by
    unfold Confirmed
    rw [hcell]
  have hoi : Occupied m e r0 i s :=
    (confirmed_iff_occupied_not_token m e r0 i s).mp hci |>.1
  have hnti : ¬ TokenEnd m e r0 i s :=
    (confirmed_iff_occupied_not_token m e r0 i s).mp hci |>.2
  have hoj : Occupied m e r0 j s := (hocc s).mp hoi
  have hntj : ¬ TokenEnd m e r0 j s := by
    intro htj
    exact hnti ((htok s).mpr htj)
  have hcj : Confirmed m e r0 j s :=
    (confirmed_iff_occupied_not_token m e r0 j s).mpr ⟨hoj, hntj⟩
  unfold Confirmed at hcj
  rw [hcell] at hcj
  exact hcj.symm

/-- Pointwise equality of support and tokens determines any listed snapshot. -/
theorem snap_eq_of_support_token_eq
    (hr0 : ∀ c, m.cellOf (r0 c) = c)
    (cells : List Nat) {i j : Nat}
    (hocc : ∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s)
    (htok : ∀ s, TokenEnd m e r0 i s ↔ TokenEnd m e r0 j s) :
    snap m e r0 cells i = snap m e r0 cells j := by
  unfold snap
  apply List.map_congr_left
  intro C _
  exact register_eq_of_support_token_eq m e r0 hr0 hocc htok

/-- Equality of registers conversely gives equality of confirmation, support,
and token predicates. -/
theorem support_token_eq_of_register_eq
    {i j : Nat} (hreg : ∀ C, reg m e r0 i C = reg m e r0 j C) :
    (∀ s, Occupied m e r0 i s ↔ Occupied m e r0 j s) ∧
    (∀ s, TokenEnd m e r0 i s ↔ TokenEnd m e r0 j s) := by
  have hconf : ∀ s, Confirmed m e r0 i s ↔ Confirmed m e r0 j s := by
    intro s
    unfold Confirmed
    rw [hreg]
  constructor
  · intro s
    unfold Occupied
    rw [hconf s, hconf (m.bar s)]
  · intro s
    unfold TokenEnd
    rw [hconf s, hconf (m.bar s)]

end Echo
