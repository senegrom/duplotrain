import TwoHistoryUnionCharge

/-!
# The sole contact obstruction to the coefficient-one count

The two-history union argument already pays every genuinely changing first
old-support contact with only two vectors beyond `contactHistory`.  An
unchanged contact is likewise two-vector unless it is literally the forward
passage of the old selected route.

This file packages that remaining case as one semantic law and proves its
exact quantitative payoff.  Since `contactHistory` has length at most
`N + 3`, a two-vector tail gives `N + 5` immediately.
-/

namespace GeneralN

/-- The only local contact statement not already discharged by
`TwoHistoryUnionCharge`: an unchanged first contact which follows the old
selected route forward still has a two-vector novelty cover over the exact
contact history. -/
def FacingForwardContactTwoNoveltyLaw : Prop :=
  ∀ (w : Wiring) (N g e : Nat)
      (A : ManufacturedReflector w g e)
      (B : ManufacturedReflector w e g)
      (C : SecondHistorySupportContact w A B)
      (next : Tongues),
    arrive C.contactState C.fresh.1 = (C.fresh.2, next) →
    next (C.fresh.1 / 3) = C.contactState (C.fresh.1 / 3) →
    C.fresh ∈ A.orientedRoute C.contactState →
    ∀ times : List Nat,
      NoveltyCoverOn w N (e, B.baseState)
        times (C.contactHistory N) 2

/-- Once the unchanged-forward residue is supplied, every possible first
old-support contact has the two-vector cover.

Changing contacts use `changed_contact_two_novelty`.  For an unchanged
contact, `facing_contact_two_novelty_or_forward` either gives the cover
already or exposes exactly the forward passage handled by the law. -/
theorem SecondHistorySupportContact.contact_two_novelty_of_forward_law
    (hlaw : FacingForwardContactTwoNoveltyLaw)
    {w : Wiring} {N g e : Nat}
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (times : List Nat) :
    NoveltyCoverOn w N (e, B.baseState)
      times (C.contactHistory N) 2 := by
  obtain ⟨next, harrive, _hpost⟩ := C.contact_post_mem (N := N)
  by_cases hchanged :
      next (C.fresh.1 / 3) ≠ C.contactState (C.fresh.1 / 3)
  · exact C.changed_contact_two_novelty harrive hchanged times
  · have hunchanged :
        next (C.fresh.1 / 3) = C.contactState (C.fresh.1 / 3) :=
      Classical.not_not.mp hchanged
    rcases C.facing_contact_two_novelty_or_forward
        harrive hunchanged times with hcover | hforward
    · exact hcover
    · exact hlaw w N g e A B C next
        harrive hunchanged hforward times

/-- Two post-contact novelty vectors above the exact contact history give the
sharp local `N + 5` count. -/
theorem SecondHistorySupportContact.prefix_then_two_novelty_distinct_le_N_add_five
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState)
    (times : List Nat)
    (hcover : NoveltyCoverOn w N (e, B.baseState)
      times (C.contactHistory N) 2)
    (hnd : (times.map
      (restrictedTonguesAt w N (e, B.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  have hcount := noveltyCoverOn_distinct_count hcover hnd
  have hhistory := C.contactHistory_length_le_N_add_three hN hbase
  omega

/-- Quantitative endpoint of the reduction: the single unchanged-forward law
implies the `N + 5` bound for every first-support-contact trajectory. -/
theorem SecondHistorySupportContact.distinct_le_N_add_five_of_forward_law
    (hlaw : FacingForwardContactTwoNoveltyLaw)
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {A : ManufacturedReflector w g e}
    {B : ManufacturedReflector w e g}
    (C : SecondHistorySupportContact w A B)
    (hbase : B.baseState = A.activatedState)
    (times : List Nat)
    (hnd : (times.map
      (restrictedTonguesAt w N (e, B.baseState))).Nodup) :
    times.length ≤ N + 5 := by
  apply C.prefix_then_two_novelty_distinct_le_N_add_five
    hN hbase times
  · exact C.contact_two_novelty_of_forward_law hlaw times
  · exact hnd

end GeneralN
