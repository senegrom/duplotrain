import TwoHistoryUnionCharge

/-!
# Sharper two-history charge when the first reflector is a stay reflector

The general `preservedTwoHistoryCore_length_le_N_add_three` loses one unit
because a flip reflector has a facing-mouth passage which is not part of its
reusable support.  A stay reflector has no such omitted passage: its entire
exploration is reusable.  Hence the same disjoint-coordinate argument gives
`N+2` rather than `N+3`.
-/

namespace GeneralN

/-- If the first manufactured reflector is a stay reflector, the preserved
two-construction history costs at most `N+2`. -/
theorem ManufacturedStayReflector.preservedTwoHistoryCore_length_le_N_add_two
    {w : Wiring} {N g e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    (R : ManufacturedStayReflector w g e)
    (B : ManufacturedReflector w e g)
    (hbase : B.baseState = (ManufacturedReflector.stay R).activatedState)
    (hbaseGrooves :
      PathGrooves (ManufacturedReflector.stay R).toSupported.paths
        B.baseState)
    (hpreGrooves :
      PathGrooves (ManufacturedReflector.stay R).toSupported.paths
        B.preReturn.2) :
    ((ManufacturedReflector.stay R).preservedTwoHistoryCore B N).length ≤
      N + 2 := by
  let A : ManufacturedReflector w g e := .stay R
  have hboundary :
      VectorCount.restrict N A.activatedState ∈
        B.writerConstructionHistory N := by
    apply List.mem_append_left
    simp [rawFirstWriterHistory, restrictedTonguesAt,
      tonguesAt, stepN, hbase, A]
  have hcharge :=
    A.reusable_add_second_first_writers_le
      hN B hbaseGrooves hpreGrooves
  have hexact : A.exploration.length = A.reusableSwitches.length := by
    simp [A, ManufacturedReflector.exploration,
      ManufacturedReflector.reusableSwitches]
  unfold ManufacturedReflector.preservedTwoHistoryCore
  rw [List.length_append, List.length_erase_of_mem hboundary,
    A.sharpHistoryCore_length,
    B.writerConstructionHistory_length]
  omega

end GeneralN
