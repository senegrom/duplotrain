import NoveltyAwareLassoOverlap

/-! Overlap-aware count for the sharpened `18*N` protected repair. -/

namespace GeneralN

/-- Two exact manufactured journeys followed by an `18*N` protected-repair
lasso expose at most `20*N+2` distinct restricted tongue vectors. -/
theorem two_manufacturing_journeys_then_repair_distinct_le_twenty
    {w : Wiring} {N e : Nat}
    (hN : ∀ p q, w.link p = some q →
      p < 3 * N ∧ q < 3 * N)
    {start : Nat × Tongues}
    (A : ManufacturedReflector w start.1 e)
    (B : ManufacturedReflector w e start.1)
    (stateA stateB : Tongues)
    (hbaseA : A.baseState = start.2)
    (hactivatedA : stateA = A.activatedState)
    (hreachA : stepN w
      (A.exploration.length + A.runway.length + 1) start =
        some (e, stateA))
    (hgroovesA : PathGrooves A.toSupported.paths stateA)
    (hbaseB : B.baseState = stateA)
    (hactivatedB : stateB = B.activatedState)
    (hreachB : stepN w
      (B.exploration.length + B.runway.length + 1) (e, stateA) =
        some (start.1, stateB))
    (hgroovesB : PathGrooves B.toSupported.paths stateB)
    (hlocal : EventuallyPeriodicWithin w (start.1, stateB) (18 * N))
    (times : List Nat)
    (hlive : ∀ k ∈ times, (stepN w k start).isSome)
    (hnd : (times.map (restrictedTonguesAt w N start)).Nodup) :
    times.length ≤ 20 * N + 2 := by
  have h := two_manufacturing_journeys_then_lasso_distinct_le_overlap
    hN A B stateA stateB hbaseA hactivatedA hreachA hgroovesA
    hbaseB hactivatedB hreachB hgroovesB hlocal times hlive hnd
  omega

end GeneralN
