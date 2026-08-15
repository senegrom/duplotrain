import TrackGlobalRepair
import StateLaw
import FirstReflectorNovelty
import TripleSelfLinkSimpleCycleClosure
import TwoJourneyTailCountSharp
import TrackThetaAllTime
import TrackStayContactAllTime
import FacingForwardNovelty
import RunwayHistoricalThree
import BoundaryOverlapTailCount

/-!
# Generic lift from a known incoming edge

A successful first step exposes the physical edge just crossed.  Positive
sample times can therefore be shifted by one and handed to any known-edge
counting theorem.  Time zero costs at most one further vector.
-/

namespace GeneralN

theorem kel_zero_positive_partition :
    ∀ xs : List Nat,
      (xs.filter (fun k => decide (k = 0))).length +
        (xs.filter (fun k => decide (0 < k))).length = xs.length := by
  intro xs
  induction xs with
  | nil => simp
  | cons k rest ih =>
      by_cases hk : k = 0
      · subst k
        simp
        omega
      · have hkPos : 0 < k := by omega
        simp [hk, hkPos]
        omega

theorem kel_zero_filter_length_le_one
    {xs : List Nat} (hnd : xs.Nodup) :
    (xs.filter (fun k => decide (k = 0))).length ≤ 1 := by
  have hfilterNodup :
      (xs.filter (fun k => decide (k = 0))).Nodup :=
    nodup_filter_nat _ hnd
  apply nodup_nat_lt_length hfilterNodup
  intro k hk
  have hk0 : k = 0 :=
    of_decide_eq_true (List.mem_filter.mp hk).2
  omega

end GeneralN
