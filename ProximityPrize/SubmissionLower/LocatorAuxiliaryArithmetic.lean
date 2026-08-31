import ProximityPrize.SubmissionLower.LocatorArithmetic

/- One fixed A68 kernel suffices for every replacement cell. -/
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem auxiliary_rank : localRankBound 68 3102 20 = 116339314 := by decide

theorem auxiliary_nullity :
    coefficientCount 12367432 131071 3102 20 -
      262144 * localRankBound 68 3102 20 = 38601570819 := by
  rw [auxiliary_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    12367432 131071 3102 20 95 (by decide) (by decide)]
  decide

theorem auxiliary_shape : 12367432 + 20 ≤ 131071 * (94 + 1) := by decide
theorem auxiliary_capacity :
    12367432 - 50804 ≤ (68 - 1) * 181874 + (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
