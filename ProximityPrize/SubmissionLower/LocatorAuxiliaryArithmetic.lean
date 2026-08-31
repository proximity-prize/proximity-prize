import ProximityPrize.SubmissionLower.LocatorArithmetic

/- One fixed A68 kernel suffices for every replacement cell. -/
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem auxiliary_rank : localRankBound 68 3346 20 = 125576178 := by decide

theorem auxiliary_nullity :
    coefficientCount 12366140 131071 3346 20 -
      262144 * localRankBound 68 3346 20 = 39935418943 := by
  rw [auxiliary_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    12366140 131071 3346 20 95 (by decide) (by decide)]
  decide

theorem auxiliary_shape : 12366140 + 20 ≤ 131071 * (94 + 1) := by decide
theorem auxiliary_capacity :
    12366140 - 50785 ≤ (68 - 1) * 181855 + (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
