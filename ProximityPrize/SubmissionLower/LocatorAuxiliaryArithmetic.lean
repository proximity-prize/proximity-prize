import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem auxiliary95_rank:localRankBound 114 2750 35 = 483536220:=by decide
theorem auxiliary95_nullity :
    coefficientCount 20721324 131071 2750 35 -
      262144 * localRankBound 114 2750 35 = 171987925155:=by
  rw [auxiliary95_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    20721324 131071 2750 35 159 (by decide) (by decide)]
  decide
theorem auxiliary95_shape:20721324 + 35 ≤ 131071 * (158 + 1):=by decide
theorem auxiliary95_capacity :
    20721324 - 50696 ≤ (114 - 1) * 181766 + (131071 - 1):=by decide
theorem auxiliary72_rank:localRankBound 72 12000 21 = 532583381:=by decide
theorem auxiliary72_nullity :
    coefficientCount 13087152 131071 12000 21 -
      262144 * localRankBound 72 12000 21 = 299893622138:=by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13087152 131071 12000 21 100 (by decide) (by decide)]
  decide
theorem auxiliary72_shape:13087152 + 21 ≤ 131071 * (99 + 1):=by decide
theorem auxiliary72_capacity :
    13087152 - 50696 ≤ (72 - 1) * 181766 + (131071 - 1):=by decide
end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
