import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem auxiliary95_rank:localRankBound 102 2800 31 = 352517216:=by decide
theorem auxiliary95_nullity :
    coefficientCount 18541152 131071 2800 31 -
      262144 * localRankBound 102 2800 31 = 131094816568:=by
  rw [auxiliary95_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    18541152 131071 2800 31 142 (by decide) (by decide)]
  decide
theorem auxiliary95_shape:18541152 + 31 ≤ 131071 * (141 + 1):=by decide
theorem auxiliary95_capacity :
    18541152 - 50706 ≤ (102 - 1) * 181776 + (131071 - 1):=by decide
theorem auxiliary72_rank:localRankBound 72 12000 21 = 532583381:=by decide
theorem auxiliary72_nullity :
    coefficientCount 13087872 131071 12000 21 -
      262144 * localRankBound 72 12000 21 = 316829900618:=by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13087872 131071 12000 21 100 (by decide) (by decide)]
  decide
theorem auxiliary72_shape:13087872 + 21 ≤ 131071 * (99 + 1):=by decide
theorem auxiliary72_capacity :
    13087872 - 50706 ≤ (72 - 1) * 181776 + (131071 - 1):=by decide
end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
