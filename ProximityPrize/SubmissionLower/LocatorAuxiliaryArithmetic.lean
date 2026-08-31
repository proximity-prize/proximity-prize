import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem auxiliary95_rank:localRankBound 95 2869 29=294179505:=by decide
theorem auxiliary95_nullity :
    coefficientCount 17268720 131071 2869 29 -
      262144*localRankBound 95 2869 29=105035624165:=by
  rw [auxiliary95_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    17268720 131071 2869 29 132 (by decide) (by decide)]
  decide
theorem auxiliary95_shape:17268720+29≤131071*(131+1):=by decide
theorem auxiliary95_capacity :
    17268720 - 50706≤(95 - 1)*181776+(131071 - 1):=by decide
theorem auxiliary72_rank:localRankBound 72 8526 21=378007751:=by decide
theorem auxiliary72_nullity :
    coefficientCount 13087872 131071 8526 21 -
      262144*localRankBound 72 8526 21=198158348960:=by
  rw [auxiliary72_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    13087872 131071 8526 21 100 (by decide) (by decide)]
  decide
theorem auxiliary72_shape:13087872+21≤131071*(99+1):=by decide
theorem auxiliary72_capacity :
    13087872 - 50706≤(72 - 1)*181776+(131071 - 1):=by decide
end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
