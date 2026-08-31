import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem auxiliary95_rank:localRankBound 95 2800 29=287001435:=by decide
theorem auxiliary95_nullity :
    coefficientCount 17269670 131071 2800 29 -
      262144*localRankBound 95 2800 29=104761399990:=by
  rw [auxiliary95_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    17269670 131071 2800 29 132 (by decide) (by decide)]
  decide
theorem auxiliary95_shape:17269670+29≤131071*(131+1):=by decide
theorem auxiliary95_capacity :
    17269670 - 50716≤(95 - 1)*181786+(131071 - 1):=by decide
theorem auxiliary72_rank:localRankBound 72 7000 21=310108381:=by decide
theorem auxiliary72_nullity :
    coefficientCount 13088592 131071 7000 21 -
      262144*localRankBound 72 7000 21=155878194098:=by
  rw [auxiliary72_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    13088592 131071 7000 21 100 (by decide) (by decide)]
  decide
theorem auxiliary72_shape:13088592+21≤131071*(99+1):=by decide
theorem auxiliary72_capacity :
    13088592 - 50716≤(72 - 1)*181786+(131071 - 1):=by decide
end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
