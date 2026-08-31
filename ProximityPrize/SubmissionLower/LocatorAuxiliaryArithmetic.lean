import ProximityPrize.SubmissionLower.LocatorArithmetic
namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
theorem auxiliary95_rank:localRankBound 95 3200 29=328613435:=by decide
theorem auxiliary95_nullity :
    coefficientCount 17266820 131071 3200 29 -
      262144*localRankBound 95 3200 29=129230045740:=by
  rw [auxiliary95_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    17266820 131071 3200 29 132 (by decide) (by decide)]
  decide
theorem auxiliary95_shape:17266820+29 ≤ 131071*(131+1):=by decide
theorem auxiliary95_capacity :
    17266820 - 50686 ≤ (95 - 1)*181756+(131071 - 1):=by decide
theorem auxiliary72_rank:localRankBound 72 24000 21=1066523381:=by decide
theorem auxiliary72_nullity :
    coefficientCount 13086432 131071 24000 21 -
      262144*localRankBound 72 24000 21=658852027658:=by
  rw [auxiliary72_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    13086432 131071 24000 21 100 (by decide) (by decide)]
  decide
theorem auxiliary72_shape:13086432+21 ≤ 131071*(99+1):=by decide
theorem auxiliary72_capacity :
    13086432 - 50686 ≤ (72 - 1)*181756+(131071 - 1):=by decide
theorem auxiliary126_rank:localRankBound 126 2814 39=668448560:=by decide
theorem auxiliary126_nullity :
    coefficientCount 22901256 131071 2814 39 -
      262144*localRankBound 126 2814 39=241401798610:=by
  rw [auxiliary126_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    22901256 131071 2814 39 175 (by decide) (by decide)]
  decide
theorem auxiliary126_shape:22901256+39 ≤ 131071*(174+1):=by decide
theorem auxiliary126_capacity :
    22901256 - 50686 ≤ (126 - 1)*181756+(131071 - 1):=by decide
end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
