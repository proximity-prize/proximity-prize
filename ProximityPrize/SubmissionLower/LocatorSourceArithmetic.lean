import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem kernelAmbient_rank : localRankBound 74 100000 22 = 4888257620 := by
  decide

theorem kernelAmbient_nullity :
    coefficientCount 13456530 131071 100000 22 -
      262144 * localRankBound 74 100000 22 = 5092988274078 := by
  rw [kernelAmbient_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13456530 131071 100000 22 103 (by decide) (by decide)]
  decide

end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
