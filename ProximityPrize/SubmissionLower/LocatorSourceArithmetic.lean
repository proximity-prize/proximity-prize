import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorSourceArithmetic
open RCN100 RCN119 RCN302
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem kernelAmbient_rank : localRankBound 68 109000 20 = 4125214002 := by
  decide

theorem kernelAmbient_nullity :
    coefficientCount 12367432 131071 109000 20 -
      262144 * localRankBound 68 109000 20 = 3915744547617 := by
  rw [kernelAmbient_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    12367432 131071 109000 20 95 (by decide) (by decide)]
  decide

end ProximityPrize.SubmissionLower.LocatorSourceArithmetic
