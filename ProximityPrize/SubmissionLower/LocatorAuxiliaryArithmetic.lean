import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 169536 21 = 7542147701 := by decide

theorem auxiliary72_nullity :
    coefficientCount 13077216 131071 169536 21 -
      262144 * localRankBound 72 169536 21 = 2142222243722 := by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13077216 131071 169536 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13077216 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13077216 - 50558 ≤ (72 - 1) * 181628 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-215 C source. -/
theorem auxiliary176_shape :
    39050020 + 63 ≤ 131071 * (297 + 1) := by decide

theorem auxiliary176_capacity :
    39050020 - 50558 ≤ (215 - 1) * 181628 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    39050020 - 2 * 50558 ≤
      (215 - 2) * 181628 + 2 * (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
