import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 127295 21 = 5662634406 := by decide

theorem auxiliary72_nullity :
    coefficientCount 13077936 131071 127295 21 -
      262144 * localRankBound 72 127295 21 = 1765947352829 := by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13077936 131071 127295 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13077936 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13077936 - 50568 ≤ (72 - 1) * 181638 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-186 C source. -/
theorem auxiliary176_shape :
    33784668 + 55 ≤ 131071 * (257 + 1) := by decide

theorem auxiliary176_capacity :
    33784668 - 50568 ≤ (186 - 1) * 181638 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    33784668 - 2 * 50568 ≤
      (186 - 2) * 181638 + 2 * (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
