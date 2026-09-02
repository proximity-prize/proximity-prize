import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 230000 21 = 10232493381 := by decide

theorem auxiliary72_nullity :
    coefficientCount 13074408 131071 230000 21 -
      262144 * localRankBound 72 230000 21 = 2587242818908418 := by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13074408 131071 230000 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13074408 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13074408 - 50519 ≤ (72 - 1) * 181589 + (131071 - 1) := by decide

/-- These historical names are retained to minimize invalidation; their
    witness is the retuned multiplicity-241 base C source. -/
theorem auxiliary176_shape :
    43762949 + 71 ≤ 131071 * (333 + 1) := by decide

theorem auxiliary176_capacity :
    43762949 - 50519 ≤ (241 - 1) * 181589 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    43762949 - 2 * 50519 ≤
      (241 - 2) * 181589 + 2 * (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
