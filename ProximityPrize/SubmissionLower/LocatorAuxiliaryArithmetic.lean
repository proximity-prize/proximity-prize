import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 130000 21 = 5782993381 := by decide

theorem auxiliary72_nullity :
    coefficientCount 13074408 131071 130000 21 -
      262144 * localRankBound 72 130000 21 = 902739011042 := by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13074408 131071 130000 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13074408 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13074408 - 50519 ≤ (72 - 1) * 181589 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-270 C source. -/
theorem auxiliary176_shape :
    49029030 + 81 ≤ 131071 * (374 + 1) := by decide

theorem auxiliary176_capacity :
    49029030 - 50519 ≤ (270 - 1) * 181589 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    49029030 - 2 * 50519 ≤
      (270 - 2) * 181589 + 2 * (131071 - 1) := by decide

/-- The stage-`j` capacity identity of the C source holds with equality for
    every `j ≤ 270`, because `181589 - (131071 - 1) = 50519`. -/
theorem auxiliary176_stage_capacity (j : ℕ) (hj : j ≤ 270) :
    49029030 - j * 50519 ≤ (270 - j) * 181589 + j * (131071 - 1) := by
  omega

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
