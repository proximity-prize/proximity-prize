import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 130000 21 = 5782993381 := by decide

theorem auxiliary72_nullity :
    coefficientCount 13073688 131071 130000 21 -
      262144 * localRankBound 72 130000 21 = 718516492562 := by
  rw [auxiliary72_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13073688 131071 130000 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13073688 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13073688 - 50509 ≤ (72 - 1) * 181579 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-275 C source. -/
theorem auxiliary176_shape :
    49934225 + 82 ≤ 131071 * (380 + 1) := by decide

theorem auxiliary176_capacity :
    49934225 - 50509 ≤ (275 - 1) * 181579 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    49934225 - 2 * 50509 ≤
      (275 - 2) * 181579 + 2 * (131071 - 1) := by decide

/-- The stage-`j` capacity identity of the C source holds with equality for
    every `j ≤ 275`, because `181579 - (131071 - 1) = 50509`. -/
theorem auxiliary176_stage_capacity (j : ℕ) (hj : j ≤ 275) :
    49934225 - j * 50509 ≤ (275 - j) * 181579 + j * (131071 - 1) := by
  omega

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
