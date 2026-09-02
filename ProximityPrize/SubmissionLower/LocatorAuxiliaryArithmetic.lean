import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorKernelEval

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 130000 21 = 5782993381 := by
  rw [← LocatorKernelEval.localRankBound_eq 72 130000 21 (by decide)]
  decide

theorem auxiliary72_nullity :
    coefficientCount 13073688 131071 130000 21 -
      262144 * localRankBound 72 130000 21 = 718516492562 := by
  rw [auxiliary72_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    13073688 131071 130000 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13073688 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13073688 - 50509 ≤ (72 - 1) * 181579 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-300 C source. -/
theorem auxiliary176_shape :
    54473700 + 87 ≤ 131071 * (415 + 1) := by decide

theorem auxiliary176_capacity :
    54473700 - 50509 ≤ (300 - 1) * 181579 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    54473700 - 2 * 50509 ≤
      (300 - 2) * 181579 + 2 * (131071 - 1) := by decide

/-- The stage-`j` capacity identity of the C source holds with equality for
    every `j ≤ 300`, because `181579 - (131071 - 1) = 50509`. -/
theorem auxiliary176_stage_capacity (j : ℕ) (hj : j ≤ 300) :
    54473700 - j * 50509 ≤ (300 - j) * 181579 + j * (131071 - 1) := by
  omega

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
