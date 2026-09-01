import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorKernelEval

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 149307 21 = 6642058346 := by
  rw [← LocatorKernelEval.localRankBound_eq 72 149307 21 (by decide)]
  decide

theorem auxiliary72_nullity :
    coefficientCount 13075848 131071 149307 21 -
      262144 * localRankBound 72 149307 21 = 1473611397929 := by
  rw [auxiliary72_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    13075848 131071 149307 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13075848 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13075848 - 50539 ≤ (72 - 1) * 181609 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-264 C source. -/
theorem auxiliary176_shape :
    47944776 + 80 ≤ 131071 * (365 + 1) := by decide

theorem auxiliary176_capacity :
    47944776 - 50539 ≤ (264 - 1) * 181609 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    47944776 - 2 * 50539 ≤
      (264 - 2) * 181609 + 2 * (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
