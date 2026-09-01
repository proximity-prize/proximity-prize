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
    coefficientCount 13076496 131071 149307 21 -
      262144 * localRankBound 72 149307 21 = 1664045697545 := by
  rw [auxiliary72_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    13076496 131071 149307 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13076496 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13076496 - 50548 ≤ (72 - 1) * 181618 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-264 C source. -/
theorem auxiliary176_shape :
    47947152 + 80 ≤ 131071 * (365 + 1) := by decide

theorem auxiliary176_capacity :
    47947152 - 50548 ≤ (264 - 1) * 181618 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    47947152 - 2 * 50548 ≤
      (264 - 2) * 181618 + 2 * (131071 - 1) := by decide

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
