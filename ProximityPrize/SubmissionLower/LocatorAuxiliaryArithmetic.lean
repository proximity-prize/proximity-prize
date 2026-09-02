import ProximityPrize.SubmissionLower.LocatorArithmetic
import ProximityPrize.SubmissionLower.LocatorKernelEval

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 74 130000 23 = 6563386200 := by
  rw [← LocatorKernelEval.localRankBound_eq 74 130000 23 (by decide)]
  decide

theorem auxiliary72_nullity :
    coefficientCount 13433220 131071 130000 23 -
      262144 * localRankBound 74 130000 23 = 157054229278 := by
  rw [auxiliary72_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    13433220 131071 130000 23 103 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13433220 + 23 ≤ 131071 * (102 + 1) := by decide

theorem auxiliary72_capacity :
    13433220 - 50460 ≤ (74 - 1) * 181530 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-400 C source. -/
theorem auxiliary176_shape :
    72612000 + 120 ≤ 131071 * (554 + 1) := by decide

theorem auxiliary176_capacity :
    72612000 - 50460 ≤ (400 - 1) * 181530 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    72612000 - 2 * 50460 ≤
      (400 - 2) * 181530 + 2 * (131071 - 1) := by decide

/-- The stage-`j` capacity identity of the C source holds with equality for
    every `j ≤ 400`, because `181530 - (131071 - 1) = 50460`. -/
theorem auxiliary176_stage_capacity (j : ℕ) (hj : j ≤ 400) :
    72612000 - j * 50460 ≤ (400 - j) * 181530 + j * (131071 - 1) := by
  omega

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
