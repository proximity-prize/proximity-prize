import ProximityPrize.SubmissionLower.LocatorArithmetic

namespace ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic

open RCN100 RCN119 RCN302

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private theorem auxiliary72_rank :
    localRankBound 72 130000 21 = 5782993381 := by
  rw [← LocatorKernelEval.localRankBound_eq 72 130000 21 (by decide)]
  decide

theorem auxiliary72_nullity :
    coefficientCount 13072248 131071 130000 21 -
      262144 * localRankBound 72 130000 21 = 350071455602 := by
  rw [auxiliary72_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    13072248 131071 130000 21 100 (by decide) (by decide)]
  decide

theorem auxiliary72_shape :
    13072248 + 21 ≤ 131071 * (99 + 1) := by decide

theorem auxiliary72_capacity :
    13072248 - 50489 ≤ (72 - 1) * 181559 + (131071 - 1) := by decide

/-- These names are retained to minimize invalidation in the replacement
    proof; their witness is the retuned multiplicity-270 C source. -/
theorem auxiliary176_shape :
    51744315 + 85 ≤ 131071 * (394 + 1) := by decide

theorem auxiliary176_capacity :
    51744315 - 50489 ≤ (285 - 1) * 181559 + (131071 - 1) := by decide

theorem auxiliary176_double_capacity :
    51744315 - 2 * 50489 ≤
      (285 - 2) * 181559 + 2 * (131071 - 1) := by decide

/-- The stage-`j` capacity identity of the C source holds with equality for
    every `j ≤ 285`, because `181559 - (131071 - 1) = 50489`. -/
theorem auxiliary176_stage_capacity (j : ℕ) (hj : j ≤ 285) :
    51744315 - j * 50489 ≤ (285 - j) * 181559 + j * (131071 - 1) := by
  omega

end ProximityPrize.SubmissionLower.LocatorAuxiliaryArithmetic
