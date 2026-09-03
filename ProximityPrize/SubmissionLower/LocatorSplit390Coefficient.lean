import ProximityPrize.SubmissionLower.LocatorSplit390Parameters

/-! Constant-time coefficient-count receipt for the Split390 source. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit390Coefficient

open ProximityPrize.Benchmark
open RCN100
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 70742880 131071 19500 120 = 35454114385401910 := by
  change coefficientCount (539 * 131071 + 95611) 131071 19500 120 =
    35454114385401910
  rw [coefficientCount_eq_oneResidueCoefficientCount
    539 95611 131071 19500 120 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorSplit390Coefficient
