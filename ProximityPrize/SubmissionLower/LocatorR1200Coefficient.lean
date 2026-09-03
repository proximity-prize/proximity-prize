import ProximityPrize.SubmissionLower.LocatorR1200Parameters

/-! Constant-time coefficient-count receipt for the R1200 source. -/

namespace ProximityPrize.SubmissionLower.LocatorR1200Coefficient

open ProximityPrize.Benchmark
open RCN100
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 217670400 131071 82100 370 =
      4337453593087735190 := by
  change coefficientCount (1660 * 131071 + 92540) 131071 82100 370 =
    4337453593087735190
  rw [coefficientCount_eq_oneResidueCoefficientCount
    1660 92540 131071 82100 370 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorR1200Coefficient
