import ProximityPrize.SubmissionLower.LocatorSplit500Parameters

/-! Constant-time coefficient-count receipt for the Split500 source. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit500Coefficient

open ProximityPrize.Benchmark
open RCN100
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 90696000 131071 21000 155 = 80552687771609625 := by
  change coefficientCount (691 * 131071 + 125939) 131071 21000 155 =
    80552687771609625
  rw [coefficientCount_eq_oneResidueCoefficientCount
    691 125939 131071 21000 155 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorSplit500Coefficient
