import ProximityPrize.SubmissionLower.LocatorR1Parameters

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1Coefficient. -/
section PackedLocator_LocatorR1Coefficient

/-! Constant-time coefficient-count receipt for the R1 source. -/

namespace ProximityPrize.SubmissionLower.LocatorR1Coefficient

open ProximityPrize.Benchmark
open RCN100
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 217647600 131071 82100 370 =
      4336440015677516390 := by
  change coefficientCount (1660 * 131071 + 69740) 131071 82100 370 =
    4336440015677516390
  rw [coefficientCount_eq_oneResidueCoefficientCount
    1660 69740 131071 82100 370 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorR1Coefficient
end PackedLocator_LocatorR1Coefficient

