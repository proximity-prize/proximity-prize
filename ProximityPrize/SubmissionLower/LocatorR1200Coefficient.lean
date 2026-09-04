import ProximityPrize.SubmissionLower.LocatorR1200Parameters

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Coefficient. -/
section PackedLocator_LocatorR1200Coefficient

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
    coefficientCount 870590400 131071 328400 1480 =
      1107287009400021065232 := by
  change coefficientCount (6642 * 131071 + 16818) 131071 328400 1480 =
    1107287009400021065232
  rw [coefficientCount_eq_oneResidueCoefficientCount
    6642 16818 131071 328400 1480 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorR1200Coefficient
end PackedLocator_LocatorR1200Coefficient

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier21 : True := by trivial
end ProximityPrize.SubmissionLower

