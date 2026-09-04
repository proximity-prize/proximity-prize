import ProximityPrize.SubmissionLower.LocatorSplit390Parameters

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Coefficient. -/
section PackedLocator_LocatorSplit390Coefficient

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
    coefficientCount 70735470 131071 19500 120 = 35445850035150610 := by
  change coefficientCount (539 * 131071 + 88201) 131071 19500 120 =
    35445850035150610
  rw [coefficientCount_eq_oneResidueCoefficientCount
    539 88201 131071 19500 120 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorSplit390Coefficient
end PackedLocator_LocatorSplit390Coefficient

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier38 : True := by trivial
end ProximityPrize.SubmissionLower

