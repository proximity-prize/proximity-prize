import ProximityPrize.SubmissionLower.LocatorSplit500Parameters

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Coefficient. -/
section PackedLocator_LocatorSplit500Coefficient

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
    coefficientCount 181373000 131071 42000 310 =
      1283287897834879898 := by
  change coefficientCount (1383 * 131071 + 101807) 131071 42000 310 =
    1283287897834879898
  rw [coefficientCount_eq_oneResidueCoefficientCount
    1383 101807 131071 42000 310 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

end ProximityPrize.SubmissionLower.LocatorSplit500Coefficient
end PackedLocator_LocatorSplit500Coefficient

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier32 : True := by trivial
end ProximityPrize.SubmissionLower

