import ProximityPrize.SubmissionLower.LocatorSplit500Source

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390Parameters. -/
section PackedLocator_LocatorSplit390Parameters

/-! Shared, reduction-cheap definitions for the 390-contact split source. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit390Parameters

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- One closed contact-rank row for the Split390 source. -/
def rankRow (r : ℕ) : ℕ :=
  let M := min r 19500
  let h := min (r + 1) (390 - r)
  rectangularCount (M + 1) (120 + 1) 0 19500 -
    rectangularCount (M + 1 - h) (120 + 1 - h) h 19500

end ProximityPrize.SubmissionLower.LocatorSplit390Parameters
end PackedLocator_LocatorSplit390Parameters

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier37 : True := by trivial
end ProximityPrize.SubmissionLower

