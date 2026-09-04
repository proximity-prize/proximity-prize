import ProximityPrize.SubmissionLower.LocatorSourceCGap

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500Parameters. -/
section PackedLocator_LocatorSplit500Parameters

/-! Shared, reduction-cheap definitions for the 500-contact split source. -/

namespace ProximityPrize.SubmissionLower.LocatorSplit500Parameters

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- One closed contact-rank row for the Split500 source. -/
def rankRow (r : ℕ) : ℕ :=
  let M := min r 42000
  let h := min (r + 1) (1000 - r)
  rectangularCount (M + 1) (310 + 1) 0 42000 -
    rectangularCount (M + 1 - h) (310 + 1 - h) h 42000

end ProximityPrize.SubmissionLower.LocatorSplit500Parameters
end PackedLocator_LocatorSplit500Parameters

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier31 : True := by trivial
end ProximityPrize.SubmissionLower

