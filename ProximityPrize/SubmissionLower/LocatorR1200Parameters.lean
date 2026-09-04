import ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200Parameters. -/
section PackedLocator_LocatorR1200Parameters

/-! Shared, reduction-cheap definitions for the 1200-contact locator source. -/

namespace ProximityPrize.SubmissionLower.LocatorR1200Parameters

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- One closed contact-rank row for the R1200 source. -/
def rankRow (r : ℕ) : ℕ :=
  let M := min r 328400
  let h := min (r + 1) (4800 - r)
  rectangularCount (M + 1) (1480 + 1) 0 328400 -
    rectangularCount (M + 1 - h) (1480 + 1 - h) h 328400

end ProximityPrize.SubmissionLower.LocatorR1200Parameters
end PackedLocator_LocatorR1200Parameters

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier20 : True := by trivial
end ProximityPrize.SubmissionLower

