import ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

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
  let M := min r 82100
  let h := min (r + 1) (1200 - r)
  rectangularCount (M + 1) (370 + 1) 0 82100 -
    rectangularCount (M + 1 - h) (370 + 1 - h) h 82100

end ProximityPrize.SubmissionLower.LocatorR1200Parameters
