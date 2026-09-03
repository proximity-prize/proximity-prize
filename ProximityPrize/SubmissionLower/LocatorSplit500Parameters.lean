import ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

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
  let M := min r 21000
  let h := min (r + 1) (500 - r)
  rectangularCount (M + 1) (155 + 1) 0 21000 -
    rectangularCount (M + 1 - h) (155 + 1 - h) h 21000

end ProximityPrize.SubmissionLower.LocatorSplit500Parameters
