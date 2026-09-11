import ProximityPrize.SubmissionLower.BoundaryTailBaseFast

namespace ProximityPrize.SubmissionLower.PropTest
open ProximityPrize.SubmissionLower.BoundaryTailBaseFast
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

-- the SHIPPED form: Prop + Decidable instance, same 30 cells
theorem propForm : ∀ k ∈ List.range 28, ZeroAtFast 12 (100+k) := by
  decide +kernel

end ProximityPrize.SubmissionLower.PropTest
