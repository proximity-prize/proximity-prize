import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked04Base01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem base_r4_part32 : ∀ i ∈ List.range 4, BaseCheckAt 4 (128+i) := by decide +kernel

theorem base_r4_part33 : ∀ i ∈ List.range 4, BaseCheckAt 4 (132+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
