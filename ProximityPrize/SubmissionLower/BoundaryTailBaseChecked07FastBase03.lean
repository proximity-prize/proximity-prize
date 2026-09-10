import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastBase02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem base_r7_part32 : ∀ i ∈ List.range 4, BaseCheckAt 7 (128+i) := by decide +kernel

theorem base_r7_part33 : ∀ i ∈ List.range 1, BaseCheckAt 7 (132+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
