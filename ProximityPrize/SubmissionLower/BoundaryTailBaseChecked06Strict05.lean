import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked06Strict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r6_part128 : ∀ i ∈ List.range 1, StrictCheckAt 6 (128+i) := by decide +kernel

theorem strict_r6_part129 : ∀ i ∈ List.range 1, StrictCheckAt 6 (129+i) := by decide +kernel

theorem strict_r6_part130 : ∀ i ∈ List.range 1, StrictCheckAt 6 (130+i) := by decide +kernel

theorem strict_r6_part131 : ∀ i ∈ List.range 1, StrictCheckAt 6 (131+i) := by decide +kernel

theorem strict_r6_part132 : ∀ i ∈ List.range 1, StrictCheckAt 6 (132+i) := by decide +kernel

theorem strict_r6_part133 : ∀ i ∈ List.range 1, StrictCheckAt 6 (133+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
