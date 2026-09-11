import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastBase02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br9p32:∀ i ∈ List.range 4,BaseCheckAt 9 (128+i):=by decide +kernel

theorem br9p33:∀ i ∈ List.range 2,BaseCheckAt 9 (132+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
