import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr9p16:∀ i ∈ List.range 6,CorrectAt 9 (128+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
