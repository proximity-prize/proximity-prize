import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr10p16:∀ i ∈ List.range 5,CorrectAt 10 (128+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
