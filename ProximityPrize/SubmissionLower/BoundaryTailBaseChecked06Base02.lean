import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked06Base01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br6p32:∀ i ∈ List.range 4,BaseCheckAt 6 (128+i):=by decide +kernel

theorem br6p33:∀ i ∈ List.range 4,BaseCheckAt 6 (132+i):=by decide +kernel

theorem br6p34:∀ i ∈ List.range 1,BaseCheckAt 6 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
