import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked04Base01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br4p32:∀ i ∈ List.range 4,BaseCheckAt 4 (128+i):=by decide +kernel

theorem br4p33:∀ i ∈ List.range 4,BaseCheckAt 4 (132+i):=by decide +kernel

theorem br4p34:∀ i ∈ List.range 3,BaseCheckAt 4 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
