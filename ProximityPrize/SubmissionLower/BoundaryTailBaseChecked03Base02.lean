import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked03Base01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br3p32:∀ i ∈ List.range 4,BaseCheckAt 3 (128+i):=by decide +kernel

theorem br3p33:∀ i ∈ List.range 4,BaseCheckAt 3 (132+i):=by decide +kernel

theorem br3p34:∀ i ∈ List.range 4,BaseCheckAt 3 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
