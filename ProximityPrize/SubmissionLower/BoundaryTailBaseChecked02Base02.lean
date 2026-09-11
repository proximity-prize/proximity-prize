import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked02Base01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br2p32:∀ i ∈ List.range 4,BaseCheckAt 2 (128+i):=by decide +kernel

theorem br2p33:∀ i ∈ List.range 4,BaseCheckAt 2 (132+i):=by decide +kernel

theorem br2p34:∀ i ∈ List.range 4,BaseCheckAt 2 (136+i):=by decide +kernel

theorem br2p35:∀ i ∈ List.range 1,BaseCheckAt 2 (140+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
