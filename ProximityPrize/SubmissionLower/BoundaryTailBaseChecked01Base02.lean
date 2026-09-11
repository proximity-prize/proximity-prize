import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked01Base01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br1p32:∀ i ∈ List.range 4,BaseCheckAt 1 (128+i):=by decide +kernel

theorem br1p33:∀ i ∈ List.range 4,BaseCheckAt 1 (132+i):=by decide +kernel

theorem br1p34:∀ i ∈ List.range 4,BaseCheckAt 1 (136+i):=by decide +kernel

theorem br1p35:∀ i ∈ List.range 2,BaseCheckAt 1 (140+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
