import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked05Base01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br5p32:∀ i ∈ List.range 4,BaseCheckAt 5 (128+i):=by decide +kernel

theorem br5p33:∀ i ∈ List.range 4,BaseCheckAt 5 (132+i):=by decide +kernel

theorem br5p34:∀ i ∈ List.range 2,BaseCheckAt 5 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
