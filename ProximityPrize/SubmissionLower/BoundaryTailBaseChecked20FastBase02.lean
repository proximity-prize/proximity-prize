import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br20p16:∀ i ∈ List.range 4,BaseCheckAt 20 (64+i):=by decide +kernel

theorem br20p17:∀ i ∈ List.range 4,BaseCheckAt 20 (68+i):=by decide +kernel

theorem br20p18:∀ i ∈ List.range 4,BaseCheckAt 20 (72+i):=by decide +kernel

theorem br20p19:∀ i ∈ List.range 4,BaseCheckAt 20 (76+i):=by decide +kernel

theorem br20p20:∀ i ∈ List.range 4,BaseCheckAt 20 (80+i):=by decide +kernel

theorem br20p21:∀ i ∈ List.range 4,BaseCheckAt 20 (84+i):=by decide +kernel

theorem br20p22:∀ i ∈ List.range 4,BaseCheckAt 20 (88+i):=by decide +kernel

theorem br20p23:∀ i ∈ List.range 4,BaseCheckAt 20 (92+i):=by decide +kernel

theorem br20p24:∀ i ∈ List.range 4,BaseCheckAt 20 (96+i):=by decide +kernel

theorem br20p25:∀ i ∈ List.range 4,BaseCheckAt 20 (100+i):=by decide +kernel

theorem br20p26:∀ i ∈ List.range 4,BaseCheckAt 20 (104+i):=by decide +kernel

theorem br20p27:∀ i ∈ List.range 4,BaseCheckAt 20 (108+i):=by decide +kernel

theorem br20p28:∀ i ∈ List.range 4,BaseCheckAt 20 (112+i):=by decide +kernel

theorem br20p29:∀ i ∈ List.range 4,BaseCheckAt 20 (116+i):=by decide +kernel

theorem br20p30:∀ i ∈ List.range 3,BaseCheckAt 20 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
