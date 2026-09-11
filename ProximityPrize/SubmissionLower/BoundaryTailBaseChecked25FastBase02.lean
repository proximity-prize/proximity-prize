import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br25p16:∀ i ∈ List.range 4,BaseCheckAt 25 (64+i):=by decide +kernel

theorem br25p17:∀ i ∈ List.range 4,BaseCheckAt 25 (68+i):=by decide +kernel

theorem br25p18:∀ i ∈ List.range 4,BaseCheckAt 25 (72+i):=by decide +kernel

theorem br25p19:∀ i ∈ List.range 4,BaseCheckAt 25 (76+i):=by decide +kernel

theorem br25p20:∀ i ∈ List.range 4,BaseCheckAt 25 (80+i):=by decide +kernel

theorem br25p21:∀ i ∈ List.range 4,BaseCheckAt 25 (84+i):=by decide +kernel

theorem br25p22:∀ i ∈ List.range 4,BaseCheckAt 25 (88+i):=by decide +kernel

theorem br25p23:∀ i ∈ List.range 4,BaseCheckAt 25 (92+i):=by decide +kernel

theorem br25p24:∀ i ∈ List.range 4,BaseCheckAt 25 (96+i):=by decide +kernel

theorem br25p25:∀ i ∈ List.range 4,BaseCheckAt 25 (100+i):=by decide +kernel

theorem br25p26:∀ i ∈ List.range 4,BaseCheckAt 25 (104+i):=by decide +kernel

theorem br25p27:∀ i ∈ List.range 4,BaseCheckAt 25 (108+i):=by decide +kernel

theorem br25p28:∀ i ∈ List.range 4,BaseCheckAt 25 (112+i):=by decide +kernel

theorem br25p29:∀ i ∈ List.range 2,BaseCheckAt 25 (116+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
