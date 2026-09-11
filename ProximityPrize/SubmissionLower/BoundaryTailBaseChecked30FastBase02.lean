import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br30p16:∀ i ∈ List.range 4,BaseCheckAt 30 (64+i):=by decide +kernel

theorem br30p17:∀ i ∈ List.range 4,BaseCheckAt 30 (68+i):=by decide +kernel

theorem br30p18:∀ i ∈ List.range 4,BaseCheckAt 30 (72+i):=by decide +kernel

theorem br30p19:∀ i ∈ List.range 4,BaseCheckAt 30 (76+i):=by decide +kernel

theorem br30p20:∀ i ∈ List.range 4,BaseCheckAt 30 (80+i):=by decide +kernel

theorem br30p21:∀ i ∈ List.range 4,BaseCheckAt 30 (84+i):=by decide +kernel

theorem br30p22:∀ i ∈ List.range 4,BaseCheckAt 30 (88+i):=by decide +kernel

theorem br30p23:∀ i ∈ List.range 4,BaseCheckAt 30 (92+i):=by decide +kernel

theorem br30p24:∀ i ∈ List.range 4,BaseCheckAt 30 (96+i):=by decide +kernel

theorem br30p25:∀ i ∈ List.range 4,BaseCheckAt 30 (100+i):=by decide +kernel

theorem br30p26:∀ i ∈ List.range 4,BaseCheckAt 30 (104+i):=by decide +kernel

theorem br30p27:∀ i ∈ List.range 4,BaseCheckAt 30 (108+i):=by decide +kernel

theorem br30p28:∀ i ∈ List.range 1,BaseCheckAt 30 (112+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
