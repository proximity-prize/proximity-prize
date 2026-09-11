import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br16p16:∀ i ∈ List.range 4,BaseCheckAt 16 (64+i):=by decide +kernel

theorem br16p17:∀ i ∈ List.range 4,BaseCheckAt 16 (68+i):=by decide +kernel

theorem br16p18:∀ i ∈ List.range 4,BaseCheckAt 16 (72+i):=by decide +kernel

theorem br16p19:∀ i ∈ List.range 4,BaseCheckAt 16 (76+i):=by decide +kernel

theorem br16p20:∀ i ∈ List.range 4,BaseCheckAt 16 (80+i):=by decide +kernel

theorem br16p21:∀ i ∈ List.range 4,BaseCheckAt 16 (84+i):=by decide +kernel

theorem br16p22:∀ i ∈ List.range 4,BaseCheckAt 16 (88+i):=by decide +kernel

theorem br16p23:∀ i ∈ List.range 4,BaseCheckAt 16 (92+i):=by decide +kernel

theorem br16p24:∀ i ∈ List.range 4,BaseCheckAt 16 (96+i):=by decide +kernel

theorem br16p25:∀ i ∈ List.range 4,BaseCheckAt 16 (100+i):=by decide +kernel

theorem br16p26:∀ i ∈ List.range 4,BaseCheckAt 16 (104+i):=by decide +kernel

theorem br16p27:∀ i ∈ List.range 4,BaseCheckAt 16 (108+i):=by decide +kernel

theorem br16p28:∀ i ∈ List.range 4,BaseCheckAt 16 (112+i):=by decide +kernel

theorem br16p29:∀ i ∈ List.range 4,BaseCheckAt 16 (116+i):=by decide +kernel

theorem br16p30:∀ i ∈ List.range 4,BaseCheckAt 16 (120+i):=by decide +kernel

theorem br16p31:∀ i ∈ List.range 3,BaseCheckAt 16 (124+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
