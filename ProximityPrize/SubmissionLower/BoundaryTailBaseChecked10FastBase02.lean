import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br10p16:∀ i ∈ List.range 4,BaseCheckAt 10 (64+i):=by decide +kernel

theorem br10p17:∀ i ∈ List.range 4,BaseCheckAt 10 (68+i):=by decide +kernel

theorem br10p18:∀ i ∈ List.range 4,BaseCheckAt 10 (72+i):=by decide +kernel

theorem br10p19:∀ i ∈ List.range 4,BaseCheckAt 10 (76+i):=by decide +kernel

theorem br10p20:∀ i ∈ List.range 4,BaseCheckAt 10 (80+i):=by decide +kernel

theorem br10p21:∀ i ∈ List.range 4,BaseCheckAt 10 (84+i):=by decide +kernel

theorem br10p22:∀ i ∈ List.range 4,BaseCheckAt 10 (88+i):=by decide +kernel

theorem br10p23:∀ i ∈ List.range 4,BaseCheckAt 10 (92+i):=by decide +kernel

theorem br10p24:∀ i ∈ List.range 4,BaseCheckAt 10 (96+i):=by decide +kernel

theorem br10p25:∀ i ∈ List.range 4,BaseCheckAt 10 (100+i):=by decide +kernel

theorem br10p26:∀ i ∈ List.range 4,BaseCheckAt 10 (104+i):=by decide +kernel

theorem br10p27:∀ i ∈ List.range 4,BaseCheckAt 10 (108+i):=by decide +kernel

theorem br10p28:∀ i ∈ List.range 4,BaseCheckAt 10 (112+i):=by decide +kernel

theorem br10p29:∀ i ∈ List.range 4,BaseCheckAt 10 (116+i):=by decide +kernel

theorem br10p30:∀ i ∈ List.range 4,BaseCheckAt 10 (120+i):=by decide +kernel

theorem br10p31:∀ i ∈ List.range 4,BaseCheckAt 10 (124+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
