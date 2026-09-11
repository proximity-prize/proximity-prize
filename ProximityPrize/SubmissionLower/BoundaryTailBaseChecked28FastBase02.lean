import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br28p16:∀ i ∈ List.range 4,BaseCheckAt 28 (64+i):=by decide +kernel

theorem br28p17:∀ i ∈ List.range 4,BaseCheckAt 28 (68+i):=by decide +kernel

theorem br28p18:∀ i ∈ List.range 4,BaseCheckAt 28 (72+i):=by decide +kernel

theorem br28p19:∀ i ∈ List.range 4,BaseCheckAt 28 (76+i):=by decide +kernel

theorem br28p20:∀ i ∈ List.range 4,BaseCheckAt 28 (80+i):=by decide +kernel

theorem br28p21:∀ i ∈ List.range 4,BaseCheckAt 28 (84+i):=by decide +kernel

theorem br28p22:∀ i ∈ List.range 4,BaseCheckAt 28 (88+i):=by decide +kernel

theorem br28p23:∀ i ∈ List.range 4,BaseCheckAt 28 (92+i):=by decide +kernel

theorem br28p24:∀ i ∈ List.range 4,BaseCheckAt 28 (96+i):=by decide +kernel

theorem br28p25:∀ i ∈ List.range 4,BaseCheckAt 28 (100+i):=by decide +kernel

theorem br28p26:∀ i ∈ List.range 4,BaseCheckAt 28 (104+i):=by decide +kernel

theorem br28p27:∀ i ∈ List.range 4,BaseCheckAt 28 (108+i):=by decide +kernel

theorem br28p28:∀ i ∈ List.range 3,BaseCheckAt 28 (112+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
