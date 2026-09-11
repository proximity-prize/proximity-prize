import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br31p16:∀ i ∈ List.range 4,BaseCheckAt 31 (64+i):=by decide +kernel

theorem br31p17:∀ i ∈ List.range 4,BaseCheckAt 31 (68+i):=by decide +kernel

theorem br31p18:∀ i ∈ List.range 4,BaseCheckAt 31 (72+i):=by decide +kernel

theorem br31p19:∀ i ∈ List.range 4,BaseCheckAt 31 (76+i):=by decide +kernel

theorem br31p20:∀ i ∈ List.range 4,BaseCheckAt 31 (80+i):=by decide +kernel

theorem br31p21:∀ i ∈ List.range 4,BaseCheckAt 31 (84+i):=by decide +kernel

theorem br31p22:∀ i ∈ List.range 4,BaseCheckAt 31 (88+i):=by decide +kernel

theorem br31p23:∀ i ∈ List.range 4,BaseCheckAt 31 (92+i):=by decide +kernel

theorem br31p24:∀ i ∈ List.range 4,BaseCheckAt 31 (96+i):=by decide +kernel

theorem br31p25:∀ i ∈ List.range 4,BaseCheckAt 31 (100+i):=by decide +kernel

theorem br31p26:∀ i ∈ List.range 4,BaseCheckAt 31 (104+i):=by decide +kernel

theorem br31p27:∀ i ∈ List.range 4,BaseCheckAt 31 (108+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
