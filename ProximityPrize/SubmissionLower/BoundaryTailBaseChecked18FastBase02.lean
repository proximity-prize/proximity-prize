import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br18p16:∀ i ∈ List.range 4,BaseCheckAt 18 (64+i):=by decide +kernel

theorem br18p17:∀ i ∈ List.range 4,BaseCheckAt 18 (68+i):=by decide +kernel

theorem br18p18:∀ i ∈ List.range 4,BaseCheckAt 18 (72+i):=by decide +kernel

theorem br18p19:∀ i ∈ List.range 4,BaseCheckAt 18 (76+i):=by decide +kernel

theorem br18p20:∀ i ∈ List.range 4,BaseCheckAt 18 (80+i):=by decide +kernel

theorem br18p21:∀ i ∈ List.range 4,BaseCheckAt 18 (84+i):=by decide +kernel

theorem br18p22:∀ i ∈ List.range 4,BaseCheckAt 18 (88+i):=by decide +kernel

theorem br18p23:∀ i ∈ List.range 4,BaseCheckAt 18 (92+i):=by decide +kernel

theorem br18p24:∀ i ∈ List.range 4,BaseCheckAt 18 (96+i):=by decide +kernel

theorem br18p25:∀ i ∈ List.range 4,BaseCheckAt 18 (100+i):=by decide +kernel

theorem br18p26:∀ i ∈ List.range 4,BaseCheckAt 18 (104+i):=by decide +kernel

theorem br18p27:∀ i ∈ List.range 4,BaseCheckAt 18 (108+i):=by decide +kernel

theorem br18p28:∀ i ∈ List.range 4,BaseCheckAt 18 (112+i):=by decide +kernel

theorem br18p29:∀ i ∈ List.range 4,BaseCheckAt 18 (116+i):=by decide +kernel

theorem br18p30:∀ i ∈ List.range 4,BaseCheckAt 18 (120+i):=by decide +kernel

theorem br18p31:∀ i ∈ List.range 1,BaseCheckAt 18 (124+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
