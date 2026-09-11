import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastZero09
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict09

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br14p0:∀ i ∈ List.range 4,BaseCheckAt 14 (0+i):=by decide +kernel

theorem br14p1:∀ i ∈ List.range 4,BaseCheckAt 14 (4+i):=by decide +kernel

theorem br14p2:∀ i ∈ List.range 4,BaseCheckAt 14 (8+i):=by decide +kernel

theorem br14p3:∀ i ∈ List.range 4,BaseCheckAt 14 (12+i):=by decide +kernel

theorem br14p4:∀ i ∈ List.range 4,BaseCheckAt 14 (16+i):=by decide +kernel

theorem br14p5:∀ i ∈ List.range 4,BaseCheckAt 14 (20+i):=by decide +kernel

theorem br14p6:∀ i ∈ List.range 4,BaseCheckAt 14 (24+i):=by decide +kernel

theorem br14p7:∀ i ∈ List.range 4,BaseCheckAt 14 (28+i):=by decide +kernel

theorem br14p8:∀ i ∈ List.range 4,BaseCheckAt 14 (32+i):=by decide +kernel

theorem br14p9:∀ i ∈ List.range 4,BaseCheckAt 14 (36+i):=by decide +kernel

theorem br14p10:∀ i ∈ List.range 4,BaseCheckAt 14 (40+i):=by decide +kernel

theorem br14p11:∀ i ∈ List.range 4,BaseCheckAt 14 (44+i):=by decide +kernel

theorem br14p12:∀ i ∈ List.range 4,BaseCheckAt 14 (48+i):=by decide +kernel

theorem br14p13:∀ i ∈ List.range 4,BaseCheckAt 14 (52+i):=by decide +kernel

theorem br14p14:∀ i ∈ List.range 4,BaseCheckAt 14 (56+i):=by decide +kernel

theorem br14p15:∀ i ∈ List.range 4,BaseCheckAt 14 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
