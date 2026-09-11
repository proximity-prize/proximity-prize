import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br24p0:∀ i ∈ List.range 4,BaseCheckAt 24 (0+i):=by decide +kernel

theorem br24p1:∀ i ∈ List.range 4,BaseCheckAt 24 (4+i):=by decide +kernel

theorem br24p2:∀ i ∈ List.range 4,BaseCheckAt 24 (8+i):=by decide +kernel

theorem br24p3:∀ i ∈ List.range 4,BaseCheckAt 24 (12+i):=by decide +kernel

theorem br24p4:∀ i ∈ List.range 4,BaseCheckAt 24 (16+i):=by decide +kernel

theorem br24p5:∀ i ∈ List.range 4,BaseCheckAt 24 (20+i):=by decide +kernel

theorem br24p6:∀ i ∈ List.range 4,BaseCheckAt 24 (24+i):=by decide +kernel

theorem br24p7:∀ i ∈ List.range 4,BaseCheckAt 24 (28+i):=by decide +kernel

theorem br24p8:∀ i ∈ List.range 4,BaseCheckAt 24 (32+i):=by decide +kernel

theorem br24p9:∀ i ∈ List.range 4,BaseCheckAt 24 (36+i):=by decide +kernel

theorem br24p10:∀ i ∈ List.range 4,BaseCheckAt 24 (40+i):=by decide +kernel

theorem br24p11:∀ i ∈ List.range 4,BaseCheckAt 24 (44+i):=by decide +kernel

theorem br24p12:∀ i ∈ List.range 4,BaseCheckAt 24 (48+i):=by decide +kernel

theorem br24p13:∀ i ∈ List.range 4,BaseCheckAt 24 (52+i):=by decide +kernel

theorem br24p14:∀ i ∈ List.range 4,BaseCheckAt 24 (56+i):=by decide +kernel

theorem br24p15:∀ i ∈ List.range 4,BaseCheckAt 24 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
