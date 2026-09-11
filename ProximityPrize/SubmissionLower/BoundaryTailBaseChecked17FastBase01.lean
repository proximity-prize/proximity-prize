import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br17p0:∀ i ∈ List.range 4,BaseCheckAt 17 (0+i):=by decide +kernel

theorem br17p1:∀ i ∈ List.range 4,BaseCheckAt 17 (4+i):=by decide +kernel

theorem br17p2:∀ i ∈ List.range 4,BaseCheckAt 17 (8+i):=by decide +kernel

theorem br17p3:∀ i ∈ List.range 4,BaseCheckAt 17 (12+i):=by decide +kernel

theorem br17p4:∀ i ∈ List.range 4,BaseCheckAt 17 (16+i):=by decide +kernel

theorem br17p5:∀ i ∈ List.range 4,BaseCheckAt 17 (20+i):=by decide +kernel

theorem br17p6:∀ i ∈ List.range 4,BaseCheckAt 17 (24+i):=by decide +kernel

theorem br17p7:∀ i ∈ List.range 4,BaseCheckAt 17 (28+i):=by decide +kernel

theorem br17p8:∀ i ∈ List.range 4,BaseCheckAt 17 (32+i):=by decide +kernel

theorem br17p9:∀ i ∈ List.range 4,BaseCheckAt 17 (36+i):=by decide +kernel

theorem br17p10:∀ i ∈ List.range 4,BaseCheckAt 17 (40+i):=by decide +kernel

theorem br17p11:∀ i ∈ List.range 4,BaseCheckAt 17 (44+i):=by decide +kernel

theorem br17p12:∀ i ∈ List.range 4,BaseCheckAt 17 (48+i):=by decide +kernel

theorem br17p13:∀ i ∈ List.range 4,BaseCheckAt 17 (52+i):=by decide +kernel

theorem br17p14:∀ i ∈ List.range 4,BaseCheckAt 17 (56+i):=by decide +kernel

theorem br17p15:∀ i ∈ List.range 4,BaseCheckAt 17 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
