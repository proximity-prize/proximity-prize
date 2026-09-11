import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br28p0:∀ i ∈ List.range 4,BaseCheckAt 28 (0+i):=by decide +kernel

theorem br28p1:∀ i ∈ List.range 4,BaseCheckAt 28 (4+i):=by decide +kernel

theorem br28p2:∀ i ∈ List.range 4,BaseCheckAt 28 (8+i):=by decide +kernel

theorem br28p3:∀ i ∈ List.range 4,BaseCheckAt 28 (12+i):=by decide +kernel

theorem br28p4:∀ i ∈ List.range 4,BaseCheckAt 28 (16+i):=by decide +kernel

theorem br28p5:∀ i ∈ List.range 4,BaseCheckAt 28 (20+i):=by decide +kernel

theorem br28p6:∀ i ∈ List.range 4,BaseCheckAt 28 (24+i):=by decide +kernel

theorem br28p7:∀ i ∈ List.range 4,BaseCheckAt 28 (28+i):=by decide +kernel

theorem br28p8:∀ i ∈ List.range 4,BaseCheckAt 28 (32+i):=by decide +kernel

theorem br28p9:∀ i ∈ List.range 4,BaseCheckAt 28 (36+i):=by decide +kernel

theorem br28p10:∀ i ∈ List.range 4,BaseCheckAt 28 (40+i):=by decide +kernel

theorem br28p11:∀ i ∈ List.range 4,BaseCheckAt 28 (44+i):=by decide +kernel

theorem br28p12:∀ i ∈ List.range 4,BaseCheckAt 28 (48+i):=by decide +kernel

theorem br28p13:∀ i ∈ List.range 4,BaseCheckAt 28 (52+i):=by decide +kernel

theorem br28p14:∀ i ∈ List.range 4,BaseCheckAt 28 (56+i):=by decide +kernel

theorem br28p15:∀ i ∈ List.range 4,BaseCheckAt 28 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
