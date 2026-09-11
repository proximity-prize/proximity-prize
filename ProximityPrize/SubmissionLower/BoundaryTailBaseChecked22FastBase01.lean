import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br22p0:∀ i ∈ List.range 4,BaseCheckAt 22 (0+i):=by decide +kernel

theorem br22p1:∀ i ∈ List.range 4,BaseCheckAt 22 (4+i):=by decide +kernel

theorem br22p2:∀ i ∈ List.range 4,BaseCheckAt 22 (8+i):=by decide +kernel

theorem br22p3:∀ i ∈ List.range 4,BaseCheckAt 22 (12+i):=by decide +kernel

theorem br22p4:∀ i ∈ List.range 4,BaseCheckAt 22 (16+i):=by decide +kernel

theorem br22p5:∀ i ∈ List.range 4,BaseCheckAt 22 (20+i):=by decide +kernel

theorem br22p6:∀ i ∈ List.range 4,BaseCheckAt 22 (24+i):=by decide +kernel

theorem br22p7:∀ i ∈ List.range 4,BaseCheckAt 22 (28+i):=by decide +kernel

theorem br22p8:∀ i ∈ List.range 4,BaseCheckAt 22 (32+i):=by decide +kernel

theorem br22p9:∀ i ∈ List.range 4,BaseCheckAt 22 (36+i):=by decide +kernel

theorem br22p10:∀ i ∈ List.range 4,BaseCheckAt 22 (40+i):=by decide +kernel

theorem br22p11:∀ i ∈ List.range 4,BaseCheckAt 22 (44+i):=by decide +kernel

theorem br22p12:∀ i ∈ List.range 4,BaseCheckAt 22 (48+i):=by decide +kernel

theorem br22p13:∀ i ∈ List.range 4,BaseCheckAt 22 (52+i):=by decide +kernel

theorem br22p14:∀ i ∈ List.range 4,BaseCheckAt 22 (56+i):=by decide +kernel

theorem br22p15:∀ i ∈ List.range 4,BaseCheckAt 22 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
